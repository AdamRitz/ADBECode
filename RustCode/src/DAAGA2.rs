use ark_bn254::{Bn254, Fr, G1Projective, G2Projective, Fq12};
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ec::pairing::Pairing;
use ark_ff::{Field, PrimeField, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand::thread_rng;
use sha2::{Digest, Sha256};

/// DAAGKAwSNP 组结构 - Type III 配对优化版
/// 保存原始标量值，同时维护 G1 和 G2 版本用于配对
pub struct DAAGKA2Group {
    pub ns: usize,              // 组大小
    pub g: G1Projective,        // G1 生成元
    pub g2: G2Projective,       // G2 生成元
    pub h1: G1Projective,       // h1 = g^δ
    pub h2: G1Projective,       // h2 = g^δ'
    pub h2_g2: G2Projective,    // h2 在 G2 中
    pub delta: Fr,              // δ 标量
    pub delta2: Fr,             // δ' 标量
    pub f: Vec<G1Projective>,   // f_i 在 G1（用于计算 z_{i,j}）
    pub f_scalars: Vec<Fr>,     // f_i 对应的标量 w_i
    pub f_g2: Vec<G2Projective>, // f_i 在 G2 中（用于配对）
    pub R: Vec<G1Projective>,   // R_i 在 G1
    pub c: Vec<Vec<G1Projective>>,    // c_{i,j} 在 G1
    pub c_g2: Vec<Vec<G2Projective>>, // c_{i,j} 在 G2（用于配对）
}

pub struct Member {
    pub index: usize,
    pub u: Fr,
    pub x: G1Projective,
    pub z: Fr,
    pub r: G1Projective,
    pub p: Fr,
    pub z_vec: Vec<G1Projective>,    // z_{i,j} 在 G1
    pub z_vec_g2: Vec<G2Projective>, // z_{i,j} 在 G2（用于配对）
}

pub struct GroupKeys {
    pub y: G1Projective,
    pub C: Fq12,
    pub dk: Vec<G1Projective>,     // dk_i 在 G1
    pub dk_g2: Vec<G2Projective>,  // dk_i 在 G2（用于解密配对）
    pub u0: G1Projective,
    pub u1: G1Projective,
    pub u0_scalar: Fr,             // u0 对应的标量
    pub u1_scalar: Fr,             // u1 对应的标量
    pub u0_g2: G2Projective,       // u0 在 G2 中
    pub u1_g2: G2Projective,       // u1 在 G2 中
}

pub struct Ciphertext {
    pub c1: G1Projective,
    pub c2: G1Projective,
    pub c3: Vec<u8>,
}

impl DAAGKA2Group {
    pub fn setup(ns: usize) -> Self {
        let mut rng = thread_rng();

        let g = G1Projective::generator();
        let g2 = G2Projective::generator();

        let delta = Fr::rand(&mut rng);
        let delta2 = Fr::rand(&mut rng);
        let h1 = g * delta;
        let h2 = g * delta2;
        let h2_g2 = g2 * delta2;

        // f_i: 同时保存标量和 G1/G2 版本
        let mut f = Vec::new();
        let mut f_scalars = Vec::new();
        let mut f_g2 = Vec::new();
        for _ in 0..ns {
            let w_i = Fr::rand(&mut rng);
            f_scalars.push(w_i);
            f.push(g * w_i);
            f_g2.push(g2 * w_i);
        }

        // R_i 在 G1
        let mut R = Vec::new();
        for _ in 0..ns {
            let gamma_i = Fr::rand(&mut rng);
            R.push(g * gamma_i);
        }

        // c_{i,j} 在 G1 和 G2
        let mut c = vec![vec![G1Projective::default(); ns]; ns];
        let mut c_g2 = vec![vec![G2Projective::default(); ns]; ns];
        for i in 0..ns {
            for j in 0..ns {
                if i != j {
                    let c_ij = Fr::rand(&mut rng);
                    c[i][j] = g * c_ij;
                    c_g2[i][j] = g2 * c_ij;
                }
            }
        }

        Self {
            ns,
            g,
            g2,
            h1,
            h2,
            h2_g2,
            delta,
            delta2,
            f,
            f_scalars,
            f_g2,
            R,
            c,
            c_g2,
        }
    }

    pub fn keygen(&self) -> (Fr, G1Projective) {
        let mut rng = thread_rng();
        let u = Fr::rand(&mut rng);
        let x = self.g * u;
        (u, x)
    }

    pub fn agreement(&self, members: &[(Fr, G1Projective)]) -> (Vec<Member>, GroupKeys) {
        let t = members.len();
        assert!(t <= self.ns, "Too many members");

        let mut rng = thread_rng();
        let idp_scalar = Fr::rand(&mut rng);

        // 计算 u0, u1 的标量值
        let u0_scalar = self.hash_h1_scalar(&idp_scalar, 0);
        let u1_scalar = self.hash_h1_scalar(&idp_scalar, 1);

        // 同时生成 G1 和 G2 版本
        let u0 = self.g * u0_scalar;
        let u1 = self.g * u1_scalar;
        let u0_g2 = self.g2 * u0_scalar;
        let u1_g2 = self.g2 * u1_scalar;

        let mut member_list = Vec::new();

        // 计算每个成员的 z_{i,j}（同时在 G1 和 G2 中）
        for (idx, &(u, x)) in members.iter().enumerate() {
            let z = Fr::rand(&mut rng);
            let r = self.g * z;
            let p = self.hash_h2(&idp_scalar, &x, &r);

            // z_{i,j} = u0^{u_i} · u1^{p_i·u_i} · f_j^{z_i}
            // 在 G1 和 G2 中同时计算
            let mut z_vec = Vec::new();
            let mut z_vec_g2 = Vec::new();
            for j in 0..self.ns {
                // G1 版本
                let term1 = u0 * u;
                let term2 = u1 * (p * u);
                let term3 = self.f[j] * z;
                z_vec.push(term1 + term2 + term3);

                // G2 版本
                let term1_g2 = u0_g2 * u;
                let term2_g2 = u1_g2 * (p * u);
                let term3_g2 = self.f_g2[j] * z;
                z_vec_g2.push(term1_g2 + term2_g2 + term3_g2);
            }

            member_list.push(Member {
                index: idx + 1,
                u,
                x,
                z,
                r,
                p,
                z_vec,
                z_vec_g2,
            });
        }

        // Enc.Key.Gen: y = ∏r_i · ∏R_j
        let mut y = G1Projective::default();
        for member in &member_list {
            y = y + member.r;
        }
        for j in t..self.ns {
            y = y + self.R[j];
        }

        // C = ê(∑x_i, u0) · ê(∑x_i^{p_i}, u1) · ê(h1, h2)^{ns-t}
        let mut sum_x = G1Projective::default();
        let mut sum_xp = G1Projective::default();

        for member in &member_list {
            sum_x = sum_x + member.x;
            sum_xp = sum_xp + (member.x * member.p);
        }

        // 使用 G2 版本进行配对
        let part1 = Bn254::pairing(sum_x, u0_g2).0;
        let part2 = Bn254::pairing(sum_xp, u1_g2).0;
        let exp = Fr::from((self.ns - t) as u64);
        let part3 = Bn254::pairing(self.h1, self.h2_g2).0.pow(exp.into_bigint());

        let C = part1 * part2 * part3;

        // Dec.Key.Gen: 计算 dk_i（同时在 G1 和 G2 中）
        let mut dk = Vec::new();
        let mut dk_g2 = Vec::new();

        for i in 0..t {
            let idx = i;

            // d̂_i = ∏_{j≠i,j≤t} z_{j,i} · ∏_{j>t} c_{j,i}
            let mut d_hat = G1Projective::default();
            let mut d_hat_g2 = G2Projective::default();

            for j in 0..t {
                if j != i {
                    d_hat = d_hat + member_list[j].z_vec[idx];
                    d_hat_g2 = d_hat_g2 + member_list[j].z_vec_g2[idx];
                }
            }

            for j in t..self.ns {
                d_hat = d_hat + self.c[j][idx];
                d_hat_g2 = d_hat_g2 + self.c_g2[j][idx];
            }

            // dk_i = d̂_i + z_{i,i}
            let dk_i = d_hat + member_list[i].z_vec[idx];
            let dk_i_g2 = d_hat_g2 + member_list[i].z_vec_g2[idx];

            // 验证：ê(g, dk_i_g2) = C · ê(y, f_i_g2)
            let left = Bn254::pairing(self.g, dk_i_g2).0;
            let right = C * Bn254::pairing(y, self.f_g2[idx]).0;

            if left != right {
                println!("⚠️ 警告：成员 {} 的解密密钥验证失败", i + 1);
            }

            dk.push(dk_i);
            dk_g2.push(dk_i_g2);
        }

        let group_keys = GroupKeys {
            y,
            C,
            dk,
            dk_g2,
            u0,
            u1,
            u0_scalar,
            u1_scalar,
            u0_g2,
            u1_g2,
        };

        (member_list, group_keys)
    }

    pub fn encrypt(
        &self,
        message: &Fq12,
        sender_sk: Fr,
        sender_pk: G1Projective,
        group_keys: &GroupKeys,
    ) -> Ciphertext {
        let mut rng = thread_rng();
        let rho = Fr::rand(&mut rng);

        let c1 = self.g * rho;
        let c2 = group_keys.y * rho;

        let h = self.hash_h4(&c1, message);
        let sig = h * sender_sk;

        let K = group_keys.C.pow(rho.into_bigint());

        let mut plaintext_bytes = Vec::new();
        message.serialize_uncompressed(&mut plaintext_bytes).unwrap();
        sender_pk.serialize_uncompressed(&mut plaintext_bytes).unwrap();
        sig.serialize_uncompressed(&mut plaintext_bytes).unwrap();

        let h3_output = self.hash_h3(&K, plaintext_bytes.len());
        let c3 = xor_bytes(&plaintext_bytes, &h3_output);

        Ciphertext { c1, c2, c3 }
    }

    pub fn decrypt(
        &self,
        ct: &Ciphertext,
        member_index: usize,
        group_keys: &GroupKeys,
    ) -> Option<(Fq12, G1Projective)> {
        let idx = member_index - 1;
        let dk_i_g2 = &group_keys.dk_g2[idx];
        let f_i_g2 = &self.f_g2[idx];

        // K' = ê(c1, dk_i_g2) / ê(c2, f_i_g2)
        let part1 = Bn254::pairing(ct.c1, *dk_i_g2).0;
        let part2 = Bn254::pairing(ct.c2, *f_i_g2).0;

        let K_prime = part1 * part2.inverse().unwrap();

        let h3_output = self.hash_h3(&K_prime, ct.c3.len());
        let plaintext_bytes = xor_bytes(&ct.c3, &h3_output);

        // 动态反序列化
        let mut cursor = 0;

        let m = match Fq12::deserialize_uncompressed(&plaintext_bytes[cursor..]) {
            Ok(val) => {
                let mut temp = Vec::new();
                val.serialize_uncompressed(&mut temp).unwrap();
                cursor += temp.len();
                val
            },
            Err(e) => {
                println!("❌ 反序列化 Fq12 失败: {:?}", e);
                return None;
            }
        };

        let xl = match G1Projective::deserialize_uncompressed(&plaintext_bytes[cursor..]) {
            Ok(val) => {
                let mut temp = Vec::new();
                val.serialize_uncompressed(&mut temp).unwrap();
                cursor += temp.len();
                val
            },
            Err(e) => {
                println!("❌ 反序列化 G1 (sender_pk) 失败: {:?}", e);
                return None;
            }
        };

        let sig = match G1Projective::deserialize_uncompressed(&plaintext_bytes[cursor..]) {
            Ok(val) => val,
            Err(e) => {
                println!("❌ 反序列化 G1 (sig) 失败: {:?}", e);
                return None;
            }
        };

        // 验证签名：ê(sig, g2) = ê(xl, h_g2)
        // 其中 sig = g^{h_scalar * sender_sk}, xl = g^{sender_sk}
        // h_g2 = g2^{h_scalar}
        let h_scalar = self.hash_h4_scalar(&ct.c1, &m);
        let h_g2 = self.g2 * h_scalar;

        let left = Bn254::pairing(sig, self.g2).0;
        let right = Bn254::pairing(xl, h_g2).0;

        if left == right {
            Some((m, xl))
        } else {
            println!("❌ 签名验证失败");
            None
        }
    }

    // ========== 辅助函数 ==========

    fn hash_h1_scalar(&self, idp: &Fr, flag: u8) -> Fr {
        let mut bytes = Vec::new();
        idp.serialize_uncompressed(&mut bytes).unwrap();
        bytes.push(flag);
        let hash = Sha256::digest(&bytes);
        Fr::from_be_bytes_mod_order(&hash)
    }

    fn hash_h2(&self, idp: &Fr, x: &G1Projective, r: &G1Projective) -> Fr {
        let mut bytes = Vec::new();
        idp.serialize_uncompressed(&mut bytes).unwrap();
        x.serialize_uncompressed(&mut bytes).unwrap();
        r.serialize_uncompressed(&mut bytes).unwrap();
        let hash = Sha256::digest(&bytes);
        Fr::from_be_bytes_mod_order(&hash)
    }

    fn hash_h3(&self, key: &Fq12, len: usize) -> Vec<u8> {
        let mut bytes = Vec::new();
        key.serialize_uncompressed(&mut bytes).unwrap();

        let mut output = Vec::new();
        let mut counter = 0u32;

        while output.len() < len {
            let mut hasher = Sha256::new();
            hasher.update(&bytes);
            hasher.update(&counter.to_be_bytes());
            let hash = hasher.finalize();
            output.extend_from_slice(&hash);
            counter += 1;
        }

        output.truncate(len);
        output
    }

    fn hash_h4_scalar(&self, c1: &G1Projective, m: &Fq12) -> Fr {
        let mut bytes = Vec::new();
        c1.serialize_uncompressed(&mut bytes).unwrap();
        m.serialize_uncompressed(&mut bytes).unwrap();
        let hash = Sha256::digest(&bytes);
        Fr::from_be_bytes_mod_order(&hash)
    }

    fn hash_h4(&self, c1: &G1Projective, m: &Fq12) -> G1Projective {
        let scalar = self.hash_h4_scalar(c1, m);
        self.g * scalar
    }
}

fn xor_bytes(a: &[u8], b: &[u8]) -> Vec<u8> {
    assert_eq!(a.len(), b.len(), "XOR requires equal length arrays");
    a.iter().zip(b.iter()).map(|(x, y)| x ^ y).collect()
}

pub fn test_daagka2(ns: usize, num_members: usize) {
    use std::time::Instant;

    println!("\n╔══════════════════════════════════════╗");
    println!("║  DAAGKA2 测试 (Type III 优化版)      ║");
    println!("╚══════════════════════════════════════╝");
    println!("组大小: {}, 成员数: {}", ns, num_members);

    let start = Instant::now();
    let group = DAAGKA2Group::setup(ns);
    let setup_time = start.elapsed();
    println!("✓ Setup 耗时: {:?}", setup_time);

    let start = Instant::now();
    let mut members = Vec::new();
    for _ in 0..num_members {
        members.push(group.keygen());
    }
    let keygen_time = start.elapsed();
    println!("✓ KeyGen ({}个成员) 耗时: {:?}", num_members, keygen_time);

    let start = Instant::now();
    let (member_list, group_keys) = group.agreement(&members);
    let agreement_time = start.elapsed();
    println!("✓ Agreement 耗时: {:?}", agreement_time);

    let mut rng = thread_rng();
    let m_scalar = Fr::rand(&mut rng);
    let base = Bn254::pairing(group.g, group.g2).0;
    let message = base.pow(m_scalar.into_bigint());

    let sender = &member_list[0];

    let start = Instant::now();
    let ct = group.encrypt(&message, sender.u, sender.x, &group_keys);
    let enc_time = start.elapsed();
    println!("✓ Encrypt 耗时: {:?}", enc_time);

    let start = Instant::now();
    let result = group.decrypt(&ct, 1, &group_keys);
    let dec_time = start.elapsed();
    println!("✓ Decrypt 耗时: {:?}", dec_time);

    match result {
        Some((decrypted_m, decrypted_sender)) => {
            let correct_m = message == decrypted_m;
            let correct_sender = sender.x == decrypted_sender;
            println!("\n【验证结果】");
            println!("  消息正确性: {} {}", if correct_m { "✅" } else { "❌" }, correct_m);
            println!("  发送者正确性: {} {}", if correct_sender { "✅" } else { "❌" }, correct_sender);

            if correct_m && correct_sender {
                println!("\n🎉 测试成功！所有验证通过。\n");
            } else {
                println!("\n⚠️ 测试部分失败。\n");
            }
        }
        None => {
            println!("\n❌ 解密失败！\n");
        }
    }

    println!("╔══════════════════════════════════════╗");
    println!("║  性能汇总                            ║");
    println!("╠══════════════════════════════════════╣");
    println!("║  Setup:     {:>20?}  ║", setup_time);
    println!("║  KeyGen:    {:>20?}  ║", keygen_time);
    println!("║  Agreement: {:>20?}  ║", agreement_time);
    println!("║  Encrypt:   {:>20?}  ║", enc_time);
    println!("║  Decrypt:   {:>20?}  ║", dec_time);
    println!("╚══════════════════════════════════════╝\n");
}
