use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective, Fq12};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{Field, PrimeField, UniformRand};
use ark_std::ops::Mul;
use sha2::{Digest, Sha256};
use std::time::Instant;
use num_traits::{One, Zero};

// use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective, Fq12};
// use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
// use ark_ff::{Field, UniformRand};
// use ark_std::ops::Mul;
// use sha2::{Digest, Sha256};
// use std::time::Instant;
// 全局公共参数结构
pub struct PublicParams {
    pub g1: G1Projective,           // G1 生成元 g
    pub g2: G2Projective,           // G2 生成元 ḡ
    pub g_zeta: G1Projective,       // g^ζ
    pub x_vec: Vec<G1Projective>,   // X_0, ..., X_n = g^{x_0}, ..., g^{x_n}
    pub y_vec: Vec<G2Projective>,   // Y_0, ..., Y_n = ḡ^{x_0}, ..., ḡ^{x_n}
    pub e_g_alphabeta: Fq12,        // e(g, ḡ)^{αβ}
    pub e_g_betagamma: Fq12,        // e(g, ḡ)^{βγ}
}

// 用户密钥结构
pub struct UserSecretKey {
    pub sk1: G2Projective,          // ḡ^r
    pub sk2: G2Projective,          // ḡ^{γβ/(ζ+H2(ID))}
    pub sk3: Vec<Fr>,               // {I_i = ID^i mod p}
    pub sk4: G2Projective,          // ḡ^{αβ} * ∏Y_i^{rI_i}
}

// 密文结构
pub struct Ciphertext {
    pub c1: G1Projective,           // g^k
    pub c2: G2Projective,           // ḡ^{kβγ/(ζ+H2(ID))}
    pub c3: Vec<u8>,                // (m||ID) ⊕ H1(e(g,ḡ)^{kαβ})
    pub c4: Vec<G1Projective>,      // {g^{u_i*k} * X_i^k}
    pub c5: Fr,                     // H2(m, e(g,ḡ)^{kαβ}, e(g,ḡ)^{kβγ}, t)
    pub timestamp: u64,
}

// 主密钥结构
pub struct MasterSecretKey {
    pub zeta: Fr,
    pub g2: G2Projective,
    pub g2_alphabeta: G2Projective,
    pub g2_betagamma: G2Projective,
    pub y_vec: Vec<G2Projective>,
}

// Hash 函数 H1: 将 GT 元素哈希为字节
fn hash_h1(gt_elem: &Fq12, len: usize) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(format!("{:?}", gt_elem).as_bytes());
    let result = hasher.finalize();
    result.iter().cycle().take(len).copied().collect()
}

// Hash 函数 H2: 将任意字节哈希为 Fr
fn hash_h2(data: &[u8]) -> Fr {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let result = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&result[..32]);
    Fr::from_le_bytes_mod_order(&bytes)
}

// Hash ID 到 Fr
fn hash_id(id: &str) -> Fr {
    hash_h2(id.as_bytes())
}

// Setup: 初始化系统参数
pub fn setup(n: usize) -> (PublicParams, MasterSecretKey) {
    let mut rng = ark_std::test_rng();

    // 生成随机参数
    let alpha = Fr::rand(&mut rng);
    let beta = Fr::rand(&mut rng);
    let gamma = Fr::rand(&mut rng);
    let zeta = Fr::rand(&mut rng);

    // 生成元
    let g1 = G1Projective::generator();
    let g2 = G2Projective::generator();

    // 计算 g^ζ
    let g_zeta = g1.mul(zeta);

    // 生成 x_i 并计算 X_i = g^{x_i}, Y_i = ḡ^{x_i}
    let mut x_vec = Vec::new();
    let mut y_vec = Vec::new();
    for _ in 0..=n {
        let xi = Fr::rand(&mut rng);
        x_vec.push(g1.mul(xi));
        y_vec.push(g2.mul(xi));
    }

    // 计算配对值
    let e_g_alphabeta = Bn254::pairing(g1, g2.mul(alpha * beta)).0;
    let e_g_betagamma = Bn254::pairing(g1, g2.mul(beta * gamma)).0;

    let pp = PublicParams {
        g1,
        g2,
        g_zeta,
        x_vec,
        y_vec: y_vec.clone(),
        e_g_alphabeta,
        e_g_betagamma,
    };

    let msk = MasterSecretKey {
        zeta,
        g2,
        g2_alphabeta: g2.mul(alpha * beta),
        g2_betagamma: g2.mul(beta * gamma),
        y_vec,
    };

    (pp, msk)
}

// KeyGen: 生成用户密钥
pub fn keygen(pp: &PublicParams, msk: &MasterSecretKey, id: &str) -> UserSecretKey {
    let mut rng = ark_std::test_rng();
    let r = Fr::rand(&mut rng);

    let id_hash = hash_id(id);

    // sk1 = ḡ^r
    let sk1 = msk.g2.mul(r);

    // sk2 = ḡ^{γβ/(ζ+H2(ID))}
    let denominator = msk.zeta + id_hash;
    let sk2 = msk.g2_betagamma.mul(denominator.inverse().unwrap());

    // sk3 = {I_i = ID^i mod p}
    let mut sk3 = Vec::new();
    let mut id_power = Fr::one();
    for _ in 0..=pp.x_vec.len() - 1 {
        sk3.push(id_power);
        id_power *= id_hash;
    }

    // sk4 = ḡ^{αβ} * ∏Y_i^{rI_i}
    let mut sk4 = msk.g2_alphabeta;
    for i in 0..sk3.len() {
        sk4 += msk.y_vec[i].mul(r * sk3[i]);
    }

    UserSecretKey { sk1, sk2, sk3, sk4 }
}

// 计算多项式系数: f(z) = (z - ID_l)^{n-l} * ∏(z - ID_j)
fn compute_polynomial_coeffs(recipient_ids: &[Fr], n: usize) -> Vec<Fr> {
    let l = recipient_ids.len() - 1;

    // 初始化多项式为 1
    let mut poly = vec![Fr::one()];

    // 计算 (z - ID_l)^{n-l}
    for _ in 0..(n - l) {
        let mut new_poly = vec![Fr::zero(); poly.len() + 1];
        for (i, &coeff) in poly.iter().enumerate() {
            new_poly[i] -= coeff * recipient_ids[l];
            new_poly[i + 1] += coeff;
        }
        poly = new_poly;
    }

    // 乘以 ∏(z - ID_j) for j = 0..l
    for &id_j in recipient_ids.iter() {
        let mut new_poly = vec![Fr::zero(); poly.len() + 1];
        for (i, &coeff) in poly.iter().enumerate() {
            new_poly[i] -= coeff * id_j;
            new_poly[i + 1] += coeff;
        }
        poly = new_poly;
    }

    // 确保长度为 n+1
    poly.resize(n + 1, Fr::zero());
    poly
}

// SignCrypt (Encryption)
pub fn enc(
    pp: &PublicParams,
    sender_sk: &UserSecretKey,
    message: &[u8],
    sender_id: &str,
    recipient_ids: &[&str],
) -> Ciphertext {
    let mut rng = ark_std::test_rng();
    let n = pp.x_vec.len() - 1;

    // 将 recipient IDs 哈希为 Fr
    let recipient_id_frs: Vec<Fr> = recipient_ids.iter().map(|id| hash_id(id)).collect();

    // 计算多项式系数
    let u_coeffs = compute_polynomial_coeffs(&recipient_id_frs, n);

    // 随机选择 k
    let k = Fr::rand(&mut rng);

    // 时间戳
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs();

    // C1 = g^k
    let c1 = pp.g1.mul(k);

    // C2 = sk2^k
    let c2 = sender_sk.sk2.mul(k);

    // 计算 e(g, ḡ)^{kαβ}
    let dk = pp.e_g_alphabeta.pow(k.into_bigint());

    // C3 = (m||ID) ⊕ H1(e(g,ḡ)^{kαβ})
    let mut data_to_encrypt = message.to_vec();
    data_to_encrypt.extend_from_slice(sender_id.as_bytes());
    let h1_output = hash_h1(&dk, data_to_encrypt.len());
    let c3: Vec<u8> = data_to_encrypt.iter()
        .zip(h1_output.iter())
        .map(|(a, b)| a ^ b)
        .collect();

    // C4 = {g^{u_i*k} * X_i^k}
    let mut c4 = Vec::new();
    for i in 0..=n {
        let elem = pp.g1.mul(u_coeffs[i] * k) + pp.x_vec[i].mul(k);
        c4.push(elem);
    }

    // 计算 e(g, ḡ)^{kβγ}
    let vk = pp.e_g_betagamma.pow(k.into_bigint());

    // C5 = H2(m, e(g,ḡ)^{kαβ}, e(g,ḡ)^{kβγ}, t)
    let mut hash_input = Vec::new();
    hash_input.extend_from_slice(message);
    hash_input.extend_from_slice(format!("{:?}", dk).as_bytes());
    hash_input.extend_from_slice(format!("{:?}", vk).as_bytes());
    hash_input.extend_from_slice(&timestamp.to_le_bytes());
    let c5 = hash_h2(&hash_input);

    Ciphertext {
        c1,
        c2,
        c3,
        c4,
        c5,
        timestamp,
    }
}

// UnSignCrypt (Decryption)
pub fn dec(
    pp: &PublicParams,
    ciphertext: &Ciphertext,
    receiver_sk: &UserSecretKey,
    receiver_id: &str,
) -> Option<Vec<u8>> {
    // 验证时间戳（简化版本，实际应该检查是否在允许窗口内）
    let current_time = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs();

    if current_time > ciphertext.timestamp + 3600 {
        // 1小时过期
        return None;
    }

    // 计算 dk = e(C1, sk4) * e(∏c_{4,j}^{I_j}, sk1)^{-1}
    let e1 = Bn254::pairing(ciphertext.c1, receiver_sk.sk4).0;

    let mut prod = G1Projective::default();
    for j in 0..ciphertext.c4.len() {
        prod += ciphertext.c4[j].mul(receiver_sk.sk3[j]);
    }
    let e2 = Bn254::pairing(prod, receiver_sk.sk1).0;
    let e2_inv = e2.inverse().unwrap();

    let dk = e1 * e2_inv;

    // (m||ID) = C3 ⊕ H1(dk)
    let h1_output = hash_h1(&dk, ciphertext.c3.len());
    let decrypted_data: Vec<u8> = ciphertext.c3.iter()
        .zip(h1_output.iter())
        .map(|(a, b)| a ^ b)
        .collect();

    // 计算 vk = e(C2, g^ζ * g^{H2(ID)})
    let id_hash = hash_id(receiver_id);
    let g_component = pp.g_zeta + pp.g1.mul(id_hash);
    let vk = Bn254::pairing(g_component, ciphertext.c2).0;

    // 验证 C5 = H2(m, dk, vk, t)
    let mut hash_input = Vec::new();
    hash_input.extend_from_slice(&decrypted_data);
    hash_input.extend_from_slice(format!("{:?}", dk).as_bytes());
    hash_input.extend_from_slice(format!("{:?}", vk).as_bytes());
    hash_input.extend_from_slice(&ciphertext.timestamp.to_le_bytes());
    let computed_c5 = hash_h2(&hash_input);

    if computed_c5 == ciphertext.c5 {
        Some(decrypted_data)
    } else {
        None
    }
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_paper4_performance() {
        println!("\n========== Paper4 Performance Test ==========");

        // 不同的接收者数量
        let recipient_counts = vec![5, 10, 15, 20];

        for &num_recipients in &recipient_counts {
            println!("\n--- Testing with {} recipients ---", num_recipients);

            let n = num_recipients + 5; // n 应该 >= 接收者数量

            // Setup
            let setup_start = Instant::now();
            let (pp, msk) = setup(n);
            let setup_time = setup_start.elapsed();
            println!("Setup time: {:?}", setup_time);

            // 生成发送者密钥
            let sender_id = "sender@hospital.com";
            let keygen_start = Instant::now();
            let sender_sk = keygen(&pp, &msk, sender_id);
            let keygen_time = keygen_start.elapsed();
            println!("Sender KeyGen time: {:?}", keygen_time);

            // 生成接收者密钥
            let mut receiver_ids = Vec::new();
            let mut receiver_sks = Vec::new();
            for i in 0..num_recipients {
                let id = format!("doctor{}@hospital.com", i);
                receiver_ids.push(id.clone());
                let sk = keygen(&pp, &msk, &id);
                receiver_sks.push(sk);
            }

            // 准备消息
            let message = b"Patient health data: ECG, blood pressure, temperature...";

            // 准备接收者ID引用
            let recipient_id_refs: Vec<&str> = receiver_ids.iter().map(|s| s.as_str()).collect();

            // 加密测试
            let enc_start = Instant::now();
            let ciphertext = enc(&pp, &sender_sk, message, sender_id, &recipient_id_refs);
            let enc_time = enc_start.elapsed();
            println!("Encryption time: {:?}", enc_time);

            // 解密测试（测试第一个接收者）
            let dec_start = Instant::now();
            let decrypted = dec(&pp, &ciphertext, &receiver_sks[0], &receiver_ids[0]);
            let dec_time = dec_start.elapsed();
            println!("Decryption time: {:?}", dec_time);

            // 验证解密结果
            match decrypted {
                Some(data) => {
                    // 提取消息部分（去掉 sender_id）
                    let msg_len = message.len();
                    if data.len() >= msg_len && &data[..msg_len] == message {
                        println!("✓ Decryption successful and message verified!");
                    } else {
                        println!("✗ Decryption failed: message mismatch");
                    }
                }
                None => {
                    println!("✗ Decryption failed: verification failed");
                }
            }

            println!("Total time (Enc + Dec): {:?}", enc_time + dec_time);
        }
    }

    #[test]
    fn test_paper4_benchmark() {
        println!("\n========== Paper4 Benchmark Test (Multiple Runs) ==========");

        let n = 20;
        let num_recipients = 10;
        let num_runs = 10;

        println!("Configuration: n={}, recipients={}, runs={}", n, num_recipients, num_runs);

        // Setup一次
        let (pp, msk) = setup(n);
        let sender_id = "sender@hospital.com";
        let sender_sk = keygen(&pp, &msk, sender_id);

        // 生成接收者
        let mut receiver_ids = Vec::new();
        let mut receiver_sks = Vec::new();
        for i in 0..num_recipients {
            let id = format!("doctor{}@hospital.com", i);
            receiver_ids.push(id.clone());
            receiver_sks.push(keygen(&pp, &msk, &id));
        }

        let message = b"Confidential patient medical records and test results";
        let recipient_id_refs: Vec<&str> = receiver_ids.iter().map(|s| s.as_str()).collect();

        // 多次运行测试
        let mut enc_times = Vec::new();
        let mut dec_times = Vec::new();

        for i in 0..num_runs {
            // 加密
            let enc_start = Instant::now();
            let ciphertext = enc(&pp, &sender_sk, message, sender_id, &recipient_id_refs);
            let enc_time = enc_start.elapsed();
            enc_times.push(enc_time);

            // 解密
            let dec_start = Instant::now();
            let _ = dec(&pp, &ciphertext, &receiver_sks[0], &receiver_ids[0]);
            let dec_time = dec_start.elapsed();
            dec_times.push(dec_time);

            if i == 0 {
                println!("First run - Enc: {:?}, Dec: {:?}", enc_time, dec_time);
            }
        }

        // 计算平均时间
        let avg_enc = enc_times.iter().sum::<std::time::Duration>() / num_runs as u32;
        let avg_dec = dec_times.iter().sum::<std::time::Duration>() / num_runs as u32;

        println!("\n--- Results (averaged over {} runs) ---", num_runs);
        println!("Average Encryption time: {:?} ({:.2} ms)", avg_enc, avg_enc.as_secs_f64() * 1000.0);
        println!("Average Decryption time: {:?} ({:.2} ms)", avg_dec, avg_dec.as_secs_f64() * 1000.0);
        println!("Average Total time: {:?} ({:.2} ms)", avg_enc + avg_dec, (avg_enc + avg_dec).as_secs_f64() * 1000.0);
    }
}
