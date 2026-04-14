use std::ops::Neg;
use ark_std::io::Cursor;
use std::ptr::null;
use std::time::Instant;
use ark_bls12_381::{g1, g2, Bls12_381, Fr, G1Projective, G2Projective, Fq12, G1Affine, G2Affine};

use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ec::pairing::Pairing;
use ark_ff::{Field, PrimeField, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand::thread_rng;
use sha2::{Digest, Sha256};
use sha3::{Shake256, digest::{Update, ExtendableOutput, XofReader}};
use ark_ec::hashing::{
    curve_maps::wb::WBMap,
    map_to_curve_hasher::MapToCurveBasedHasher,
    HashToCurve,
};
use ark_ff::field_hashers::DefaultFieldHasher;

/// DAAGKA 中与 L 相关的必要参数
pub struct DAAGKAGroup {
    pub L: usize,            // 组大小
    pub g1: G1Projective,
    pub g2: G2Projective,
    pub y: G1Projective,
    pub psi: Fq12,             // 与 L 绑定的加密密钥 C
    pub fi: Vec<G1Projective>,  // f_1 ... f_L
    pub dk: Vec<G2Projective>,  // dk_1 ... dk_L
    pub theta:Fr,
    pub x:G1Projective
}

pub const DST_G1: &[u8] = b"MY-PROTOCOL-H2C-G1";
pub const DST_G2: &[u8] = b"MY-PROTOCOL-H2C-G2";
/// 密文结构
pub struct Cipher {
    pub c1: G1Projective,
    pub c2: G2Projective,
    pub c3: Vec<u8>,
}
pub fn Shake256(
    point: &[u8],
    out_len: usize,
) -> Vec<u8> {
    // 2) XOF 扩展
    let mut hasher = Shake256::default();
    hasher.update(point);

    let mut reader = hasher.finalize_xof();
    let mut out = vec![0u8; out_len];
    reader.read(&mut out);
    out
}
impl DAAGKAGroup {

    /// 初始化一个 L 人的 DAAGKA 组
    pub fn setup(L: usize) -> Self {
        let mut rng = thread_rng();

        let g1 = G1Projective::generator();
        let g2 = G2Projective::generator();

        // 生成 L 个 f_i 和 d̂_i
        let mut fi = Vec::new();
        let mut di_hat = Vec::new();
        for _ in 0..L {
            fi.push(G1Projective::rand(&mut rng));
            di_hat.push(G2Projective::rand(&mut rng));
        }

        // 随机选择 y ∈ G1
        let y = G1Projective::rand(&mut rng);

        // 真实 DAAGKA 里 C = complicated(model)
        // 但必须包含 (L - t) 项，因此我们构造一个合法的 L 相关键：
        // C = e(g,g)^(L)  （只要依赖 L，结构是可行的）
        let pairing_gg = Bls12_381::pairing(g1, g2).0;
        let psi = pairing_gg.pow([L as u64]);

        // dk_i = d̂_i * γ_i
        // 真实 DAAGKA 中 γ_i = z_{i,i} 与 L 相关
        let mut dk = Vec::new();
        for i in 0..L {
            let gamma_i = Fr::from((i + 1) as u64);   // 最小结构：γ_i 跟 L 相关
            let dki = di_hat[i] * gamma_i;
            dk.push(dki);
        }
        let theta=Fr::rand(&mut rng);
        let x=g1*theta;
        Self { L, g1, g2, y, psi, fi, dk ,theta,x}
    }

    /// 输入：
    ///     消息 m：Bytes
    ///     元素 y:
    pub fn encrypt(&self, m: &Vec<u8>) -> Cipher {
        // 随机选取 r
        let mut rng = thread_rng();
        let rho = Fr::rand(&mut rng);
        // c1 = g1^rho
        let c1 = self.g1 * rho;
        // c2 = g1^r
        let c2 = self.g2 * rho;
        // h = H(c1,m)
        let mut bytes1=Vec::new();
        c1.serialize_uncompressed(&mut bytes1).unwrap();
        bytes1.extend_from_slice(&m);
        let h=hash_to_g2(&bytes1);
        // sig = h^theta
        let sig = h * self.theta;
        // c3 left = (m,x,l)
        let mut bytes2=Vec::new();
        
        self.x.serialize_uncompressed( &mut bytes2).unwrap();
        sig.serialize_uncompressed(&mut bytes2).unwrap();
        bytes2.extend_from_slice(&m);
        // c3 right = H(psi^rho)
        let rho_big = rho.into_bigint();
        let psirho=(self.psi).pow(rho_big);
        let mut bytespsirho=Vec::new();
        psirho.serialize_uncompressed(&mut bytespsirho).unwrap();
        let right=Shake256(& bytespsirho,bytes2.len());
        let mut c3 = vec![0u8; bytes2.len()];
        for i in 0..bytes2.len() {
            c3[i]=(bytes2[i] ^ right[i]);
        }
        Cipher { c1, c2, c3 }
    }

    /// 解密：使用用户 i 的 dk_i 和 f_i（两者都和 L 相关）
    pub fn decrypt(&self, ct: &Cipher, i: usize) -> Vec<u8> {
        let dki = &self.dk[i];
        let fi  = &self.fi[i];

        let part1 = Bls12_381::pairing(&ct.c1, dki).0;
        let part2 = Bls12_381::pairing(fi,&ct.c2 ).0;

        let key = part1 / part2;
        let mut keyBytes=Vec::new();
        key.serialize_uncompressed(&mut keyBytes).unwrap();
        Shake256(&keyBytes,ct.c3.len());
        // (x,sig,m)
        for i in 0..ct.c3.len() {
            keyBytes[i]=ct.c3[i] ^ keyBytes[i];
        }
        let g2_len=0 ;
        self.g2.into_affine().uncompressed_size();
       
        assert!(keyBytes.len() >= 2 * g2_len);

        // x
        let mut x_bytes = &keyBytes[0..g2_len];
        let x = G2Affine::deserialize_uncompressed(&mut x_bytes);

        // sig
        let mut sig_bytes = &keyBytes[g2_len..2 * g2_len];
        let sig = G2Affine::deserialize_uncompressed(&mut sig_bytes);
        // m
        let m = keyBytes[2 * g2_len..].to_vec();
        // e(g,sig) == e(x,h)
        let mut bytes1=Vec::new();
        bytes1.extend_from_slice(&m);
        ct.c1.serialize_uncompressed(&mut bytes1).unwrap();
        let h=hash_to_g2(&bytes1);
        let e1=Bls12_381::pairing(self.g1,self.g2);
        let e2=Bls12_381::pairing(self.x,h);
        
        if e1==e2{
            return m;
        }else{
            return keyBytes;
        }
    }
}

type H2G1 = MapToCurveBasedHasher<
    G1Projective,
    DefaultFieldHasher<Sha256, 128>,
    WBMap<g1::Config>,
>;

// Hash to G2
type H2G2 = MapToCurveBasedHasher<
    G2Projective,
    DefaultFieldHasher<Sha256, 128>,
    WBMap<g2::Config>,
>;
fn hash_to_g1(msg: &[u8]) -> G1Affine {
    let h = H2G1::new(DST_G1).unwrap();
    h.hash(msg).unwrap()
}

fn hash_to_g2(msg: &[u8]) -> G2Affine {
    let h = H2G2::new(DST_G2).unwrap();
    h.hash(msg).unwrap()
}
// 测试 Enc/Dec
pub fn test_daagka(L: usize,times:usize) {
    let grp = DAAGKAGroup::setup(L);

    let mut rng = thread_rng();

    let mut m:Vec<u8> = Vec::new();
    for _ in 0..96 {
        m.push(5);
    }
    let mut encryptionTime=0;
    let mut decryptionTime = 0;
    for t in 1..=times{

        let startEncryption = Instant::now();
        let ct = grp.encrypt(&m);
        encryptionTime += startEncryption.elapsed().as_nanos() as i128;

        let startDecryption = Instant::now();
        grp.decrypt(&ct,1);
        decryptionTime+=startDecryption.elapsed().as_nanos() as i128;

    }

    println!("L:{:?} 加密耗时{:?}",L,encryptionTime as f64 /times as f64 / 1_000_000.0);
    println!("L:{:?} 解密耗时{:?}",L,decryptionTime as f64 /times as f64 / 1_000_000.0);


    
}
const ID_LEN: usize = 256;
const MSG_LEN: usize = 256;
pub(crate) const CHUNK: usize = 256;
const C3_LEN: usize = 3 * CHUNK; // 768

pub struct Ciphertext {
    pub c1: G1Projective,
    pub c2: G2Projective,
    pub c3: [u8; C3_LEN],
}

// --- 工具函数：SHAKE256 XOF 输出 out_len bytes ---
fn shake256_xof(input: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = Shake256::default();
    h.update(input);
    let mut reader = h.finalize_xof();
    let mut out = vec![0u8; out_len];
    reader.read(&mut out);
    out
}

// --- 工具函数：hash(bytes) -> Fr （替代 element_from_hash 到 Zr） ---
fn hash_to_fr(input: &[u8]) -> Fr {
    // 为了性能测试，直接用 SHAKE256 输出 64 bytes 再 mod r
    let wide = shake256_xof(input, 64);
    Fr::from_le_bytes_mod_order(&wide)
}

// --- 工具函数：把 G1/G2 点序列化成固定长度 buffer（用于拼接输入） ---
// 注意：uncompressed 序列化长度不是 256。为了“固定 256 bytes”性能对齐，
// 我们将序列化结果写入 Vec，然后截断/填充到 256。
// 这只是为了性能基准，不用于真正协议安全。
fn to_fixed_256_g1(p: &G1Projective) -> [u8; CHUNK] {
    let mut v = Vec::new();
    p.into_affine().serialize_uncompressed(&mut v).unwrap();
    let mut out = [0u8; CHUNK];
    let n = v.len().min(CHUNK);
    out[..n].copy_from_slice(&v[..n]);
    out
}

fn to_fixed_256_g2(p: &G2Projective) -> [u8; CHUNK] {
    let mut v = Vec::new();
    p.into_affine().serialize_uncompressed(&mut v).unwrap();
    let mut out = [0u8; CHUNK];
    let n = v.len().min(CHUNK);
    out[..n].copy_from_slice(&v[..n]);
    out
}

// --- 核心结构（对应你的 Paper2） ---
pub struct Paper2Ark {
    pub g: G2Projective,
    pub ppub: G1Projective,      // 你原文 ppub 在 G1
    pub id: [u8; ID_LEN],        // 固定 256 bytes
    pub psi: Fq12, // GT 元素
    pub s2: G1Projective,        // 你 Enc 用的 s2 在 G1
    pub e: G2Projective,         // 你 Enc 用的 e 在 G2（对应 c2 = xE）
    pub theta: Fr,               // 用于生成一个可选签名结构
}

impl Paper2Ark {
    pub fn setup(max_group_size: usize) -> Self {
        let mut rng = thread_rng();

        let g = G2Projective::generator();
        let ppub = G1Projective::rand(&mut rng);

        // id 固定 256 bytes（你 PBC 是 element_to_bytes(g) ）
        let id = to_fixed_256_g2(&g);

        // 构造 psi：用 pairing(g, g2_gen) 的某个幂，绑定 max_group_size
        let g2 = G2Projective::generator();
        let base = Bls12_381::pairing(G1Projective::generator().into_affine(), g2.into_affine());
        let psi = base.0.pow([max_group_size as u64]);

        let s2 = G1Projective::rand(&mut rng);
        let e  = G2Projective::rand(&mut rng);
        let theta = Fr::rand(&mut rng);

        Self { g, ppub, id, psi, s2, e, theta }
    }

    // Enc: 输入 m（256 bytes）
    pub fn enc(&self, m: [u8; MSG_LEN]) -> Ciphertext {
        let mut rng = thread_rng();

        // 随机数 x (rho)
        let x = Fr::rand(&mut rng);

        // c1 = x * g   （G1 标量乘）
        let c1 = self.g * x;

        // h = H(c1 || m || id) -> Fr
        let c1_bytes = to_fixed_256_g2(&c1);
        let mut h_in = [0u8; C3_LEN];
        h_in[0..CHUNK].copy_from_slice(&c1_bytes);
        h_in[CHUNK..2*CHUNK].copy_from_slice(&m);
        h_in[2*CHUNK..3*CHUNK].copy_from_slice(&self.id);
        let h = hash_to_fr(&h_in);

        // F = h*s2 + x*ppub   （2 次 G1 标量乘 + 1 次加法）
        let left  = self.s2 * h;
        let right = self.ppub * x;
        let f = left + right;

        // c2 = x * e （G2 标量乘）
        let c2 = self.e * x;

        // combine3 = id || m || F   （固定 768 bytes）
        let f_bytes = to_fixed_256_g1(&f);
        let mut combine3 = [0u8; C3_LEN];
        combine3[0..CHUNK].copy_from_slice(&self.id);
        combine3[CHUNK..2*CHUNK].copy_from_slice(&m);
        combine3[2*CHUNK..3*CHUNK].copy_from_slice(&f_bytes);

        // keystream = SHAKE256( serialize(psi^x) ) 输出 768
        let psix = self.psi.pow(x.into_bigint());
        let mut seed = Vec::new();
        psix.serialize_uncompressed(&mut seed).unwrap();
        let stream = shake256_xof(&seed, C3_LEN);

        // c3 = combine3 XOR stream
        let mut c3 = [0u8; C3_LEN];
        for i in 0..C3_LEN {
            c3[i] = combine3[i] ^ stream[i];
        }
        let c11=G1Projective::generator();
        Ciphertext { c1:c11, c2, c3 }
    }

    // Dec: 输入 ct, D（一个 G2 私钥元素，模拟你的 D）
    // 你说解密可以不通过，只要效率一样：那就执行相同 pairing + hash + xor，
    // 最后直接返回 m'（不验签）。
    pub fn dec(
        &self,
        ct: &Ciphertext,
        i: usize,
        ppub_g2: &G2Projective,
    ) -> ([u8; MSG_LEN], [u8; CHUNK], bool) {
        let di=G2Projective::generator();
        // 1) Wi = H3(sid_v, i)  
        let wi: G1Projective = h3_sid_i_to_g1(&self.id, i);
        // 2) (id1,m,F) = C3 XOR H5( e(Di,C1) * e(-Wi,C2) )
        let left  = Bls12_381::pairing(ct.c1.into_affine(), di.into_affine()).0;
        let right = Bls12_381::pairing(wi.neg().into_affine(), ct.c2.into_affine()).0;
        let prod: Fq12 = left * right;

        let mut seed = Vec::new();
        prod.serialize_uncompressed(&mut seed).unwrap();
        let stream = shake256_xof(&seed, C3_LEN);

        let mut out = [0u8; C3_LEN];
        for k in 0..C3_LEN {
            out[k] = ct.c3[k] ^ stream[k];
        }

        // out = id1 || m || Fbytes
        let mut id1 = [0u8; CHUNK];
        id1.copy_from_slice(&out[0..CHUNK]);

        let mut m = [0u8; MSG_LEN];
        m.copy_from_slice(&out[CHUNK..2 * CHUNK]);

        // F 从 out[2*CHUNK..3*CHUNK] 里反序列化
         let mut slice: &[u8] = &out[2 * CHUNK..]; // 直接给剩余部分
        let f_affine = G1Affine::deserialize_uncompressed(&mut slice);
        
        // 3) h = H6(C1, m, id1) -> Fr
        let c1_bytes = to_fixed_256_g1(&ct.c1);
        let mut h_in = [0u8; 3 * CHUNK];
        h_in[0..CHUNK].copy_from_slice(&c1_bytes);
        h_in[CHUNK..2 * CHUNK].copy_from_slice(&m);
        h_in[2 * CHUNK..3 * CHUNK].copy_from_slice(&id1);
        let h: Fr = hash_to_fr(&h_in);

        // 4) 检查： e(F, P) ?= e(C1 + h*H1(id1,2), P_pub)
        let p = G2Projective::generator();                
        let h1 = h1_id1_2_to_g1(&id1);                    // H1(id1,2) ∈ G1
        let lhs_g1 = ct.c1 + (h1 * h);                    // C1 + h*H1
        let e_left  = Bls12_381::pairing(G1Projective::generator(), p.into_affine()).0;
        let e_right = Bls12_381::pairing(lhs_g1.into_affine(), ppub_g2.into_affine()).0;

        let ok = (e_left == e_right);
        (m, id1, ok)
    }
    fn h3_sid_i_to_g1(sid_v: &[u8; CHUNK], i: usize) -> G1Projective {
        let mut buf = [0u8; CHUNK + 8];
        buf[..CHUNK].copy_from_slice(sid_v);
        buf[CHUNK..].copy_from_slice(&(i as u64).to_be_bytes());
        hash_to_g1(&buf).into_group()
    }

    // H1: (id1, 2) -> G1
    fn h1_id1_2_to_g1(id1: &[u8; CHUNK]) -> G1Projective {
        let mut buf = [0u8; CHUNK + 1];
        buf[..CHUNK].copy_from_slice(id1);
        buf[CHUNK] = 2u8;
        hash_to_g1(&buf).into_group()
    }
}
fn h3_sid_i_to_g1(sid_v: &[u8; CHUNK], i: usize) -> G1Projective {
    let mut buf = [0u8; CHUNK + 8];
    buf[..CHUNK].copy_from_slice(sid_v);
    buf[CHUNK..].copy_from_slice(&(i as u64).to_be_bytes());
    hash_to_g1(&buf).into_group()
}

// H1: (id1, 2) -> G1
fn h1_id1_2_to_g1(id1: &[u8; CHUNK]) -> G1Projective {
    let mut buf = [0u8; CHUNK + 1];
    buf[..CHUNK].copy_from_slice(id1);
    buf[CHUNK] = 2u8;
    hash_to_g1(&buf).into_group()
}

fn sha256_256(input: &[u8]) -> [u8; CHUNK] {
    // 对齐你的 PBC：输出固定 256 bytes（重复扩展）
    let mut out = [0u8; CHUNK];
    let h = Sha256::digest(input);
    // h 是 32 bytes，重复填充到 256
    for i in 0..CHUNK {
        out[i] = h[i % 32];
    }
    out
}

// hash(bytes) -> Fr（替代 element_from_hash 到 Zr）


fn to_fixed_256_gt(x: &Fq12) -> [u8; CHUNK] {
    let mut v = Vec::new();
    x.serialize_uncompressed(&mut v).unwrap();
    let mut out = [0u8; CHUNK];
    let n = v.len().min(CHUNK);
    out[..n].copy_from_slice(&v[..n]);
    out
}

pub struct Ct3 {
    pub c1: G1Projective,
    pub c2: G1Projective,
    pub c3: [u8; CHUNK],
    pub c4: G1Projective,
    pub c5: Fr,
    // 为了 Dec 里算 w 的输入，需要 X（你 PBC 里用 XBytes）
    pub x_gt: Fq12,
}

pub struct Paper3Ark {
    pub g: G1Projective,
    pub id: [u8; CHUNK],
    pub hs: G1Projective,

    pub e_g1: G1Projective, // 你原文 e,z 都是 G1，这里保留
    pub z_g1: G1Projective,

    pub s1: G1Projective,
    pub s2: G1Projective,

    pub v: Fq12, // GT
    pub h_g1: G1Projective, // 你原文 h ∈ G1
}

impl Paper3Ark {
    pub fn setup(max_group_size: usize) -> Self {
        let mut rng = thread_rng();

        let g = G1Projective::generator();
        let id = to_fixed_256_g1(&g);

        let hs = G1Projective::rand(&mut rng);
        let e_g1 = G1Projective::rand(&mut rng);
        let z_g1 = G1Projective::rand(&mut rng);
        let s1 = G1Projective::rand(&mut rng);
        let s2 = G1Projective::rand(&mut rng);
        let h_g1 = G1Projective::rand(&mut rng);

        // v ∈ GT：用 pairing(g, g2_gen)^max_group_size 构造一个 GT 元素
        let g2 = G2Projective::generator();
        let base = Bls12_381::pairing(g.into_affine(), g2.into_affine());
        let v = base.0.pow([max_group_size as u64]);

        Self { g, id, hs, e_g1, z_g1, s1, s2, v, h_g1 }
    }

    // Enc(v, sk, sum) -> (c1..c5)
    pub fn enc(&self, sk: &G1Projective, sum: &G1Projective, m: [u8; CHUNK]) -> Ct3 {
        let mut rng = thread_rng();

        // a, p ∈ Fr
        let a = Fr::rand(&mut rng);
        let p = Fr::rand(&mut rng);

        // X = v^a
        let x_gt = self.v.pow(a.into_bigint());

        // c1 = sk^p （G1 标量乘）
        let c1 = *sk * p;

        // c2 = g^{-a}
        let aneg = -a;
        let c2 = self.g * aneg;

        // c3 = m XOR SHA256(XBytes)
        let x_bytes = to_fixed_256_gt(&x_gt);
        let mask = sha256_256(&x_bytes);
        let mut c3 = [0u8; CHUNK];
        for i in 0..CHUNK {
            c3[i] = m[i] ^ mask[i];
        }

        // c4 = h^a(s+id)
        let c4left = self.h_g1 * a;
        let c4right=(self.h_g1* a)*a;
        let c4= c4left+c4right;

        // w = H(m, X, c1, c2) -> Fr
        let c1_bytes = to_fixed_256_g1(&c1);
        let c2_bytes = to_fixed_256_g1(&c2);
        let mut w_in = [0u8; 4 * CHUNK];
        w_in[0..CHUNK].copy_from_slice(&m);
        w_in[CHUNK..2*CHUNK].copy_from_slice(&x_bytes);
        w_in[2*CHUNK..3*CHUNK].copy_from_slice(&c1_bytes);
        w_in[3*CHUNK..4*CHUNK].copy_from_slice(&c2_bytes);
        let w = hash_to_fr(&w_in);

        // c5 = p^{-1}(a+w)
        let c5 = (a + w) * p.inverse().unwrap();

        Ct3 { c1, c2, c3, c4, c5, x_gt }
    }

    // Dec(c1..c5, sk, sum1, sum2) -> mm (256 bytes) + 做一次“对齐的验证计算”
    pub fn dec(
        &self,
        ct: &Ct3,
        sk: &G1Projective,
        sum1: Fr,
        sum2: Fr,
    ) -> ([u8; CHUNK], bool) {

        // hsum = h^{sum1}
        let hsum = self.h_g1 * sum1;

        // lrsum = ( e(c2,hsum) * e(c4,sk) )^{sum2}
        // pairing 需要 G1 x G2，这里你的 PBC 用的 G1/G1 但 pairing 类型不对；
        // 为了保持“pairing 开销”，我们把第二输入统一用固定 G2 生成元提升到 G2：
        let g2 = G2Projective::generator();
        let left  = Bls12_381::pairing(ct.c2.into_affine(), g2.into_affine());
        let right = Bls12_381::pairing(ct.c4.into_affine(), g2.into_affine());
        let mut lrsum = left.0 * right.0;
        lrsum = lrsum.pow(sum2.into_bigint());

        // Z = c1^{c5} （算但不用于后续，保持结构）
        let _z_tmp = ct.c1 * ct.c5;

        // mm = c3 XOR SHA256(lrsum)
        let lr_bytes = to_fixed_256_gt(&lrsum);
        let mask = sha256_256(&lr_bytes);
        let mut mm = [0u8; CHUNK];
        for i in 0..CHUNK {
            mm[i] = ct.c3[i] ^ mask[i];
        }

        // w = H(mm, X, c1, c2)
        let x_bytes = to_fixed_256_gt(&ct.x_gt);
        let c1_bytes = to_fixed_256_g1(&ct.c1);
        let c2_bytes = to_fixed_256_g1(&ct.c2);
        let mut w_in = [0u8; 4 * CHUNK];
        w_in[0..CHUNK].copy_from_slice(&mm);
        w_in[CHUNK..2*CHUNK].copy_from_slice(&x_bytes);
        w_in[2*CHUNK..3*CHUNK].copy_from_slice(&c1_bytes);
        w_in[3*CHUNK..4*CHUNK].copy_from_slice(&c2_bytes);
        let w = hash_to_fr(&w_in);

        // HID = H(ID)
        let hid = hash_to_fr(&self.id);

        // hHID = h^{HID} * hs  （projective 用加法）
        let h_hid = (self.h_g1 * hid) + self.hs;

        // result = e(z, hHID) * v^{-w}
        let ez = Bls12_381::pairing(self.z_g1.into_affine(), g2.into_affine());
        let vw = self.v.pow((-w).into_bigint());
        let result = ez.0 * vw;

        // compare(result, lrsum)（不要求成立）
        let ok = result == lrsum;

        (mm, ok)
    }
}
