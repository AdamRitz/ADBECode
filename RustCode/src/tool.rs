use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective, Fq12};
use ark_ec::{pairing::Pairing, CurveGroup, PrimeGroup};
use ark_ff::{Field, PrimeField, UniformRand, Zero, One};
use ark_serialize::CanonicalSerialize;
use rand::thread_rng;
use sha2::{Sha256, Digest};

//生成  [1,a,a^2,...,a^{2*L}]
pub fn GenAlphaVector(L:usize)->(Vec<Fr>,Fr) {
    let mut rng = thread_rng();
    let alpha = Fr::rand(&mut rng);
    let mut alpha_powers = vec![Fr::one();  2*L + 1];
    for i in 1..=alpha_powers.len()-1 {
        alpha_powers[i] = alpha_powers[i - 1] * alpha;
    }
    (alpha_powers,alpha)
}
// 输入: Alpha 向量
// 输出: CRS G1 幂向量 G1s。注: 群组长度为 L 的时候 G1S 幂向量长度为 L+1。
// 公式: [g,g^a....]
pub fn GenG1Vector(alphaVector:&Vec<Fr>)->Vec<G1Projective> {
    let L = (alphaVector.len()-1)/2;
    let mut G1s:Vec<G1Projective>=Vec::new();
    for i in 0..=L {
        G1s.push(G1Projective::generator()*alphaVector[i]);
    }
    G1s
}

// 输入: Alpha 向量
// 输出: CRS G2 幂向量 G2s。注：L+1 处不生成用生成元 g 替代。 群组长度为 L 的时候 G2s 幂向量长度为 2L+1。
// 公式: [g,g^a....]
pub fn GenG2Vector(alphaVector:&Vec<Fr>)->Vec<G2Projective> {
    let L = (alphaVector.len()-1)/2;
    let mut G2s:Vec<G2Projective>=Vec::new();
    for i in 0..=2*L  {
        if i==L+1{
            G2s.push(G2Projective::zero());
            continue
        }
        G2s.push(G2Projective::generator()*alphaVector[i]);
    }
    G2s
}