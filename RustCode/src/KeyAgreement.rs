use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective, Fq12, Fq, G2Affine, Config, Fq2};
use ark_ec::{pairing::Pairing, CurveGroup, PrimeGroup};
use ark_ff::{Field, PrimeField, UniformRand, Zero, One, inv};
use ark_serialize::CanonicalSerialize;
use rand::thread_rng;
use sha2::{Sha256, Digest};
use std::collections::HashMap;
use std::ops::{Mul, Add, Neg};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_std::iterable::Iterable;
use num_bigint::BigInt;
use num_traits::Num;
use crate::{tool, KeyAgreement};
use std::fs::File;
use std::io::{Write, BufWriter};
use ark_ff::BigInteger;
use tiny_keccak::{Hasher, Keccak};
// 公共参数结构 OK
pub struct PublicParameters {
    pub g1s: Vec<G1Projective>,
    pub g2s: Vec<G2Projective>,
}


// 使用压缩序列化 G1 点
pub fn compress_points_g1(p: &G1Projective) -> Vec<u8> {
    // 将点转换为仿射坐标
    let affine = p.into_affine();

    // 序列化 x 和 y 坐标为字节向量（每个坐标 32 字节）
    let mut buf = Vec::new();

    // 序列化 x 坐标（32 字节）
    let mut x_bytes = Vec::new();
    affine.x.serialize_uncompressed(&mut x_bytes).unwrap();
    x_bytes.reverse(); // 将 x 坐标字节反转为大端
    buf.extend_from_slice(&x_bytes);

    // 序列化 y 坐标（32 字节）
    let mut y_bytes = Vec::new();
    affine.y.serialize_uncompressed(&mut y_bytes).unwrap();
    y_bytes.reverse(); // 将 y 坐标字节反转为大端
    buf.extend_from_slice(&y_bytes);
    buf

}


pub fn compress_points_g2(p: &G2Projective) -> Vec<u8> {
    // 将点转换为仿射坐标
    let affine = p.into_affine();

    // 序列化 x 和 y 坐标为字节向量（每个坐标 32 字节）
    let mut buf = Vec::new();

    // 序列化 x1 坐标（32 字节）
    let mut x1_bytes = Vec::new();
    affine.x.c0.serialize_uncompressed(&mut x1_bytes).unwrap();
    x1_bytes.reverse(); // 将 c0 字节反转为大端
    buf.extend_from_slice(&x1_bytes);

    // 序列化 x2 坐标（32 字节）
    let mut x2_bytes = Vec::new();
    affine.x.c1.serialize_uncompressed(&mut x2_bytes).unwrap();
    x2_bytes.reverse(); // 将 c1 字节反转为大端
    buf.extend_from_slice(&x2_bytes);

    // 序列化 y1 坐标（32 字节）
    let mut y1_bytes = Vec::new();
    affine.y.c0.serialize_uncompressed(&mut y1_bytes).unwrap();
    y1_bytes.reverse(); // 将 c0 字节反转为大端
    buf.extend_from_slice(&y1_bytes);

    // 序列化 y2 坐标（32 字节）
    let mut y2_bytes = Vec::new();
    affine.y.c1.serialize_uncompressed(&mut y2_bytes).unwrap();
    y2_bytes.reverse(); // 将 c1 字节反转为大端
    buf.extend_from_slice(&y2_bytes);

    buf
}


// 输入: CRS G1 幂向量（三位）。
// 输出: CRS G1 字符串。
pub fn SolidityG1s(g1s: &Vec<G1Projective>) -> Vec<Vec<String>> {
    let mut res = Vec::new();
    for p in g1s {
        let a = p.into_affine();
        res.push(vec![a.x.to_string(), a.y.to_string()]);
    }
    res
}

// 输入: CRS G2 幂向量。
// 输出: CRS G2 字符串。
pub fn SolidityG2s(g2s: &Vec<G2Projective>) -> Vec<Vec<String>> {
    let mut v=Vec::new();
    for p in g2s {
        let a=p.into_affine();
        v.push(vec![a.x.c0.to_string(),a.x.c1.to_string(),a.y.c0.to_string(),a.y.c1.to_string()]);
    }
    v
}



pub fn Verify(g1s:&Vec<G1Projective>,g2s:&Vec<G2Projective>)->bool{

    //1. Pairing 测试 g1s[i] 与 g2s[i] 指数相同(1-L)：e(g1s[j],g2)=e(g1,g2s[j])
    let g1=G1Projective::generator();
    let g2=G2Projective::generator();
    for j in 1..=g1s.len()-1 {
        if(Bls12_381::pairing(g1s[j],g2)!=Bls12_381::pairing(g1,g2s[j])){
            println!("Verify: Round One Check Failed");
            return false;
        }
    }

    //2. Pairing 测试 g1s 与 g2s 是否存在递增: e(g1s[1],g2s[j]) = e(g1,g2s[j+1]) 3
    for j in 1..=2*(g1s.len()-1)-1{
        if (j==g1s.len()-1) || (j==g1s.len()){
            continue
        }
        if Bls12_381::pairing(g1s[1],g2s[j])!=Bls12_381::pairing(g1,g2s[j+1]){
            println!("Verify: Round Two Check Failed");
            return false;
        }
    }

    //3.  Pairing 测试 g1s 与 g2s 是否存在递增 (缺失项)
    if (Bls12_381::pairing(g1s[2],g2s[g1s.len()-1])!=Bls12_381::pairing(g1,g2s[g1s.len()-1+2])){
        return false;
    }

    true

}
pub fn TestVerify(L:usize)->(Vec<G1Projective>,Vec<G2Projective>,Vec<Fr>){

        let (alphaVectors, alpha) = tool::GenAlphaVector(L);
        let g1s = tool::GenG1Vector(&alphaVectors);
        let g2s = tool::GenG2Vector(&alphaVectors);
        let filename = format!("./{}.txt", L);
        //write_crs_to_txt(&filename, &g1s, &g2s);
    
        return (g1s,g2s,alphaVectors);
    
    //println!("0x{}", hex::encode(hash_g1s_g2s_simple(&g1s,&g2s)));
    //println!("{:?}", Verify(&g1s,&g2s));

    //println!("{:?}", KeyAgreement::VerifyG1Vector(g1s,proof1));
}

/// Fq -> 32-byte big-endian (Solidity uint256 encoding)
fn push_fq_u256_be(out: &mut Vec<u8>, x: &Fq) {
    let be = x.into_bigint().to_bytes_be();
    let mut buf = [0u8; 32];
    buf[32 - be.len()..].copy_from_slice(&be);
    out.extend_from_slice(&buf);
}

/// Fq2 -> (c0, c1), each as uint256 (32-byte big-endian)
fn push_fq2_u256_be(out: &mut Vec<u8>, x: &Fq2) {
    // arkworks 的 Fq2 通常是 c0 + c1 * u
    push_fq_u256_be(out, &x.c0);
    push_fq_u256_be(out, &x.c1);
}

/// keccak256( encodePacked( g1s.x,y..., g2s.x0,x1,y0,y1... ) )
pub fn hash_g1s_g2s_simple(g1s: &Vec<G1Projective>, g2s: &Vec<G2Projective>) -> [u8; 32] {
    // 预估容量：G1 每点 2*32=64 bytes；G2 每点 4*32=128 bytes
    let mut bytes = Vec::with_capacity(g1s.len() * 64 + g2s.len() * 128);

    // 1) G1: projective -> affine -> x||y
    for p in g1s {
        let a = p.into_affine();
        push_fq_u256_be(&mut bytes, &a.x);
        push_fq_u256_be(&mut bytes, &a.y);
    }

    // 2) G2: projective -> affine -> x.c0||x.c1||y.c0||y.c1
    for q in g2s {
        let a = q.into_affine();
        push_fq2_u256_be(&mut bytes, &a.x);
        push_fq2_u256_be(&mut bytes, &a.y);
    }

    // 3) Keccak-256
    let mut out = [0u8; 32];
    let mut k = Keccak::v256();
    k.update(&bytes);
    k.finalize(&mut out);
    out
}
