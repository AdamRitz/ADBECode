mod KeyAgreement;
mod KeyAgreementInterface;
mod tool;
mod AESOperation;
mod Test;
mod DAAGA;
mod DAAGA2;
mod Paper4;

use Test::*;
use std::time::Instant;
extern crate core;
use serde_json::json;
use warp::Filter;
//use core::num::fmt::Part::Num;
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective, Fq12,G2Affine, Fq2,G1Affine,Fq};
use ark_ec::{pairing::Pairing, PrimeGroup,AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField, UniformRand, Zero, One, BigInteger};
use rand::thread_rng;
use std::collections::HashMap;
use std::{env, string};
use std::ops::{Add, Neg};
use ark_ec::bn::Bn;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ec::twisted_edwards::Projective;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use sha2::{Digest, Sha256};
use num_bigint::BigInt;
use num_traits;
use num_traits::Num;
use serde_json::Value::String;
use serde::Serialize;
use std::fs::File;
use std::io::{BufWriter, Write};
use aes::Aes256;
use aes::cipher::{Array, BlockCipherEncrypt, BlockCipherDecrypt, KeyInit};
use aes::cipher::consts::U16;
use sha2::digest::Update;
use crate::AESOperation::AESEncryption;
use crate::DAAGA2::test_daagka2;
use crate::DAAGA::test_daagka;


///  BGW中用户公钥就是pp
pub struct PublicParameters {
    pub g1s:Vec<G1Projective>,
    pub g2s: Vec<G2Projective>,
}
#[derive(Serialize)]
pub struct UserSetupData {
    g1s: Vec<(std::string::String, std::string::String)>,
    g2s: Vec<(std::string::String, std::string::String, std::string::String, std::string::String)>,
    proof1: Vec<((std::string::String, std::string::String), (std::string::String, std::string::String), std::string::String)>,
    proof2: Vec<((std::string::String, std::string::String, std::string::String, std::string::String), (std::string::String, std::string::String, std::string::String, std::string::String), std::string::String)>

}
/// 用户私钥

pub struct UserSecretKey{
    pub t:Fr,
    pub sk:G2Projective,
}
/// 密文结构
pub struct Ciphertext {
    pub ct1: G1Projective,
    pub ct2: G1Projective,
    pub ct3: Fq12,
    pub ct4: G1Projective,
}


/// 生成 BGW 以及其参数
pub struct BGW {
    pub L: usize,
    pub alpha_powers: Vec<Fr>,
    pub upks: Vec<UserPublicKey>,
    pub pp:PublicParameters,
    pub g1: G1Projective,
    pub g2: G2Projective,
}
pub struct UserPublicKey{
    pub g1s:G1Projective,
    pub g2s:Vec<G2Projective>,
}
impl BGW {
    pub fn setup(L: usize) -> Self {
        let g1 = G1Projective::generator();
        let g2 = G2Projective::generator();
        // 取随机数 α
        let mut rng = thread_rng();
        let alpha = Fr::rand(&mut rng);

        // 计算 α 的幂，填充到向量中 1, a .....
        let mut alpha_powers = vec![Fr::one(); 2 * L + 2];
        for i in 1..alpha_powers.len() {
            alpha_powers[i] = alpha_powers[i - 1] * &alpha;
        }
        //生成元填充到参数中
        //生成公共参数pp
        // g^a,....g^L
        let mut g1s = Vec::new();
        for i in 1..=L {
            g1s.push(G1Projective::generator() * alpha_powers[i]);
        }
        // g^a,....g^2L
        let mut g2s = Vec::new();
        for i in 1..=2 * L {
            g2s.push(G2Projective::generator() * alpha_powers[i]);
        }

        g2s[L ] = G2Projective::zero(); // 现在才合法

        let pp=PublicParameters{g1s,g2s};
        //返回
        let upks = Vec::new();


        Self { L, alpha_powers, upks,pp,g1, g2 }

    }
    // 密钥生成函数 注： g2s 是用 g2 填充了 0 号位置，但是 Setup 没有填充。 
    pub fn keygen(&self, j: usize) -> (UserSecretKey, UserPublicKey ) {
        // 生成随机数t
        let t_j = Fr::rand(&mut thread_rng());
        // 生成usk
        let sk = self.g2 * (t_j * self.alpha_powers[self.L +1- j]);
        // 生成upk
        let g1s = self.g1*t_j;
        let mut g2s = Vec::new();
        g2s.push(self.g2);
        for k in 1..self.L+1 {
            if k==self.L+1-j{
                g2s.push(self.g2 );
                continue;
            }
            g2s.push(self.g2 * (t_j*self.alpha_powers[k]));
        }
        let mut upk = UserPublicKey{g1s,g2s};
        let mut usk=UserSecretKey{t:t_j,sk:sk};

        (usk,upk)

    }

    pub fn NewEncrypt(
        &self,
        S: &[usize],
        M: &Fq12,
        usk: &UserSecretKey,     
    ) -> Ciphertext {
        // 产生随机数 s
        let mut rng = thread_rng();
        let s = Fr::rand(&mut rng);
        // 1. 求ct1
        let ct1 = self.g1 * s;

        // 2. 求ct2
        // 求 sum pks
        let mut sum1=G1Projective::zero();
        for &j in S {
            sum1 +=  self.upks[j].g1s;
        }
        // 求 sum g^{a_is}
        let mut sum2 = Fr::zero();
        for &j in S {
            sum2 +=  self.alpha_powers[j];
        }
        let gais= self.g1 * sum2;
        let result = gais+sum1;
        let ct2 = result*s;
        // 3. 求 ct3
        let K = Bls12_381::pairing(self.pp.g1s[0]*s, self.pp.g2s[self.L-1]).0;
        let ct3=K*M;
        // 7. 求 ct4
        let mut byteM=Vec::new();
        M.serialize_uncompressed(&mut byteM).unwrap();
        K.serialize_uncompressed(&mut byteM).unwrap();
        let digest = Sha256::digest(&byteM);
        let ct4 = self.g1 * Fr::from_be_bytes_mod_order(&digest)* usk.t;        // h ∈ G1
        Ciphertext { ct1, ct2, ct3,ct4}
    }
    pub fn Encrypt1(
        &self,
        S: &[usize]
    ) -> (G1Projective,Fq12) {
        let mut sum1=G1Projective::zero();
        for &j in S {
            sum1 +=  self.upks[j].g1s;
        }
        // 求 sum g^{a_is}
        let mut sum2 = Fr::zero();
        for &j in S {
            sum2 +=  self.alpha_powers[j];
        }
        let gais= self.g1 * sum2;
        let sum = gais+sum1;
        let KK = Bls12_381::pairing(self.pp.g1s[0], self.pp.g2s[self.L-1]).0;
        return (sum,KK)
    }
    pub fn Encrypt2(
        &self,
        S: &[usize],
        M: &Fq12,
        usk: &UserSecretKey,
        sum:&G1Projective,
        KK:&Fq12
    ) -> Ciphertext {
        // 产生随机数 s
        let mut rng = thread_rng();
        let s = Fr::rand(&mut rng);
        // 1. 求ct1
        let ct1 = self.g1 * s;

        // 2. 求ct2
        let ct2 = *sum*s;
        // 3. 求 ct3
        let K=KK.pow(s.into_bigint());

        let ct3=K*M;
        // 7. 求 ct4
        let mut byteM=Vec::new();
        M.serialize_uncompressed(&mut byteM).unwrap();
        K.serialize_uncompressed(&mut byteM).unwrap();
        let digest = Sha256::digest(&byteM);
        let ct4 = self.g1 * Fr::from_be_bytes_mod_order(&digest)* usk.t;        // h ∈ G1
        Ciphertext { ct1, ct2, ct3,ct4}
    }
    pub fn NewDecrypt(
        &self,
        i: usize,
        S: &[usize],
        usk: &UserSecretKey,
        ct: &Ciphertext,
        upk: &UserPublicKey
    ) -> Option<Fq12> {  // 返回 Option 类型
        // 计算 part1，虽然等下是求逆用
        let part1 = Bls12_381::pairing(ct.ct2, self.pp.g2s[self.L-i]).0;

        // 计算 part2（之前犯错原因为把生成元当作单位元）
        let mut ski = usk.clone();
        let mut sum = G2Projective::zero();

        for &j in S {
            if j == i {
                continue;
            }
            sum = sum + self.upks[j].g2s[self.L + 1 - i] + self.pp.g2s[self.L  + j - i];
        }

        let result = ski.sk + sum;
        let part2 = Bls12_381::pairing(ct.ct1, result).0;
        let K = part1 / part2;
        let M = ct.ct3*K.inverse().unwrap();

        // 计算签名
        let mut byteM=Vec::new();
        M.serialize_uncompressed(&mut byteM).unwrap();
        K.serialize_uncompressed(&mut byteM).unwrap();
        let digest = Sha256::digest(&byteM);
        let left=Bls12_381::pairing(ct.ct4,self.pp.g2s[0]);
        let right=Bls12_381::pairing(self.g1 * Fr::from_be_bytes_mod_order(&digest),upk.g2s[1]);

        // 验签
        if left == right {
            //println!("验签通过");
            return Some(M);  // 返回解密后的明文 M
        }

        println!("验签失败");
        None  // 如果验签失败，返回 None
    }
    pub fn Decrypt1(
        &self,
        i: usize,
        S: &[usize],
        usk: &UserSecretKey,
    ) -> G2Projective {  // 返回 Option 类型
        let mut ski = usk.clone();
        let mut sum = G2Projective::zero();

        for &j in S {
            if j == i {
                continue;
            }
            sum = sum + self.upks[j].g2s[self.L + 1 - i] + self.pp.g2s[self.L  + j - i];
        }

        let result = ski.sk + sum;
        return result
    }
    pub fn Decrypt2(
        &self,
        i: usize,
        S: &[usize],
        usk: &UserSecretKey,
        ct: &Ciphertext,
        upk: &UserPublicKey,
        sum:&G2Projective
    ) -> Option<Fq12> {  // 返回 Option 类型

        let ct1_neg = -ct.ct1;

        // a: G1 侧，b: G2 侧；这里传 &G1 / &G2，arkworks 0.5 会通过 From<&G1> / From<&G2>
        // 自动转成 G1Prepared / G2Prepared
        let ml = Bls12_381::multi_miller_loop(
            [&ct.ct2, &ct1_neg],                 // a: impl IntoIterator<Item = impl Into<G1Prepared>>
            [&self.pp.g2s[self.L - i], sum],  // b: impl IntoIterator<Item = impl Into<G2Prepared>>
        );

        // final_exponentiation 返回 Option<PairingOutput<Bls12_381>>
        let K = Bls12_381::final_exponentiation(ml)
            .expect("final_exponentiation should not fail")
            .0; // PairingOutput<Bls12_381>(TargetField) -> Fq
        let M = ct.ct3*K.inverse().unwrap();

        // 计算签名
        let mut byteM=Vec::new();
        M.serialize_uncompressed(&mut byteM).unwrap();
        K.serialize_uncompressed(&mut byteM).unwrap();
        let digest = Sha256::digest(&byteM);



        let ml = Bls12_381::multi_miller_loop(
            [&ct.ct4, &(self.g1 * Fr::from_be_bytes_mod_order(&digest))],                 // a: impl IntoIterator<Item = impl Into<G1Prepared>>
            [&self.pp.g2s[0], &(-upk.g2s[1])],  // b: impl IntoIterator<Item = impl Into<G2Prepared>>
        );
        // 验签
        if Bls12_381::final_exponentiation(ml).expect("final_exponentiation should not fail").0  == Fq12::one() {
            //println!("验签通过");
            return Some(M);  // 返回解密后的明文 M
        }

        println!("验签失败");
        None  // 如果验签失败，返回 None

    }
    // 没用 pairing 加速对齐其他论文
    pub fn Decrypt2Fortest(
        &self,
        i: usize,
        S: &[usize],
        usk: &UserSecretKey,
        ct: &Ciphertext,
        upk: &UserPublicKey,
        sum:&G2Projective
    ) -> Option<Fq12> {  // 返回 Option 类型

        let ct1_neg = -ct.ct1;

        // a: G1 侧，b: G2 侧；这里传 &G1 / &G2，arkworks 0.5 会通过 From<&G1> / From<&G2>
        // 自动转成 G1Prepared / G2Prepared
        let ml = Bls12_381::multi_miller_loop(
            [&ct.ct2, &ct1_neg],                 // a: impl IntoIterator<Item = impl Into<G1Prepared>>
            [&self.pp.g2s[self.L - i], sum],  // b: impl IntoIterator<Item = impl Into<G2Prepared>>
        );

        // final_exponentiation 返回 Option<PairingOutput<Bls12_381>>
        let K = Bls12_381::final_exponentiation(ml)
            .expect("final_exponentiation should not fail")
            .0; // PairingOutput<Bls12_381>(TargetField) -> Fq
        let M = ct.ct3*K.inverse().unwrap();

        // 计算签名
        let mut byteM=Vec::new();
        M.serialize_uncompressed(&mut byteM).unwrap();
        K.serialize_uncompressed(&mut byteM).unwrap();
        let digest = Sha256::digest(&byteM);



        // let ml = Bls12_381::multi_miller_loop(
        //     [&ct.ct4, &(self.g1 * Fr::from_be_bytes_mod_order(&digest))],                 // a: impl IntoIterator<Item = impl Into<G1Prepared>>
        //     [&self.pp.g2s[0], &(-upk.g2s[1])],  // b: impl IntoIterator<Item = impl Into<G2Prepared>>
        // );
        // // 验签
        // if Bls12_381::final_exponentiation(ml).expect("final_exponentiation should not fail").0  == Fq12::one() {
        //     //println!("验签通过");
        //     return Some(M);  // 返回解密后的明文 M
        // }
        //
        // println!("验签失败");
        // None  // 如果验签失败，返回 None
        let ea = Bls12_381::pairing(&ct.ct4, &self.pp.g2s[0]);
        let eb = Bls12_381::pairing(&(self.g1 * Fr::from_be_bytes_mod_order(&digest)), &(upk.g2s[1]));
        if ea.0==eb.0 {
            //println!("验签通过");
            return Some(M);  // 返回解密后的明文 M
        }
        None  // 如果验签失败，返回 None
    }

}
// fn main(){
//     let (g1s, g2s, proof1, proof2) = KeyAgreement::UserSetUP();
//     let js = serde_json::to_string(&g1s).unwrap();
//     let response = json!({
//         "g1s": g1s,
//         "g2s": g2s,
//         "proof1": proof1,
//         "proof2": proof2
//     });
//
// }
#[tokio::main]
async fn Server() {
      let sum_route = warp::path!("sum" / i64 / i64)
        .map(|a: i64, b: i64| {
            let sum = a + b;
            warp::reply::json(&format!("{}", sum))
        });
    // let UserSetUp = warp::path!("UserSetUp"/usize)
    //     .map(|L:usize| {
    //         // 调用 UserSetUP，返回结果并包装成 JSON 格式响应
    //         let (g1s, g2s, proof1, proof2) = KeyAgreement::UserSetUP(L);
    //         let response = json!({
    //     "g1s": g1s,
    //     "g2s": g2s,
    //     "proof1": proof1,
    //     "proof2": proof2
    // });
    //
    //         // 将所有返回的数据打包成一个对象，确保每个字段名是明确的
    //         println!("{:?}{:?}",proof1,response);
    //         warp::reply::json(&response)
    //     });

    let UserSetUpAndKeyGen = warp::path!("UserSetUpAndKeyGen"/usize)
        .map(|L:usize| {


            // 调用 UserSetUP，返回结果并包装成 JSON 格式响应


            let j=2;
            let t_j = Fr::rand(&mut thread_rng());
            let (alphaVectors,alpha)=tool::GenAlphaVector(L);
            let g1s=tool::GenG1Vector(&alphaVectors);
            let g2s=tool::GenG2Vector(&alphaVectors);
            // 生成usk
            let usk = g2s[L+1-j]*t_j;
            // 生成upk
            let keyG1s = (G1Projective::generator()*t_j);
            let keyG1sAffine=keyG1s.into_affine();
            let mut serilizedkeyG1s=Vec::new();
            serilizedkeyG1s.push(keyG1sAffine.x.to_string());
            serilizedkeyG1s.push(keyG1sAffine.y.to_string());
            let mut keyG2s = Vec::new();
            keyG2s.push(G2Projective::generator());
            for k in 1..=L {
                if k==L+1-j{
                    keyG2s.push(G2Projective::zero() );
                    continue;
                }
                keyG2s.push( (g2s[k]*t_j));
            }
            let r=verify_public_key(g1s.clone(),g2s.clone(),&UserPublicKey{g1s:keyG1s,g2s:keyG2s.clone()},2,5);
            //println!("{:?}",G2Projective::generator()==G2Projective::generator());
            println!("{:?}",r);
            let response = json!({
        "g1s": KeyAgreement::SolidityG1s(&g1s),
        "g2s": KeyAgreement::SolidityG2s(&g2s),
        "keyG1s":serilizedkeyG1s,
        "keyG2s":KeyAgreement::SolidityG2s(&keyG2s)
    });
            // 将所有返回的数据打包成一个对象，确保每个字段名是明确的
            warp::reply::json(&response)
        });


    warp::serve(UserSetUpAndKeyGen)
        .run(([127, 0, 0, 1], 3030))  // 监听 localhost:3030
        .await;

}

pub fn verify_public_key(g1s:Vec<G1Projective>,g2s:Vec<G2Projective>, pk: &UserPublicKey, j: usize,L:usize) -> bool {


    // 获取 expected pairing：e([alpha^L]_2, upk_j^*)
    let r =Bls12_381::pairing(pk.g1s,g2s[L]);
    let mut tail = Bls12_381::pairing(g1s[0], &pk.g2s[L]);

    let a=pk.g1s.into_affine();
    let b=g2s[L].into_affine();
    let c=g1s[0].into_affine();
    let d=pk.g2s[L].into_affine();
    println!("{:?}",Bls12_381::pairing(a,b)==Bls12_381::pairing(c,d));
    println!("{:?}",[a.x.to_string(),a.y.to_string(),b.x.c1.to_string(),b.x.c0.to_string(),b.y.c1.to_string(),b.y.c0.to_string(),
    c.x.to_string(),c.y.to_string(),d.x.c1.to_string(),d.x.c0.to_string(),d.y.c1.to_string(),d.y.c0.to_string()]);

    for i in 1..=L+1-j-1{
        if(Bls12_381::pairing(g1s[L-i],pk.g2s[i])!=r){
            return  false
        }
    }
    for i in L+1-j+1..=L{
        if(Bls12_381::pairing(g1s[L-i],pk.g2s[i])!=r){
            return  false
        }
    }

    // 返回 true，表示验证通过
    return true
}
fn pad48_to_64_be(x48: &[u8]) -> [u8; 64] {
    assert_eq!(x48.len(), 48);
    let mut out = [0u8; 64];
    // EIP-2537: Fp is 64-byte BE, top 16 bytes must be zero  :contentReference[oaicite:5]{index=5}
    out[16..64].copy_from_slice(x48);
    out
}
fn G1ElementToBytes(p:&G1Projective) -> [u8;128] {
    let mut out = [0u8; 128];
    let mut xBytes =[0u8;64];
    let mut yBytes =[0u8;64];
    if p.is_zero() {
        return out;
    }
    // 1. 改变为仿射坐标
    let a=p.into_affine();
    // 2. into_bigint 转为大数，to_bytes_be 转为 big endian 大端。
    let x = a.x.into_bigint().to_bytes_be();
    let y = a.y.into_bigint().to_bytes_be();
    // 3. 填充
    xBytes[64 - x.len()..].copy_from_slice(&x);
    yBytes[64 - y.len()..].copy_from_slice(&y);
    out[0..64].copy_from_slice(&xBytes);
    out[64..128].copy_from_slice(&yBytes);
    out
}
fn G2ElementToBytes(p:&G2Projective)->[u8;256]{
    let mut out = [0u8; 256];
    let mut x0Bytes =[0u8;64];
    let mut x1Bytes =[0u8;64];
    let mut y0Bytes =[0u8;64];
    let mut y1Bytes =[0u8;64];
    if p.is_zero() {
        return out;
    }
    // 1. 改变为仿射坐标
    let a=p.into_affine();
    // 2. into_bigint 转为大数，to_bytes_be 转为 big endian 大端。
    let x0 = a.x.c0.into_bigint().to_bytes_be();
    let x1 = a.x.c1.into_bigint().to_bytes_be();
    let y0 = a.y.c0.into_bigint().to_bytes_be();
    let y1 = a.y.c1.into_bigint().to_bytes_be();
    // 3. 填充

    x0Bytes[64 - x0.len()..].copy_from_slice(&x0);
    x1Bytes[64 - x1.len()..].copy_from_slice(&x1);
    y0Bytes[64 - y0.len()..].copy_from_slice(&y0);
    y1Bytes[64 - y1.len()..].copy_from_slice(&y1);
    out[0..64].copy_from_slice(&x0Bytes);
    out[64..128].copy_from_slice(&x1Bytes);
    out[128..192].copy_from_slice(&y0Bytes);
    out[192..256].copy_from_slice(&y1Bytes);
    out
}
pub fn write_key_to_txt(
    path: &str,
    g1s: &G1Projective,
    g2s: &Vec<G2Projective>,
) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);


    let a = G1ElementToBytes(g1s);
    write!(w, "\"0x{}\"", hex::encode(a))?;
    writeln!(w, ",")?;
    writeln!(w, " [")?;
    for (i, p) in g2s.iter().enumerate() {
        if (i==0){

            continue;}
        let a = G2ElementToBytes(p);
        write!(
            w,
            "\"0x{}\"",
            hex::encode(a)
        )?;
        if i + 1 != g2s.len() {
            writeln!(w, ",")?;
        }
    }
    writeln!(w, "\n]")?;

    Ok(())
}
pub fn write_crs_to_txt(
    path: &str,
    g1s: &Vec<G1Projective>,
    g2s: &Vec<G2Projective>,
) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);

    writeln!(w, "[")?;
    for (i, p) in g1s.iter().enumerate() {
        let a = G1ElementToBytes(p);
        write!(w, "\"0x{}\"", hex::encode(a))?;
        if i + 1 != g1s.len() {
            writeln!(w, ",")?;
        }
    }
    writeln!(w, "]")?;
    writeln!(w, ",")?;
    writeln!(w, " [")?;
    for (i, p) in g2s.iter().enumerate() {

        let a = G2ElementToBytes(p);
        write!(
            w,
            "\"0x{}\"",
            hex::encode(a)
        )?;
        if i + 1 != g2s.len() {
            writeln!(w, ",")?;
        }
    }
    writeln!(w, "\n]")?;

    Ok(())
}
fn GenSolidityCRS(L:usize)->BGW{
    let mut scheme = BGW::setup(L);
    let s = format!("{}test.txt", L);
    write_crs_to_txt(&s,&scheme.pp.g1s,&scheme.pp.g2s);
    return scheme;
}
fn GenSolidityKey(L:usize,schme:BGW){
    let  (sk,pk)=schme.keygen(1);
    let s = format!("{}testkey.txt", L);
    write_key_to_txt(&s,&pk.g1s,&pk.g2s);
}
// 96 192 576
fn Len(){
    let mut a = Vec::new();
    G1Projective::generator().into_affine().serialize_uncompressed(&mut a).unwrap();
    let mut b = Vec::new();
    G2Projective::generator().into_affine().serialize_uncompressed(&mut b).unwrap();
    let mut c=Vec::new();
    Bls12_381::pairing(G1Projective::generator().into_affine(),G2Projective::generator().into_affine()).serialize_uncompressed(&mut c).unwrap();


    println!("{:?}",a.len());
    println!("{:?}",b.len());
    println!("{:?}",c.len())
}
fn TestEncAll(to:usize,times:usize){
    // Test ADBE
    println!("Testing ADBE");
    for i in (20..=to).step_by(20){
        TestEncDecTime2(i,times);
    }
    // Test DAAGKA
    println!("Testing DAAGKA");
    for i in (20..=to).step_by(20){
        test_daagka(i,times);
    }
    println!("Testing IBEGKA");
    for i in (20..=to).step_by(20){
        test_paper2(i,times);
    }
    println!("Testing BPSC");
    for i in (20..=to).step_by(20){
        test_paper3_like(i,times)
    }
}
fn TestOnce(){
    // Test ADBE
    TestEncDecTime2(10,5);
    // Test DAAGKA
    test_daagka(10,5);
    test_paper2(10,5);
}
fn main() {
    // for i in(20..=200).step_by(20){
    //     let scheme=GenSolidityCRS(i);
    //     GenSolidityKey(i,scheme);
    // }
    //test_daagka(5);
    // ---------------- G1 generator -> 128 bytes (x||y) ----------------

    let mut a = Vec::new();
    G1Projective::generator().into_affine().serialize_uncompressed(&mut a).unwrap();
    G1Projective::generator().into_affine().serialize_uncompressed(&mut a).unwrap();
    G1Projective::generator().into_affine().serialize_uncompressed(&mut a).unwrap();
    Bls12_381::pairing(G1Projective::generator(),G2Projective::generator()).serialize_uncompressed(&mut a).unwrap();
    print!("{} {}", hex::encode(&a),a.len());
    // for i in (100..=100).step_by(20){
    //     TestEncDecTime(i,20);
    // }
    // 重要的

    
    // for i in (20..=20).step_by(20){
    //     let (g1s,g2s,alphapowers)=KeyAgreement::TestVerify(i);
    //     let (sk,pk)=SolidityKeyGen(g1s,g2s,alphapowers);
    //     let filename = format!("./{}.txt", i);
    //     write_pk_for_solidity(&filename,&pk);
    // }

    //TestEncDecTime2(10,1);
    //TestEncDecTime2(20,1);
    //TestEncDecTime2(50,1);
    //test_daagka2(10,10);
}

// 链下 UserSetup，Join 测试函数。 若需要产生对应的密码材料，需要取消掉注释。
pub fn TestOffChain(){
    let mut AgreeTime=0;
    let mut KeyTime=0;
    for i in (20..=200).step_by(20){
        AgreeTime=0;
        KeyTime=0;
        for j in 0..20{
            let startAgree = Instant::now();
            let (g1s,g2s,alphapowers)=KeyAgreement::TestVerify(i);
            AgreeTime+=startAgree.elapsed().as_nanos() as i128;
            let startKey = Instant::now();
            SolidityKeyGen(g1s,g2s,alphapowers);
            KeyTime+=startKey.elapsed().as_nanos() as i128;

        }
        println!("L:{:?} UserSetup耗时{:?} ms",i,AgreeTime as f64 /20 as f64 / 1_000_000.0);
        println!("L:{:?} KeyGen{:?} ms",i,KeyTime as f64 /20 as f64 / 1_000_000.0);

        //let filename = format!("./{}key.txt", i);
        //write_pk_for_solidity(&filename,&pk);
    }
    
}
// upk 中的 g2s 带填充了。 j=2
pub fn SolidityKeyGen(g1s:Vec<G1Projective>,g2s:Vec<G2Projective>,alpha_powers:Vec<Fr>) -> (UserSecretKey, UserPublicKey ) {
    // 输入的 alpha_powers 长度为 2L+1，同样 0 位是填充的 1 元。
    let j=2;
    // 5
    let L=g1s.len()-1;
    // 生成随机数t
    let g2=G2Projective::generator();
    let g1=G1Projective::generator();
    let t_j = Fr::rand(&mut thread_rng());
    // 生成usk
    let sk = g2 * (t_j * alpha_powers[L +1- j]);
    // 生成upk
    let g1s = g1*t_j;
    let mut g2s = Vec::new();
    // 填充
    g2s.push(g2);
    // 1..6=1-5
    for k in 1..L+1 {
        if k==L+1-j{
            g2s.push(g2 );
            continue;
        }
        g2s.push(g2 * (t_j*alpha_powers[k]));
    }
    let mut upk = UserPublicKey{g1s,g2s};
    let mut usk=UserSecretKey{t:t_j,sk:sk};

    (usk,upk)

}


/// 把 upk 写成 Solidity 可用的 PK 输入（文本文件）
pub fn write_pk_for_solidity(path: &str, upk: &UserPublicKey) -> std::io::Result<()> {
    let f = File::create(path)?;
    let mut w = BufWriter::new(f);

    let g1a: G1Affine = upk.g1s.into_affine();
    let x = g1a.x().expect("G1 inf").into_bigint().to_string();
    let y = g1a.y().expect("G1 inf").into_bigint().to_string();

    writeln!(w, "[")?;
    
    writeln!(w, "  [{},{}],", x, y)?;

    writeln!(w, "[")?;
    for (i, p) in upk.g2s.iter().enumerate() {
        let a: G2Affine = p.into_affine();
        let ax = a.x().expect("G2 inf");
        let ay = a.y().expect("G2 inf");

        let x1 = ax.c0.into_bigint().to_string();
        let x2 = ax.c1.into_bigint().to_string();
        let y1 = ay.c0.into_bigint().to_string();
        let y2 = ay.c1.into_bigint().to_string();

        if i + 1 == upk.g2s.len() {
            writeln!(w, "    [{},{},{},{}]", x1, x2, y1, y2)?;
        } else {
            writeln!(w, "    [{},{},{},{}],", x1, x2, y1, y2)?;
        }
        
    }
    writeln!(w, "]")?;
    writeln!(w, "]")?;

    w.flush()?;
    Ok(())
}



fn TestUserSetup(L:usize,times:usize) {
    let mut SetUP=0;
    let mut KeyGen=0;
    for i in 0..times{
        let start = Instant::now();
        let mut scheme = BGW::setup(L);
        SetUP+= start.elapsed().as_nanos() as i128;
        let start = Instant::now();
        let (sk,pk)=scheme.keygen(1);
        KeyGen+= start.elapsed().as_nanos() as i128;
    }

    println!("L:{:?} UserSetupTime{:?}",L,SetUP as f64 /times as f64 / 1_000_000.0);
    println!("L:{:?} KeyGen{:?}",L,KeyGen as f64 /times as f64 / 1_000_000.0);
    }

fn Past(){


    //TestEncryption(10);
    // TestUserSetup(20,10);
    // TestUserSetup(40,10);
    // TestUserSetup(60,10);
    // TestUserSetup(80,10);
    // TestUserSetup(100,10);
    // TestUserSetup(120,10);
    // TestUserSetup(140,10);
    // TestUserSetup(160,10);
    // TestUserSetup(180,10);
    // TestUserSetup(200,10);


    let L=5;
    let j=2;
    let t_j = Fr::rand(&mut thread_rng());
    let (alphaVectors,alpha)=tool::GenAlphaVector(L);

    let g1s=tool::GenG1Vector(&alphaVectors);
    let g2s=tool::GenG2Vector(&alphaVectors);
    // 生成usk
    let usk = g2s[L+1-j]*t_j;
    // 生成upk

    let keyG1s = (G1Projective::generator()*t_j);
    let mut keyG2s = Vec::new();
    keyG2s.push(G2Projective::generator());
    for k in 1..=L {
        if k==L+1-j{
            keyG2s.push(G2Projective::zero() );
            continue;
        }
        keyG2s.push( (g2s[k]*t_j));
    }
    println!("{:?}",keyG2s.len());

    let r=verify_public_key(g1s,g2s,&UserPublicKey{g1s:keyG1s,g2s:keyG2s},2,5);
    //println!("{:?}",G2Projective::generator()==G2Projective::generator());
    // println!("{:?}",r);
}


