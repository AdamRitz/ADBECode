use std::collections::HashMap;
use std::time::Instant;
use aes::cipher::Array;
use aes::cipher::consts::U16;
use rand::thread_rng;
use crate::{Ciphertext, UserPublicKey, BGW};
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective, Fq12,G2Affine, Fq2,G1Affine};
use ark_ec::{pairing::Pairing, PrimeGroup,AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField, UniformRand, Zero, One};
use ark_serialize::CanonicalSerialize;
use crate::DAAGA::{Paper2Ark, Paper3Ark};
// 测试解密是否成功
pub fn TestEncDec(L:usize) {
    // 1. 初始化----------------------------------------------------------------------------------------
    let mut scheme = BGW::setup(L);

    // 2. 生成公私钥对，私钥存储在外用于实验，公钥存储在 BGW 结构体中--------------------------------------------
    scheme.upks.push(UserPublicKey{g1s:G1Projective::generator(),g2s: vec![G2Projective::zero()]});
    let mut secret_keys = HashMap::new();
    for j in 1..L+1 {
        let (sk,pk)=scheme.keygen(j);
        secret_keys.insert(j, sk);
        scheme.upks.push(pk);
    }
    // S 代表目标集合

    let mut S = Vec::new();
    for i in 1..=L {
        S.push(i);
    }

    // 3. 生成加密目标集合 S，（S 代表目标集合）
    let r = Fr::rand(&mut thread_rng());
    let gt = Bls12_381::pairing(scheme.g1, scheme.g2).0;
    let M = gt.pow(r.into_bigint());
    
    // 4. 开始加密
    let startEncryption= Instant::now();
    let ct = scheme.NewEncrypt( &S, &M,&secret_keys[&(1 as usize)]);
    println!("加密耗时{:?}",startEncryption.elapsed(),);
    
    // 5. 开始解密
    let i = 3;
    let usk_i = &secret_keys[&i];
    let startDecryption = Instant::now();
    let recovered = scheme.NewDecrypt(i, &S, usk_i, &ct,&scheme.upks[1]).unwrap();
    println!("解密耗时{:?}",startDecryption.elapsed());


    if M==recovered{
        println!("解密成功");
    }else{
        println!("解密失败");
    }

}
// 测试全部线上的解密时间
pub fn TestEncDecTime(L:usize,times:usize) {
    
    // 1. 初始化
    let mut encryptionTime=0;
    let mut decryptionTime=0;
    let mut scheme = BGW::setup(L);

    // 2. 生成公私钥对，私钥存储在外用于实验，公钥存储在 BGW 结构体中--------------------------------------------
    scheme.upks.push(UserPublicKey{g1s:G1Projective::generator(),g2s: vec![G2Projective::zero()]});
    let mut secret_keys = HashMap::new();
    for j in 1..L+1 {
        let (sk,pk)=scheme.keygen(j);
        secret_keys.insert(j, sk);
        scheme.upks.push(pk);
    }
    // 3. 生成加密目标集合 S，（S 代表目标集合）
    let mut S = Vec::new();
    for i in 1..=L {
        S.push(i);
    }

    // 4. 明文 (随机数 r ) 映射到 GT 群 M
    let r = Fr::rand(&mut thread_rng());
    let gt = Bls12_381::pairing(scheme.g1, scheme.g2).0;
    let M = gt.pow(r.into_bigint());
    
    // 5. 开始
    let ct = scheme.NewEncrypt( &S, &M,&secret_keys[&(1 as usize)]);

    for t in 1..=times{
        let startEncryption = Instant::now();
        let ct = scheme.NewEncrypt( &S, &M,&secret_keys[&(1 as usize)]);
        encryptionTime += startEncryption.elapsed().as_nanos() as i128;
        
        let startDecryption = Instant::now();
        let recovered = scheme.NewDecrypt(1, &S, &secret_keys[&(1 as usize)], &ct,&scheme.upks[1]).unwrap();
        decryptionTime+=startDecryption.elapsed().as_nanos() as i128;

    }
    println!("L:{:?} 加密耗时{:?}",L,encryptionTime as f64 /times as f64 / 1_000_000.0);
    println!("L:{:?} 解密耗时{:?}",L,decryptionTime as f64 /times as f64 / 1_000_000.0);
    
}
// 测试全部线上的解密时间
pub fn TestEncLen(L:usize,times:usize) {

    // 1. 初始化

    let mut scheme = BGW::setup(L);

    // 2. 生成公私钥对，私钥存储在外用于实验，公钥存储在 BGW 结构体中--------------------------------------------
    scheme.upks.push(UserPublicKey{g1s:G1Projective::generator(),g2s: vec![G2Projective::zero()]});
    let mut secret_keys = HashMap::new();
    for j in 1..L+1 {
        let (sk,pk)=scheme.keygen(j);
        secret_keys.insert(j, sk);
        scheme.upks.push(pk);
    }
    // 3. 生成加密目标集合 S，（S 代表目标集合）
    let mut S = Vec::new();
    for i in 1..=L {
        S.push(i);
    }

    // 4. 明文 (随机数 r ) 映射到 GT 群 M
    let r = Fr::rand(&mut thread_rng());
    let gt = Bls12_381::pairing(scheme.g1, scheme.g2).0;
    let M = gt.pow(r.into_bigint());

    // 5. 开始
    let ct = scheme.NewEncrypt( &S, &M,&secret_keys[&(1 as usize)]);

    for t in 1..=times{

        let ct = scheme.NewEncrypt( &S, &M,&secret_keys[&(1 as usize)]);
        
        let recovered = scheme.NewDecrypt(1, &S, &secret_keys[&(1 as usize)], &ct,&scheme.upks[1]).unwrap();
    }


}
// 测试线下线上结合解密时间
pub fn TestEncDecTime2(L:usize,times:usize) {

    // 1. 初始化
    let mut encryptionTime=0;
    let mut decryptionTime=0;
    let mut scheme = BGW::setup(L);

    // 2. 生成公私钥对，私钥存储在外用于实验，公钥存储在 BGW 结构体中--------------------------------------------
    scheme.upks.push(UserPublicKey{g1s:G1Projective::generator(),g2s: vec![G2Projective::zero()]});
    let mut secret_keys = HashMap::new();
    for j in 1..L+1 {
        let (sk,pk)=scheme.keygen(j);
        secret_keys.insert(j, sk);
        scheme.upks.push(pk);
    }
    // 3. 生成加密目标集合 S，（S 代表目标集合）
    let mut S = Vec::new();
    for i in 1..=L {
        S.push(i);
    }

    // 4. 明文 (随机数 r ) 映射到 GT 群 M
    let r = Fr::rand(&mut thread_rng());
    let gt = Bls12_381::pairing(scheme.g1, scheme.g2).0;
    let M = gt.pow(r.into_bigint());

    // 5. 开始
    let (sum,KK)=scheme.Encrypt1(&S);
    let sum2=scheme.Decrypt1(1, &S, &secret_keys[&(1 as usize)]);
    for t in 1..=times{

        let startEncryption = Instant::now();
        let ct = scheme.Encrypt2( &S, &M,&secret_keys[&(1 as usize)],&sum,&KK);
        encryptionTime += startEncryption.elapsed().as_nanos() as i128;

        let startDecryption = Instant::now();
        let recovered = scheme.Decrypt2Fortest(1, &S, &secret_keys[&(1 as usize)], &ct,&scheme.upks[1],&sum2).unwrap();
        decryptionTime+=startDecryption.elapsed().as_nanos() as i128;
    }
    println!("L:{:?} 加密耗时{:?}",L,encryptionTime as f64 /times as f64 / 1_000_000.0);
    println!("L:{:?} 解密耗时{:?}",L,decryptionTime as f64 /times as f64 / 1_000_000.0);

}
pub fn test_paper2(L:usize,times:usize) {
    let mut encryptionTime=0;
    let mut decryptionTime=0;
    let p = Paper2Ark::setup(L);

    let mut rng = thread_rng();
    let sk = G1Projective::rand(&mut rng);
    let sum = G1Projective::rand(&mut rng);
    let m = [5u8; 256];
    for t in 1..=times {
        let startEncryption = Instant::now();
        let ct = p.enc( m);
        encryptionTime += startEncryption.elapsed().as_nanos() as i128;
        let startDecryption = Instant::now();

         p.dec(&ct,1,&G2Projective::generator());
        decryptionTime+=startDecryption.elapsed().as_nanos() as i128;
    }

    println!("L:{:?} 加密耗时{:?}",L,encryptionTime as f64 /times as f64 / 1_000_000.0);
    println!("L:{:?} 解密耗时{:?}",L,decryptionTime as f64 /times as f64 / 1_000_000.0);

}
pub fn test_paper3_like(L:usize,times:usize) {
    let mut encryptionTime=0;
    let mut decryptionTime=0;
    let p = Paper3Ark::setup(L);

    let mut rng = thread_rng();
    let sk = G1Projective::rand(&mut rng);
    let sum = G1Projective::rand(&mut rng);
    let m = [5u8; 256];
    for t in 1..=times {
        let startEncryption = Instant::now();
        let ct = p.enc(&sk, &sum, m);
        encryptionTime += startEncryption.elapsed().as_nanos() as i128;
        let sum1 = Fr::rand(&mut rng);
        let sum2 = Fr::rand(&mut rng);
        let startDecryption = Instant::now();

        let (mm, ok) = p.dec(&ct, &sk, sum1, sum2);
        decryptionTime+=startDecryption.elapsed().as_nanos() as i128;
    }

    println!("L:{:?} 加密耗时{:?}",L,encryptionTime as f64 /times as f64 / 1_000_000.0);
    println!("L:{:?} 解密耗时{:?}",L,decryptionTime as f64 /times as f64 / 1_000_000.0);

}

// fn TestEncrTimeWithTimes(L:usize,times:usize) {
//     // 初始化----------------------------------------------------------------------------------------
//     let mut scheme = BGW::setup(L);
// 
//     // 生成公私钥对，私钥存储在外用于实验，公钥存储在 BGW 结构体中--------------------------------------------
//     scheme.upks.push(UserPublicKey{g1s:G1Projective::generator(),g2s: vec![G2Projective::zero()]});
//     let mut secret_keys = HashMap::new();
//     let mut keyGenTime=0;
//     for j in 1..L+1 {
//         let startKeyGen = Instant::now();
//         let (sk,pk)=scheme.keygen(j);
//         keyGenTime+=startKeyGen.elapsed().as_nanos() as i128;
//         secret_keys.insert(j, sk);
//         scheme.upks.push(pk);
//     }
// 
//     // S 代表目标集合
//     let mut S = Vec::new();
//     for i in 1..=L {
//         S.push(i);
//     }
// 
//     //明文 (随机数 r ) 映射到 GT 群 M
//     let r = Fr::rand(&mut thread_rng());
//     let gt = Bls12_381::pairing(scheme.g1, scheme.g2).0;
//     let M = gt.pow(r.into_bigint());
//     let i = 3;
//     let usk_i = &secret_keys[&i];
//     let mut encryptionTime=0;
//     let mut decryptionTime=0;
// 
//     for t in 1..=times{
//         let startEncryption = Instant::now();
//         let ct = scheme.NewEncrypt( &S, &M);
//         println!("{:?}", ct.ct3);
//         encryptionTime += startEncryption.elapsed().as_nanos() as i128;
//         let startDecryption = Instant::now();
//         let recovered = scheme.NewDecrypt(i, &S, usk_i, &ct);
//         decryptionTime+=startDecryption.elapsed().as_nanos() as i128;
// 
//     }
// 
//     println!("L:{:?} 加密耗时{:?}",L,encryptionTime as f64 /times as f64 / 1_000_000.0);
//     println!("L:{:?} 解密耗时{:?}",L,decryptionTime as f64 /times as f64 / 1_000_000.0);
// 
// }