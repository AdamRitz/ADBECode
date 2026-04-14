use std::collections::HashMap;


//For DBE
fn mainDBE() {
    // 初始化----------------------------------------------------------------------------------------
    let L = 5;
    let mut scheme = BGW::setup(L);

    // 生成公私钥对，私钥存储在外用于实验，公钥存储在 BGW 结构体中--------------------------------------------
    scheme.upks.push(UserPublicKey{g1s:G1Projective::generator(),g2s: vec![G2Projective::zero()]});
    let mut secret_keys = HashMap::new();
    for j in 1..L+1 {
        let (sk,pk)=scheme.keygen(j);
        secret_keys.insert(j, sk);
        scheme.upks.push(pk);
    }

    let S = vec![1,2, 3];
    let r = Fr::rand(&mut thread_rng());
    let gt = Bn254::pairing(scheme.g1, scheme.g2).0;
    let M = gt.pow(r.into_bigint());
    let ct = scheme.encrypt( &S, &M);

    let i = 3;
    let usk_i = &secret_keys[&i];
    let recovered = scheme.decrypt(i, &S, usk_i, &ct);
    if recovered ==M{
        println!("recovered");
    }else{
        println!("not recovered");
    }
    //计算下时间
}

fn MainGenPoint() {
    let g2: G2Projective = G2Projective::generator()+G2Projective::generator();
    let g2_affine: G2Affine = g2.into_affine();

    let x = g2_affine.x;
    let y = g2_affine.y;

    println!("Solidity G2 format:");
    println!("[\n  {},\n  {},\n  {},\n  {}\n]",
             x.c1.into_bigint(), x.c0.into_bigint(),
             y.c1.into_bigint(), y.c0.into_bigint()
    );
}