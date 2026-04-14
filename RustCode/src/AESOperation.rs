use aes::Aes256;
use aes::cipher::{Array, BlockCipherEncrypt, BlockCipherDecrypt, KeyInit};
use aes::cipher::consts::U16;

pub fn AESEncryption(Key:[u8;32], M:Vec<u8>) -> [Array<u8, U16>; 24] {
    // 初始化密钥
    let b:[u8;32]=Key.try_into().unwrap();
    let key = Array::from(b);
    // 初始化明文 M
    let mut block: [Array<u8, U16>; 24] = Default::default();
    for i in 0..24 {
        let mut temp=[0u8; 16];
        temp.copy_from_slice(&M[i * 16..(i + 1) * 16]); // 从 M 中复制每个 16 字节的块
        block[i] = Array::from(temp);
    }
    let cipher = Aes256::new( & key);


    // 加密 block（就地加密）
    cipher.encrypt_blocks( & mut block);
    
    return block;
}
pub fn AESDecryption(Key:[u8;32], mut block: [Array<u8, U16>; 24] ) -> [Array<u8, U16>; 24] {
    // 初始化密钥
    let b:[u8;32]=Key.try_into().unwrap();
    let key = Array::from(b);
    let cipher = Aes256::new( & key);

    cipher.decrypt_blocks(& mut block);
    
    return block;
}