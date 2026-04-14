//     pub fn encrypt(
//         &self,
//         S: &[usize],
//         M: &Fq12,
//     ) -> Ciphertext {
//         // 产生随机数 s
//         let mut rng = thread_rng();
//         let s = Fr::rand(&mut rng);
//         // 求ct1
//         let ct1 = self.g1 * s;

//         // 求ct2
//         // 求 sum pks
//         let mut sum1=G1Projective::zero();
//         for &j in S {
//             sum1 +=  self.upks[j].g1s;
//         }
//         // 求 sum g^{a_is}
//         let mut sum2 = Fr::zero();
//         for &j in S {
//             sum2 +=  self.alpha_powers[j];
//         }
//         let gais= self.g1 * sum2;
//         let result = gais+sum1;
//         let ct2 = result*s;
// 
//         let key = Bn254::pairing(self.g1 *(s*self.alpha_powers[1]), self.g2 * self.alpha_powers[self.L]).0;
//         let ct3 = *M * key;
// 
//         Ciphertext { ct1, ct2, ct3 }
//     }
// 
//     pub fn decrypt(
//         &self,
//         i: usize,
//         S: &[usize],
//         usk_i: &UserSecretKey,
//         ct: &Ciphertext,
//     ) -> Fq12 {
//         // 计算 part1，虽然等下是求逆用
//         let part1 = Bn254::pairing(ct.ct2, self.g2 * self.alpha_powers[self.L +1- i]).0;
//         // 计算 part2（之前犯错原因为把生成元当作单位元）
//         let mut ski = usk_i.clone();
//         let mut sum = G2Projective::zero();
// 
//         for &j in S {
//             if j == i {
//                 continue;
//             }
//             sum=sum+self.upks[j].g2s[self.L+1-i]+self.g2*(self.alpha_powers[self.L+1+j-i]);
// 
//         }
//         let result=ski + sum;
//         let part2 = Bn254::pairing(ct.ct1, result).0;
//         ct.ct3 * part2 / part1
//     }
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