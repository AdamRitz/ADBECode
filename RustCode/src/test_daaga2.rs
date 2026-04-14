// 测试 DAAGA2 的独立文件
use crate::DAAGA2::*;

pub fn run_daaga2_tests() {
    println!("\n██████████████████████████████████████████████████");
    println!("█  DAAGKA2 性能测试 - 论文完整实现  █");
    println!("██████████████████████████████████████████████████\n");

    // 测试不同的组大小配置
    test_daagka2(20, 16);
    test_daagka2(50, 40);
    test_daagka2(100, 80);

    println!("\n██████████████████████████████████████████████████");
    println!("█  所有测试完成！  █");
    println!("██████████████████████████████████████████████████\n");
}

pub fn run_benchmark() {
    benchmark_daagka2();
}
