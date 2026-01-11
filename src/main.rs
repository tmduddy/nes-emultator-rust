pub mod cpu;
pub mod opcodes;

#[macro_use]
extern crate lazy_static;

fn main() {
    let cpu = cpu::CPU::new();
    cpu.debug_print();
}
