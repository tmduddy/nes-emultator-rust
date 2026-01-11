use crate::opcodes;
use std::collections::HashMap;

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

#[derive(Debug)]
pub struct Status {
    pub negative: bool,
    pub overflow: bool,
    /// Not used in this instruction set. In reality this is pinned high (1) but for our purposes
    /// it's easier to leave it permenantly false to maintain consistency with the other flags.
    pub no_op: bool,
    pub break_cmd: bool,
    /// Not used for the NES specific instruction set.
    pub decimal: bool,
    pub interrupt_disable: bool,
    pub zero: bool,
    pub carry: bool,
}

impl Status {
    fn new() -> Self {
        Status {
            negative: false,
            overflow: false,
            no_op: false,
            break_cmd: false,
            decimal: false,
            interrupt_disable: false,
            zero: false,
            carry: false,
        }
    }

    fn as_array(&self) -> [bool; 8] {
        [
            self.negative,
            self.overflow,
            self.no_op,
            self.break_cmd,
            self.decimal,
            self.interrupt_disable,
            self.zero,
            self.carry,
        ]
    }

    fn to_binary_string(&self) -> String {
        let mut bin_rep = vec!["0"; 8];

        for (i, val) in self.as_array().iter().enumerate() {
            if *val {
                bin_rep[i] = "1";
            }
        }

        bin_rep.join("")
    }

    pub fn to_binary(&self) -> u16 {
        u16::from_str_radix(&self.to_binary_string(), 2).expect("couldn't parse Status to binary")
    }
}

#[derive(Debug)]
pub struct CPU {
    /// ## The Accumulator register (A)
    ///
    /// Stores the results of arithmetic, logic, and memory access operations.
    /// It is used as an input parameter for some operations.
    pub register_a: u8,

    /// ## Index Register X (X)
    ///
    /// Used as an offset in specific memory addressing modes. Can be used for auxiliary storage
    /// needs (holding temp values, being used as a counter, etc.)
    pub register_x: u8,

    /// ## Index Register Y (Y)
    ///
    /// Used as an offset in specific memory addressing modes. Can be used for auxiliary storage
    /// needs (holding temp values, being used as a counter, etc.)
    pub register_y: u8,

    /// ## Processor status (P)
    ///
    /// 8-bit register represents 7 status flags that can be set or unse depending on the result of
    /// the last executed instruction
    /// for example: Z flag is set (1) if the result of an operation is 0, and is unset/erased (0)
    /// otherwise.
    ///
    /// The flags are usually written as NV1B DIZC
    /// and are defined as
    /// \[N\]egative Flag
    /// o\[V\]erflow Flag
    /// 1 - Always pushed as 1
    /// \[B\]reak Command
    /// \[D\]ecimal Mode Flag
    /// \[I\]nterrupt Disable
    /// \[Z\]ero Flag
    /// \[C\]arry Flag
    pub status: Status,

    /// ## Program Counter (PC)
    ///
    /// Holds the address for the next machine language instruction to be executed.
    pub program_counter: u16,

    /// ## Memory array (mem)
    ///
    /// Simulates the on board 64K memory of the NES.
    /// Note that different address blocks are reserved for different system functions.
    /// - 0x0000 -> 0x2000 is reserved for CPU RAM
    /// - 0x2000 -> 0x4020 is redirected to other hardware devices
    /// - 0x4020 -> 0x6000 is a special zone used differently by different carts. Ignored for now.
    /// - 0x6000 -> 0x8000 is mapped to RAM space on a cartridge, ignored for now.
    /// - 0x8000 -> 0xFFFF is reserved for Program ROM (PRG ROM)
    memory: [u8; 0xFFFF],
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: Status::new(),
            program_counter: 0,
            memory: [0; 0xFFFF],
        }
    }

    pub fn debug_print(&self) {
        println!(
            "\
A:\t0x{:X}
X:\t0x{:X}
Y:\t0x{:X}
Status:\t0b{:b}
PC:\t0x{:X}",
            self.register_a,
            self.register_x,
            self.register_y,
            self.status.to_binary(),
            self.program_counter
        );
    }

    /// Uses the active addressing mode to determine the atual addresses to read.
    fn get_operand_address(&mut self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter as u16,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),

            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }

            AddressingMode::Absolute_X => {
                let pos = self.mem_read_u16(self.program_counter);
                let addr = pos.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let pos = self.mem_read_u16(self.program_counter);
                let addr = pos.wrapping_add(self.register_y as u16);
                addr
            }

            AddressingMode::Indirect_X => {
                // Find the value pointed at by the PC
                let base = self.mem_read(self.program_counter);
                // Add the value in X to use as a ptr to the actual address
                let ptr = base.wrapping_add(self.register_x) as u16;

                // Find the two bytes indicated by the ptr
                let low = self.mem_read(ptr);
                let high = self.mem_read(ptr.wrapping_add(1));

                // Account for LE encoding and return those values as the new address
                (high as u16) << 8 | (low as u16)
            }
            AddressingMode::Indirect_Y => {
                // Find the value pointed at by the PC
                let base = self.mem_read(self.program_counter) as u16;

                // Find the two values pointed at by base
                let low = self.mem_read(base);
                let high = self.mem_read(base.wrapping_add(1));

                // account for LE encoding
                let deref_base = (high as u16) << 8 | (low as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    /// Read one byte from the memory array at the given address (index).
    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    /// Write one byte to the memory array at the given address (index).
    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }

    /// Read 2 bytes at once fromt he memory array at the given address (index), accounting for
    /// the little endian encoding expected by the NES.
    ///
    /// e.g. $12_34 -> 34_12
    fn mem_read_u16(&mut self, addr: u16) -> u16 {
        // swap the positions of the most and least signficant 8 bits.
        let low = self.mem_read(addr) as u16;
        let high = self.mem_read(addr + 1) as u16;
        high << 8 | low
    }

    /// Write 2 bytes at once fromt he memory array at the given address (index), accounting for
    /// the little endian encoding expected by the NES.
    ///
    /// e.g. writing 34_12 will store $1234
    fn mem_write_u16(&mut self, addr: u16, data: u16) {
        // swap the positions of the most and least signficant 8 bits.
        let high = (data >> 8) as u8;
        let low = (data & 0xff) as u8;
        self.mem_write(addr, low);
        self.mem_write(addr + 1, high);
    }

    /// Loads a given program into PRG ROM
    pub fn load(&mut self, program: Vec<u8>) {
        // Note that PRG ROM starts at 0x8000, all previous bytes are reserved for other
        // system functions.
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    /// Simulates the console's behavior when a new cartridge is inserted.
    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    /// Handles the Reset Interrupt signal sent when a cartridge is loaded.
    /// This signal informs the CPU to reset the internal state and start the program_counter at
    /// a specific memory address pointed to by 0xFFFC (set via self.load)
    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = Status::new();

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    /// Executes the program in PRG ROM.
    pub fn run(&mut self) {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;

        // Clock cycle loop
        loop {
            // Fetch the op code from the program at the counter.
            let code = self.mem_read(self.program_counter);
            let opcode = opcodes
                .get(&code)
                .expect(&format!("couldn't find code 0x{:X} in opcodes map", code));

            // Increment to the next program step immediately after reading.
            self.program_counter += 1;

            // Track the current state of the PC to identify if it needs to be incremented after
            // the code is run.
            let pc_state = self.program_counter;

            match opcode.instruction {
                "ADC" => self.adc(&opcode.addressing_mode),
                "LDA" => self.lda(&opcode.addressing_mode),
                "STA" => self.sta(&opcode.addressing_mode),
                "TAX" => self.tax(),
                "INX" => self.inx(),
                "BRK" => return,
                _ => {
                    panic!("bad opcode found somehow")
                }
            }
            if self.program_counter == pc_state {
                self.program_counter += (opcode.byte_count - 1) as u16;
            }
        }
    }

    /// `ADC` Adds a value from memory to the A register, stores in the A register.
    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut value = self.mem_read(addr);
        // If the carry flag is already set we need to add 1 to the value
        value = value.wrapping_add(match self.status.carry {
            true => 1,
            false => 0,
        });
        println!("ADC 0x{:X} (0x{:X})", addr, value);

        self.set_carry_flag((value as u16) + (self.register_a as u16) > 0xFF);
        self.update_zero_and_negative_flags(self.register_a);
        self.register_a = self.register_a.wrapping_add(value);
    }

    /// `LDA`. Loads a value into the A register.
    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        println!("LDA 0x{:X} (0x{:X})", addr, value);

        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `STA`. Copies a value from the A register into memory.
    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        println!("STA 0x{:X}", addr);
        self.mem_write(addr, self.register_a);
    }

    /// 0xAA Opcode `TAX`. Copies a value from register A to register X.
    fn tax(&mut self) {
        println!("TAX");
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    /// 0xE8 op code `INX`. Increments the value in the X register by 1.
    fn inx(&mut self) {
        println!("INX");
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn set_carry_flag(&mut self, should_set: bool) {
        self.status.carry = should_set;
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        // set or clear the [Z]ero flag.
        if result == 0 {
            self.status.zero = true;
        } else {
            self.status.zero = false;
        }

        // set or clear the [N]egative flag.
        if result & 0b1000_0000 != 0 {
            self.status.negative = true;
        } else {
            self.status.negative = false;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_status_to_binary_string_works_with_defaults() {
        let status = Status::new();
        assert_eq!(status.to_binary_string(), "00100000");
    }

    #[test]
    fn test_status_to_binary_works_with_defaults() {
        let status = Status::new();
        assert_eq!(status.to_binary(), 0b0010_0000);
    }

    #[test]
    fn test_status_works_with_non_default_values() {
        let mut status = Status::new();
        status.negative = true;
        status.carry = true;
        status.zero = true;

        assert_eq!(status.to_binary_string(), "10100011");
    }

    #[test]
    fn test_0xa9_lda_immediate_load_data() {
        let mut cpu = CPU::new();
        // LDA 0x05
        // BRK
        let program = vec![0xa9, 0x05, 0x00];
        cpu.load_and_run(program);
        assert_eq!(
            cpu.register_a, 0x05,
            "provided value should be found in register"
        );
        assert!(
            cpu.status.to_binary() & 0b0000_0010 == 0b00,
            "Zero flag should be unset"
        );
        assert!(
            cpu.status.to_binary() & 0b1000_0000 == 0,
            "Negative flag should be unset"
        );
    }

    #[test]
    fn test_0xa9_lda_handles_zero() {
        let mut cpu = CPU::new();
        // LDA #$0
        // BRK
        let program = vec![0xa9, 0x00, 0x00];

        cpu.load_and_run(program);
        assert_eq!(
            cpu.register_a, 0x00,
            "provided value should be found in register"
        );
        assert!(cpu.status.zero, "zero flag should be true");
        assert!(!cpu.status.negative, "Negative flag should be unset");
    }

    #[test]
    fn test_0xa5_lda_from_memory() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x55);

        // LDA 0x10
        // BRK
        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_0xaa_tax_copies_value_from_a() {
        let mut cpu = CPU::new();
        // LDA #$05
        // TAX
        // BRK
        let program = vec![0xa9, 0x05, 0xAA, 0x00];

        cpu.load_and_run(program);
        assert_eq!(
            cpu.register_x, 0x05,
            "provided value should be found in register"
        );
        assert!(!cpu.status.zero, "Zero flag should be unset");
        assert!(!cpu.status.negative, "Negative flag should be unset");
    }

    #[test]
    fn test_0xaa_tax_handles_zero() {
        let mut cpu = CPU::new();
        // LDA #$05
        // TAX
        // BRK
        let program = vec![0xa9, 0x00, 0xAA, 0x00];

        cpu.load_and_run(program);
        assert_eq!(
            cpu.register_x, 0x00,
            "provided value should be found in register"
        );
        assert!(cpu.status.zero, "Zero flag should be set");
        assert!(!cpu.status.negative, "Negative flag should be unset");
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        // LDA #$c0
        // TAX
        // INX
        // BRK
        let program = vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00];

        cpu.load_and_run(program);
        assert_eq!(
            cpu.register_x, 0xc1,
            "The value in X should be 1 higher than was loaded"
        );
    }

    #[test]
    fn test_inx_handles_zero() {
        let mut cpu = CPU::new();
        // LDA #$0xFF
        // TAX
        // INX
        // BRK
        let program = vec![0xA9, 0xFF, 0xAA, 0xE8, 0x00];

        cpu.load_and_run(program);
        assert_eq!(cpu.register_x, 0, "the value in X should rollover to 0");
        assert!(cpu.status.zero, "Zero flag should be set");
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::new();
        // LDA #$0xFF
        // TAX
        // INX
        // INX
        // BRK
        let program = vec![0xA9, 0xFF, 0xAA, 0xE8, 0xE8, 0x00];

        cpu.load_and_run(program);
        assert_eq!(
            cpu.register_x, 1,
            "the value in X should rollover to 0 and start counting up again"
        );
    }

    #[test]
    fn test_sta_loads_data() {
        let mut cpu = CPU::new();
        // LDA 0xFF
        // STA 0x10
        // BRK
        let program = vec![0xA9, 0xFF, 0x85, 0x10];

        cpu.load_and_run(program);

        assert_eq!(cpu.mem_read(0x10), 0xFF);
    }

    #[test]
    fn test_adc_adds_data_immediate() {
        let mut cpu = CPU::new();
        // LDA 0x04
        // ADC 0x05
        // BRK
        let program = vec![0xA9, 0x04, 0x69, 0x05, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 0x09,
            "The A register should hold the sum of the value in 0x10 and A"
        );
    }

    #[test]
    fn test_adc_handles_zero() {
        let mut cpu = CPU::new();
        // LDA 0x00
        // ADC 0x00
        // BRK
        let program = vec![0xA9, 0x00, 0x69, 0x00, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0x00, "The A register should hold 0");

        assert!(cpu.status.zero, "Zero flag should be set");
    }

    #[test]
    fn test_adc_adds_data_from_memory() {
        let mut cpu = CPU::new();
        // LDA 0x04
        // STA 0x10
        // LDA 0x05
        // ADC 0x10
        // BRK
        let program = vec![0xA9, 0x04, 0x85, 0x10, 0xA9, 0x05, 0x6d, 0x10, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 0x09,
            "The A register should hold the sum of the value in 0x10 and A"
        );
    }
}
