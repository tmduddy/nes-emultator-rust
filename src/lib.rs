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
    pub status: u8,

    /// ## Program Counter (PC)
    ///
    /// Holds the address for the next machine language instruction to be executed.
    pub program_counter: u16,

    /// ## Memory array (mem)
    ///
    /// Simulates the on board 64K memory of the NES.
    /// Note that different address blocks are reserved for different system functions.
    /// - 0x8000 -> 0xFFFF is reserved for Program ROM (PRG ROM)
    memory: [u8; 0xFFFF],
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            status: 0,
            program_counter: 0,
            memory: [0; 0xFFFF],
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
        self.status = 0b0000_0000;

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn run(&mut self) {
        // clock cycle loop
        loop {
            // Fetch the op code from the program at the counter.
            let ops_code = self.mem_read(self.program_counter);

            // Increment to the next program step.
            self.program_counter += 1;

            match ops_code {
                // Opcode `LDA`
                0xA9 => {
                    let param = self.mem_read(self.program_counter);
                    self.program_counter += 1;
                    self.lda(param);
                }
                // Opcode `TAX`
                0xAA => self.tax(),
                // Opcode `INX`
                0xE8 => self.inx(),
                // Opcode `BRK`
                0x00 => return,
                _ => todo!(),
            }
        }
    }

    /// 0xA9 op code `LDA`. Loads a value into the A register.
    fn lda(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// 0xAA Opcode `TAX`. Copies a value from register A to register X.
    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    /// 0xE8 op code `INX`. Increments the value in the X register by 1.
    fn inx(&mut self) {
        println!("{:?}", self.register_x);
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        // set or clear the [Z]ero flag.
        if result == 0 {
            self.status = self.status | 0b0000_0010;
        } else {
            self.status = self.status & 0b1111_1101;
        }

        // set or clear the [N]egative flag.
        if result & 0b1000_0000 != 0 {
            self.status = self.status | 0b1000_0000;
        } else {
            self.status = self.status & 0b0111_1111;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_0xa9_lda_immediate_load_data() {
        let mut cpu = CPU::new();
        // LDA #$05
        // BRK
        let program = vec![0xa9, 0x05, 0x00];
        cpu.load_and_run(program);
        assert_eq!(
            cpu.register_a, 0x05,
            "provided value should be found in register"
        );
        assert!(
            cpu.status & 0b0000_0010 == 0b00,
            "Zero flag should be unset"
        );
        assert!(
            cpu.status & 0b1000_0000 == 0,
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
        assert!(
            cpu.status | 0b0000_0000 == 0b0000_0010,
            "Zero flag should be set"
        );
        assert!(
            cpu.status & 0b1000_0000 == 0,
            "Negative flag should be unset"
        );
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
        assert!(cpu.status | 0b0000_0000 == 0, "Zero flag should be unset");
        assert!(
            cpu.status & 0b1000_0000 == 0,
            "Negative flag should be unset"
        );
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
        assert!(
            cpu.status | 0b0000_0000 == 0b0000_0010,
            "Zero flag should be set"
        );
        assert!(
            cpu.status & 0b1000_0000 == 0,
            "Negative flag should be unset"
        );
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
        assert!(
            cpu.status | 0b0000_0000 == 0b0000_0010,
            "Zero flag should be set"
        );
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
}
