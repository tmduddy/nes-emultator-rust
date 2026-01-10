#[derive(Debug, Default)]
pub struct CPU {
    /// ## The Accumulator register (A)
    /// Stores the results of arithmetic, logic, and memory access operations.
    /// It is used as an input parameter for some operations.
    pub register_a: u8,
    /// ## Processor status (P)
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
    /// holds the address for the next machine language instruction to be executed.
    pub program_counter: u16,
}

impl CPU {
    pub fn new() -> Self {
        CPU::default()
    }

    pub fn interpret(&mut self, program: Vec<u8>) {
        // Initialize the program counter.
        self.program_counter = 0;

        // clock cycle loop
        loop {
            // Fetch the op code from the program at the counter.
            let ops_code = program[self.program_counter as usize];

            // Increment to the next program step.
            self.program_counter += 1;

            match ops_code {
                // Opcode `LDA`
                0xA9 => {
                    let param = program[self.program_counter as usize];
                    self.program_counter += 1;
                    self.lda(param);
                }
                // Opcode `BRK`
                0x00 => {
                    break;
                }
                _ => todo!(),
            }
        }
    }

    /// 0xA9 op code `LDA`. Loads a value into the A register.
    fn lda(&mut self, value: u8) {
        self.register_a = value;

        // set or clear the [Z]ero flag.
        if self.register_a == 0 {
            self.status = self.status | 0b0000_0010;
        } else {
            self.status = self.status & 0b1111_1101;
        }

        // set or clear the [N]egative flag.
        if self.register_a & 0b1000_0000 != 0 {
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
        cpu.interpret(vec![0xa9, 0x05, 0x00]);
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
        cpu.interpret(vec![0xa9, 0x00, 0x00]);
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
}
