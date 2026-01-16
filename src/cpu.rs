use crate::{bus::Bus, opcodes};
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

#[derive(Clone, Debug)]
pub struct Status {
    pub negative: bool,
    pub overflow: bool,
    /// Not used in this instruction set. In reality this is pinned high (1) but for our purposes
    /// it's easier to leave it permanently false to maintain consistency with the other flags.
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
        let mut bin_rep = ["0"; 8];

        for (i, val) in self.as_array().iter().enumerate() {
            if *val {
                bin_rep[i] = "1";
            }
        }

        bin_rep.join("")
    }

    pub fn to_binary(&self) -> u8 {
        u8::from_str_radix(&self.to_binary_string(), 2).expect("couldn't parse Status to binary")
    }

    /// Takes a u8 integer and uses it to set the status flags bit by bit.
    pub fn from_binary(&mut self, new_flags: u8) {
        let binary_rep = format!("{:b}", new_flags);
        for (i, bit) in binary_rep.chars().map(|c| c.to_string()).enumerate() {
            match i {
                0 => self.negative = bit == "1",
                1 => self.overflow = bit == "1",
                2 => self.no_op = bit == "1",
                3 => self.break_cmd = bit == "1",
                4 => self.decimal = bit == "1",
                5 => self.interrupt_disable = bit == "1",
                6 => self.zero = bit == "1",
                7 => self.carry = bit == "1",
                _ => panic!("how did you get here"),
            }
        }
    }
}

// Note: The tutorial shows this approach, using the STACK_ADDR + cpu.stack_pointer to point at stack data rather than
// an explicit stack address. I'm wondering if this is a u8 solution thing.
const STACK_ADDR: u16 = 0x0100;
const STACK_RESET: u8 = 0xFD;

const PRG_ROM_START: u16 = 0x0600;

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

    /// ## Stack Pointer (SP)
    ///
    /// Used to hold the address of the top of the stack (memory addresses [0x0100 .. 0x1FF]).
    /// When a byte gets pushed to the stack the SP value decrements, and vice versa when bytes
    /// are retrieved from the stack.
    pub stack_pointer: u8,

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
    // memory: [u8; 0xFFFF],

    /// ## Bus
    ///
    /// Simulates the wiring connections between the CPU and the bus, connecting the CPU with the
    /// system memory and other components.
    bus: Bus,
}

pub trait Memory {
    fn mem_read(&self, addr: u16) -> u8;
    fn mem_write(&mut self, addr: u16, value: u8) -> ();

    /// Read 2 bytes at once fromt he memory array at the given address (index), accounting for
    /// the little endian encoding expected by the NES.
    ///
    /// e.g. $12_34 -> 34_12
    fn mem_read_u16(&mut self, addr: u16) -> u16 {
        // swap the positions of the most and least significant 8 bits.
        let low = self.mem_read(addr) as u16;
        let high = self.mem_read(addr + 1) as u16;
        high << 8 | low
    }

    /// Write 2 bytes at once from the memory array at the given address (index), accounting for
    /// the little endian encoding expected by the NES.
    ///
    /// e.g. writing 34_12 will store $1234
    fn mem_write_u16(&mut self, addr: u16, data: u16) {
        // swap the positions of the most and least significant 8 bits.
        let high = (data >> 8) as u8;
        let low = (data & 0xff) as u8;
        self.mem_write(addr, low);
        self.mem_write(addr + 1, high);
    }
}

impl Memory for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.bus.mem_read(addr)
    }

    fn mem_write(&mut self, addr: u16, value: u8) -> () {
        self.bus.mem_write(addr, value);
    }

    /// Read 2 bytes at once fromt he memory array at the given address (index), accounting for
    /// the little endian encoding expected by the NES.
    ///
    /// e.g. $12_34 -> $34_12
    fn mem_read_u16(&mut self, addr: u16) -> u16 {
        self.bus.mem_read_u16(addr)
    }

    /// Write 2 bytes at once from the memory array at the given address (index), accounting for
    /// the little endian encoding expected by the NES.
    ///
    /// e.g. writing 34_12 will store $1234
    fn mem_write_u16(&mut self, addr: u16, value: u16) {
        self.bus.mem_write_u16(addr, value);
    }
}

impl Default for CPU {
    fn default() -> Self {
        CPU::new()
    }
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            stack_pointer: STACK_RESET,
            status: Status::new(),
            program_counter: 0,
            bus: Bus::new(),
        }
    }

    pub fn debug_print(&self) {
        println!(
            "\
\tA:\t{:#04X}
\tX:\t{:#04X}
\tY:\t{:#04X}
\tStatus:\t{:#010b}
\tPC:\t{:#06X}",
            self.register_a,
            self.register_x,
            self.register_y,
            self.status.to_binary(),
            self.program_counter
        );
        println!("\tSTACK:");
        for addr in self.stack_pointer..(STACK_RESET) {
            let ptr = addr as u16 + STACK_ADDR;
            println!("\t\t${:04X}\t{:#04X}", ptr, self.mem_read(ptr));
        }
    }

    fn print_command(&self, cmd: &str) {
        println!("{}", cmd);
    }

    fn print_command_with_addr(&self, cmd: &str, addr: u16) {
        println!("{cmd} ${addr:04X}")
    }

    fn print_command_with_args(&self, cmd: &str, addr: u16, value: u8) {
        println!(
            "{} ${:04X} ({:#04X} = {:#010b} = {})",
            cmd, addr, value, value, value
        );
    }

    /// Uses the active addressing mode to determine the atual addresses to read.
    fn get_operand_address(&mut self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),

            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_x);
                addr.into()
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_y);
                addr.into()
            }

            AddressingMode::Absolute_X => {
                let pos = self.mem_read_u16(self.program_counter);
                pos.wrapping_add(self.register_x as u16)
            }
            AddressingMode::Absolute_Y => {
                let pos = self.mem_read_u16(self.program_counter);
                pos.wrapping_add(self.register_y as u16)
            }

            AddressingMode::Indirect_X => {
                // Find the value pointed at by the PC
                let base = self.mem_read(self.program_counter);
                // Add the value in X to use as a ptr to the actual address
                let ptr = base.wrapping_add(self.register_x);

                // Find the two bytes indicated by the ptr
                let low = self.mem_read(ptr as u16);
                let high = self.mem_read(ptr.wrapping_add(1) as u16);

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
                deref_base.wrapping_add(self.register_y as u16)
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    /// Loads a given program into PRG ROM
    pub fn load(&mut self, program: Vec<u8>) {
        // Note that PRG ROM starts at 0x8000, all previous bytes are reserved for other
        // system functions.
        // self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        // self.mem_write_u16(0xFFFC, 0x8000);
        // edited for SNAKE
        for i in 0..(program.len() as u16) {
            self.mem_write(0x0000 + i, program[i as usize]);
        }
        self.mem_write_u16(0xFFFC, 0x0000);
    }

    /// Simulates the console's behavior when a new cartridge is inserted.
    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    /// Handles the Reset Interrupt signal sent when a cartridge is loaded.
    /// This signal informs the CPU to reset the internal state and start the program_counter at
    /// a specific memory address pointed to by 0xFFFC (set via self.load).
    /// This also resets the stack pointer to the top of the stack at 0x1FF.
    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.status = Status::new();

        self.program_counter = self.mem_read_u16(0xFFFC);
        self.stack_pointer = STACK_RESET;
    }

    pub fn run(&mut self) {
        self.run_with_callback(|_| {});
    }

    /// Executes the program in PRG ROM.
    pub fn run_with_callback<F>(&mut self, mut callback: F)
    where
        F: FnMut(&mut CPU),
    {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;

        // Clock cycle loop
        loop {
            // Fetch the op code from the program at the counter.
            let code = self.mem_read(self.program_counter);
            // Increment to the next program step immediately after reading.
            self.program_counter += 1;

            // Track the current state of the PC to identify if it needs to be incremented after
            // the code is run.
            let pc_state = self.program_counter;

            let opcode = opcodes
                .get(&code)
                .unwrap_or_else(|| panic!("couldn't find code 0x{:X} in opcodes map", code));

            match opcode.instruction {
                "ADC" => self.adc(&opcode.addressing_mode),
                "AND" => self.and(&opcode.addressing_mode),
                "ASL" => self.asl(&opcode.addressing_mode),
                "ASL_A" => self.asl_a(),
                "BCC" => self.branch(!self.status.carry),
                "BCS" => self.branch(self.status.carry),
                "BEQ" => self.branch(self.status.zero),
                "BIT" => self.bit(&opcode.addressing_mode),
                "BMI" => self.branch(self.status.negative),
                "BNE" => self.branch(!self.status.zero),
                "BPL" => self.branch(!self.status.negative),
                "BRK" => {
                    self.print_command("BRK");
                    return;
                }
                "BVC" => self.branch(!self.status.overflow),
                "BVS" => self.branch(self.status.overflow),
                "CLC" => self.clc(),
                "CLD" => self.cld(),
                "CLI" => self.cli(),
                "CLV" => self.clv(),
                "CMP" => self.compare(&opcode.addressing_mode, self.register_a),
                "CPX" => self.compare(&opcode.addressing_mode, self.register_x),
                "CPY" => self.compare(&opcode.addressing_mode, self.register_y),
                "DEC" => self.dec(&opcode.addressing_mode),
                "DEX" => self.dex(),
                "DEY" => self.dey(),
                "EOR" => self.eor(&opcode.addressing_mode),
                "INC" => self.inc(&opcode.addressing_mode),
                "INX" => self.inx(),
                "INY" => self.iny(),
                "JMP" => self.jmp(&opcode.addressing_mode),
                "JMP_I" => self.jmp_i(),
                "JSR" => self.jsr(),
                "LDA" => self.lda(&opcode.addressing_mode),
                "LDX" => self.ldx(&opcode.addressing_mode),
                "LDY" => self.ldy(&opcode.addressing_mode),
                "LSR_A" => self.lsr_a(),
                "LSR" => self.lsr(&opcode.addressing_mode),
                "NOP" => self.nop(),
                "ORA" => self.ora(&opcode.addressing_mode),
                "PHA" => self.pha(),
                "PHP" => self.php(),
                "PLA" => self.pla(),
                "PLP" => self.plp(),
                "ROL_A" => self.rol_a(),
                "ROL" => self.rol(&opcode.addressing_mode),
                "ROR_A" => self.ror_a(),
                "ROR" => self.ror(&opcode.addressing_mode),
                "RTI" => self.rti(),
                "RTS" => self.rts(),
                "SBC" => self.sbc(&opcode.addressing_mode),
                "SEC" => self.sec(),
                "SED" => self.sed(),
                "SEI" => self.sei(),
                "STA" => self.sta(&opcode.addressing_mode),
                "STX" => self.stx(&opcode.addressing_mode),
                "STY" => self.sty(&opcode.addressing_mode),
                "TAX" => self.tax(),
                "TAY" => self.tay(),
                "TSX" => self.tsx(),
                "TXA" => self.txa(),
                "TXS" => self.txs(),
                "TYA" => self.tya(),
                _ => {
                    panic!("bad opcode found somehow")
                }
            }
            if self.program_counter == pc_state {
                self.program_counter += (opcode.byte_count - 1) as u16;
            }

            callback(self);
        }
    }

    /// `ADC` Adds a value from memory to the A register, stores in the A register.
    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("ADC", addr, value);
        self.add_to_register_a(value);
    }

    /// `AND` performs a bitwise AND between the A register and a memory value.
    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("AND", addr, value);

        self.register_a &= value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `ASL` performs a bitwise left shift of 1 on a value at an address, doubling it in place.
    fn asl(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut value = self.mem_read(addr);
        self.print_command_with_args("ASL", addr, value);

        // Set the carry flag if the initial value has the highest bit set
        self.set_carry_flag(value >> 7 == 1);

        value <<= 1;
        self.mem_write(addr, value);
        self.update_zero_and_negative_flags(value);
    }

    /// `ASL_A` performs a bitwise left shift of 1 directly on the A register, doubling it.
    fn asl_a(&mut self) {
        self.print_command("ASL A");
        // Set the carry flag if the initial value has the highest bit set
        self.set_carry_flag(self.register_a >> 7 == 1);

        self.register_a <<= 1;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `BIT` performs an AND between a value in memory and the A register then sets some flags
    /// accordingly. The result is not kept.
    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("BIT", addr, value);

        let result = value & self.register_a;

        self.status.zero = result == 0;
        self.status.negative = value & 0b1000_0000 > 0;
        self.status.overflow = value & 0b0100_0000 > 0;
    }

    /// `CLC` clears the carry flag
    fn clc(&mut self) {
        self.print_command("CLC");
        self.set_carry_flag(false);
    }

    /// `CLD` clears the decimal mode flag
    fn cld(&mut self) {
        self.print_command("CLD");
        self.set_decimal_mode(false);
    }

    /// `CLI` clears the interrupt disable flag
    fn cli(&mut self) {
        self.print_command("CLI");
        self.set_interrupt_disable(false);
    }

    /// `CLV` clears the overflow flag
    fn clv(&mut self) {
        self.print_command("CLV");
        self.set_overflow_flag(false);
    }

    /// The "compare" family of instructions compares a register with a memory value and sets some
    /// flags accordingly. The result is not kept.
    fn compare(&mut self, mode: &AddressingMode, target: u8) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("CMP", addr, value);

        self.set_carry_flag(target >= value);
        self.update_zero_and_negative_flags(target.wrapping_sub(value));
    }

    /// `DEC` decrements the value at a given memory address by 1 and sets some flags accordingly.
    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("DEC", addr, value);

        let result = value.wrapping_sub(1);

        self.mem_write(addr, result);
        self.update_zero_and_negative_flags(result);
    }

    /// `DEX` decrements the value in the X register and sets some flags accordingly.
    fn dex(&mut self) {
        self.print_command("DEX");

        self.register_x = self.register_x.wrapping_sub(1);

        self.update_zero_and_negative_flags(self.register_x);
    }

    /// `DEY` decrements the value in the Y register and sets some flags accordingly.
    fn dey(&mut self) {
        self.print_command("DEY");

        self.register_y = self.register_y.wrapping_sub(1);

        self.update_zero_and_negative_flags(self.register_y);
    }

    /// `EOR` performs a bitwise XOR between the A register and a memory value and sets some
    /// flags accordingly.
    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("EOR", addr, value);
        self.register_a ^= value;

        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `INC` increments the value at a given memory address by 1 and sets some flags accordingly.
    fn inc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("INC", addr, value);

        let result = value.wrapping_add(1);

        self.mem_write(addr, result);
        self.update_zero_and_negative_flags(result);
    }

    /// 0xE8 op code `INX`. Increments the value in the X register by 1.
    fn inx(&mut self) {
        self.print_command("INX");
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    /// 0xC8 op code `INY`. Increments the value in the Y register by 1.
    fn iny(&mut self) {
        self.print_command("INY");
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    /// `JMP` jumps to a specific 16 bit memory address
    fn jmp(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.print_command_with_addr("JMP", addr);

        self.program_counter = addr;
    }

    /// `JMP_I` provides a unique "Indirect" address mode not supported by our AddressingMode
    /// system.
    /// Note: there is a bug with the 6502 chip in this mode in cases where the address falls on
    /// a page boundary (i.e. $xxFF) The LSB will be correctly read from $xxFF, but the MSB will
    /// be read from $xx00.
    /// ## Example:
    /// Given the following memory state:
    /// addr  | value
    /// ------|------
    /// $3000 | $10
    /// ...
    /// $30FF | $20
    /// $3100 | $30
    /// you would expect the command `JMP $30FF` to jump to $3020, but it will actually jump to
    /// $1020 because of this page boundary bug.
    fn jmp_i(&mut self) {
        let addr = self.mem_read_u16(self.program_counter);

        // If not for the bug described above, indirect_ref could be self.mem_read_u16(addr).
        // Instead we need to do some little endian encoding work to find the bugged location.
        let indirect_ref = if addr & 0x00FF == 0x00FF {
            let low = self.mem_read(addr);
            let high = self.mem_read(addr & 0xFF00);
            (high as u16) << 8 | (low as u16)
        } else {
            self.mem_read_u16(addr)
        };
        self.print_command_with_addr("JMP I", addr);

        self.program_counter = indirect_ref;
    }

    /// `JSR` Pushes the return point onto the stack and then updates the PC to the target address.
    fn jsr(&mut self) {
        let addr = self.program_counter + 1;
        self.print_command_with_addr("JSR", addr);
        self.write_to_stack_u16(addr);
        let target_addr = self.mem_read_u16(self.program_counter);
        self.program_counter = target_addr;
    }

    /// `LDA`. Loads a value into the A register.
    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("LDA", addr, value);

        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `LDX` Loads a value into the X register.
    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("LDX", addr, value);

        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    /// `LDY` Loads a value into the Y register.
    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("LDY", addr, value);

        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    /// `LSR_A` performs a bitwise right shift of the value in the A register, halving it in place.
    fn lsr_a(&mut self) {
        self.print_command("LSR A");

        // Set the carry flag if the initial value has the 0 bit set.
        self.set_carry_flag(self.register_a & 1 == 1);

        self.register_a >>= 1;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `LSR` performs a bitwise right shift of 1 on a value at an address, doubling it in place.
    fn lsr(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut value = self.mem_read(addr);
        self.print_command_with_args("LSR", addr, value);

        // Set the carry flag if the initial value has the highest bit set
        self.set_carry_flag(value & 1 == 1);

        value >>= 1;
        self.mem_write(addr, value);
        self.update_zero_and_negative_flags(value);
    }

    /// `NOP` does nothing but increment the program counter, which is already handled by the
    /// clock cycle loop.
    fn nop(&mut self) {
        self.print_command("NOP");
    }

    /// `ORA` does a logical OR (inclusive) between the A register and a byte from memory.
    fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("LSR", addr, value);

        self.register_a |= value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `PHA` pushes the current value of the A register to the stack
    fn pha(&mut self) {
        self.print_command("PHA");
        self.write_to_stack(self.register_a);
    }

    /// `PHP` pushes the current value of the status flags to the stack
    fn php(&mut self) {
        self.print_command("PHP");
        let mut flags = self.status.clone();
        flags.break_cmd = true;
        flags.no_op = true;

        self.write_to_stack(flags.to_binary());
    }

    /// `PLA` pulls the current value of the stack at the stack pointer to the A register.
    fn pla(&mut self) {
        self.print_command("PLA");
        self.register_a = self.read_from_stack();
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `PLP` pulls the current value of the stack and uses it to set the status flags.
    fn plp(&mut self) {
        self.print_command("PLP");
        let new_flags = self.read_from_stack();
        self.status.from_binary(new_flags);
        self.status.break_cmd = false;
        self.status.no_op = true;
    }

    /// `ROL_A` rotates all of the bits in the accumulator one to the left, using the carry flag
    /// to handle the edges.
    fn rol_a(&mut self) {
        self.print_command("ROL A");
        // Store the 7th bit of the current value for use in the carry flag.
        let new_carry = (self.register_a >> 7) & 1 == 1;
        let mut rolled_val = self.register_a;
        rolled_val <<= 1;
        // Update the 0th bit of the rolled_val based on the original value of the carry flag.
        if self.status.carry {
            rolled_val |= 1;
        } else {
            rolled_val &= !1;
        }

        self.set_carry_flag(new_carry);
        self.register_a = rolled_val;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `ROL` rotates all of the bits at a memory address one to the left, using the carry flag
    /// to handle the edges.
    fn rol(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("ROL", addr, value);

        let new_carry = (value >> 7) & 1 == 1;
        let mut rolled_val = value;
        rolled_val <<= 1;
        // Update the 0th bit of the rolled_val based on the original value of the carry flag.
        if self.status.carry {
            rolled_val |= 1;
        } else {
            rolled_val &= !1;
        }

        self.set_carry_flag(new_carry);
        self.mem_write(addr, rolled_val);
        self.update_zero_and_negative_flags(rolled_val);
    }

    /// `ROR_A` rotates all of the bits in the accumulator one to the right, using the carry flag
    /// to handle the edges.
    fn ror_a(&mut self) {
        self.print_command("ROR A");

        // store the 0th bit of the current value for use in the carry flag.
        let new_carry = self.register_a & 1 == 1;
        let mut rolled_val = self.register_a;
        rolled_val >>= 1;
        println!("rolled_val {:#010b}", rolled_val);
        // Update the 7th bit of the rolled_val based on the original value of the carry flag.
        if self.status.carry {
            rolled_val |= 0b1000_0000;
        } else {
            let mask: u8 = !(1 << 7);
            rolled_val &= mask;
        }

        self.set_carry_flag(new_carry);
        self.register_a = rolled_val;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `ROR` rotates all of the bits at a memory address one to the right, using the carry flag
    /// to handle the edges.
    fn ror(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("ROR", addr, value);

        // store the 0th bit of the current value for use in the carry flag.
        let new_carry = value & 1 == 1;
        let mut rolled_val = value;
        rolled_val >>= 1;
        // Update the 7th bit of the rolled_val based on the original value of the carry flag.
        if self.status.carry {
            rolled_val |= 0b1000_0000;
        } else {
            let mask: u8 = !(1 << 7);
            rolled_val &= mask;
        }

        self.set_carry_flag(new_carry);
        self.mem_write(addr, rolled_val);
        self.update_zero_and_negative_flags(rolled_val);
    }

    /// `RTI` returns at the end of an interrupt routine, pulling the status flags from the stack
    /// then the PC.
    fn rti(&mut self) {
        self.print_command("RTI");
        let new_flags = self.read_from_stack();
        self.status.from_binary(new_flags);
        // This command does some extra work to explicitly set the otherwise-unused no_op or BREAK2 flag
        self.status.break_cmd = false;
        self.status.no_op = true;
        self.program_counter = self.read_from_stack_u16();
    }

    /// `RTS` returns to the calling routine at the end of a subroutine and pulls the PC - 1 from
    /// the stack.
    fn rts(&mut self) {
        self.program_counter = self.read_from_stack_u16() + 1;
        self.print_command_with_addr("RTS", self.program_counter);
    }

    /// `SBC` Subtracts a value from memory from the A register, stores in the A register.
    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.print_command_with_args("SBC", addr, value);
        self.add_to_register_a(((value as i8).wrapping_neg().wrapping_sub(1)) as u8);
    }

    /// `SEC` sets the carry flag to 1.
    fn sec(&mut self) {
        self.print_command("SEC");
        self.status.carry = true;
    }

    /// `SED` sets the Decimal Mode flag to 1.
    fn sed(&mut self) {
        self.print_command("SED");
        self.status.decimal = true;
    }

    /// `SEI` sets the Interrupt Disable flag to 1.
    fn sei(&mut self) {
        self.print_command("SEI");
        self.status.interrupt_disable = true;
    }

    /// `STA` copies a value from the A register into memory.
    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.print_command_with_addr("STA", addr);

        self.mem_write(addr, self.register_a);
    }

    /// `STX` copies a value from the X register into memory.
    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.print_command_with_addr("STX", addr);

        self.mem_write(addr, self.register_x);
    }

    /// `STY` copies a value from the Y register into memory.
    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.print_command_with_addr("STY", addr);

        self.mem_write(addr, self.register_y);
    }

    /// Opcode `TAX` copies a value from register A to register X.
    fn tax(&mut self) {
        self.print_command("TAX");
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    /// Opcode `TAY` copies a value from register A to register Y.
    fn tay(&mut self) {
        self.print_command("TAY");
        self.register_y = self.register_a;
        self.update_zero_and_negative_flags(self.register_y);
    }

    /// `TSX` copies the stack contents into register X
    fn tsx(&mut self) {
        self.print_command("TSX");
        let stack_contents = self.read_from_stack();
        self.register_x = stack_contents;
        self.update_zero_and_negative_flags(self.register_x);
    }

    /// `TXA` copies the contents of the X register into the A register
    fn txa(&mut self) {
        self.print_command("TXA");
        self.register_a = self.register_x;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// `TXS` copies the contents fo the X register into the Stack
    fn txs(&mut self) {
        self.print_command("TXS");
        self.stack_pointer = self.register_x;
    }

    /// `TYA` copies the contents of the Y register into the A register
    fn tya(&mut self) {
        self.print_command("TYA");
        self.register_a = self.register_y;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn add_to_register_a(&mut self, data: u8) {
        let sum = self.register_a as u16
            + data as u16
            + (match self.status.carry {
                true => 1,
                false => 0,
            }) as u16;

        let carry = sum > 0xff;
        self.set_carry_flag(carry);

        let result = sum as u8;

        self.set_overflow_flag((data ^ result) & (result ^ self.register_a) & 0x80 != 0);

        self.register_a = result;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// Used by all of the branching logic instructions to jump the PC by a given offset
    fn branch(&mut self, condition: bool) {
        self.print_command("BRANCH");
        if condition {
            let offset = self.mem_read(self.program_counter) as i8;
            let jump_addr = self
                .program_counter
                .wrapping_add(1) // Step forward one now that we've read the offset
                .wrapping_add(offset as u16); // Jump up (or down!) by the provided offset

            self.program_counter = jump_addr;
        }
    }

    fn set_carry_flag(&mut self, should_set: bool) {
        self.status.carry = should_set;
    }

    fn set_decimal_mode(&mut self, should_set: bool) {
        self.status.decimal = should_set;
    }

    fn set_interrupt_disable(&mut self, should_set: bool) {
        self.status.interrupt_disable = should_set;
    }

    fn set_overflow_flag(&mut self, should_set: bool) {
        self.status.overflow = should_set;
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        // set or clear the [Z]ero flag.
        self.status.zero = result == 0;

        // set or clear the [N]egative flag.
        self.status.negative = result & 0b1000_0000 != 0;
    }

    fn read_from_stack(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read(STACK_ADDR + self.stack_pointer as u16)
    }

    fn read_from_stack_u16(&mut self) -> u16 {
        let low = self.read_from_stack() as u16;
        let high = self.read_from_stack() as u16;

        high << 8 | low
    }

    fn write_to_stack(&mut self, value: u8) {
        self.mem_write(STACK_ADDR + self.stack_pointer as u16, value);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    fn write_to_stack_u16(&mut self, value: u16) {
        let high = (value >> 8) as u8;
        let low = (value & 0xff) as u8;
        self.write_to_stack(high);
        self.write_to_stack(low);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_status_to_binary_string_works_with_defaults() {
        let status = Status::new();
        assert_eq!(status.to_binary_string(), "00000000");
    }

    #[test]
    fn test_status_to_binary_works_with_defaults() {
        let status = Status::new();
        assert_eq!(status.to_binary(), 0b0000_0000);
    }

    #[test]
    fn test_status_works_with_non_default_values() {
        let mut status = Status::new();
        status.negative = true;
        status.carry = true;
        status.zero = true;

        assert_eq!(status.to_binary_string(), "10000011");
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
    fn test_iny_handles_zero() {
        let mut cpu = CPU::new();
        // LDA #$0xFF
        // TAY
        // INY
        // BRK
        let program = vec![0xA9, 0xFF, 0xA8, 0xC8, 0x00];

        cpu.load_and_run(program);
        assert_eq!(cpu.register_y, 0, "the value in Y should rollover to 0");
        assert!(cpu.status.zero, "Zero flag should be set");
    }

    #[test]
    fn test_iny_overflow() {
        let mut cpu = CPU::new();
        // LDA #$0xFF
        // TAX
        // INY
        // INY
        // BRK
        let program = vec![0xA9, 0xFF, 0xA8, 0xC8, 0xC8, 0x00];

        cpu.load_and_run(program);
        assert_eq!(
            cpu.register_y, 1,
            "the value in Y should rollover to 0 and start counting up again"
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

    #[test]
    fn test_and_immediate() {
        let mut cpu = CPU::new();
        cpu.register_a = 0b1010;
        // LDA 0b1010
        // AND 0b1001
        // BRK
        let program = vec![0xA9, 0b1010, 0x29, 0b1001, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0b1000, "A should AND to 0b1000");
    }

    #[test]
    fn test_and_from_memory() {
        let mut cpu = CPU::new();
        cpu.register_a = 0b1010;
        // LDA 0b1001
        // STA 0x10
        // LDA 0b1010
        // AND 0x10
        // BRK
        let program = vec![0xA9, 0b1001, 0x85, 0x10, 0xA9, 0b1010, 0x2D, 0x10, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0b1000, "AND should read from 0x10");
    }

    #[test]
    fn test_and_handles_zero() {
        let mut cpu = CPU::new();
        // LDA 0b0110
        // AND 0b1001
        // BRK
        let program = vec![0xA9, 0b0110, 0x29, 0b1001, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0b0000, "A should AND to 0s");
        assert!(cpu.status.zero, "Zero flag should be set");
    }

    #[test]
    fn test_asl_from_memory_doubles() {
        let mut cpu = CPU::new();
        // LDA #10
        // STA 0x10
        // ASL 0x10
        // BRK
        let program = vec![0xA9, 10, 0x85, 0x10, 0x0E, 0x10, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.mem_read(0x10),
            20,
            "ALS should double the value at the address"
        );
    }

    #[test]
    fn test_lsr_from_memory_halves() {
        let mut cpu = CPU::new();
        // LDA #10
        // STA 0x10
        // LSR 0x10
        // BRK
        let program = vec![0xA9, 10, 0x85, 0x10, 0x46, 0x10, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.mem_read(0x10),
            5,
            "LSR should halve the value at the address"
        );
    }

    #[test]
    fn test_lsr_a_halves() {
        let mut cpu = CPU::new();
        // LDA #10
        // LSR_A
        // BRK
        let program = vec![0xA9, 10, 0x4A, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 5,
            "LSR_A should halve the value in the A_register"
        );
    }

    #[test]
    fn test_branch_updates_pc_when_true_positive() {
        let mut cpu = CPU::new();
        cpu.program_counter = 10;
        cpu.mem_write(10, 5);
        cpu.branch(true);

        assert_eq!(
            cpu.program_counter, 16,
            "PC should be updated by 1 (read) then 5 (content of memory at original PC)"
        )
    }

    #[test]
    fn test_branch_noops_when_false() {
        let mut cpu = CPU::new();
        cpu.program_counter = 10;
        cpu.mem_write(10, 5);
        cpu.branch(false);

        assert_eq!(cpu.program_counter, 10, "PC counter should be unchanged")
    }

    #[test]
    fn test_branch_updates_pc_when_true_negative() {
        let mut cpu = CPU::new();
        cpu.program_counter = 10;
        cpu.mem_write(10, 0b1111_1011);
        // cpu.bus.cpu_vram[10] = 0b1111_1011; // -5 via 2s complement
        cpu.branch(true);

        assert_eq!(
            cpu.program_counter, 6,
            "PC should be updated by 1 (read) then -5 (content of memory at original PC)"
        );
    }

    #[test]
    fn test_bit_sets_flags_from_memory() {
        let mut cpu = CPU::new();
        // LDA 0b1100_0000
        // STA 0x10
        // LDA 0b0011_1111
        // BIT 0x10
        // BRK
        let program = vec![
            0xA9,
            0b1100_0000,
            0x85,
            0x10,
            0xA9,
            0b0011_1111,
            0x24,
            0x10,
            0x00,
        ];

        cpu.load_and_run(program);

        assert!(
            cpu.status.overflow,
            "the overflow bit should be set by Bit 6 of the memory"
        );
        assert!(
            cpu.status.negative,
            "the negative bit should be set by Bit 7 of the memory"
        );
        assert!(
            cpu.status.zero,
            "the zero bit should be set by the result of the AND"
        );
    }

    #[test]
    fn test_dec_from_memory() {
        let mut cpu = CPU::new();
        // LDA 100
        // STA 0x10
        // DEC 0x10
        let program = vec![0xA9, 100, 0x85, 0x10, 0xC6, 0x10];
        cpu.load_and_run(program);

        assert_eq!(cpu.mem_read(0x10), 99);
    }

    #[test]
    fn test_dex() {
        let mut cpu = CPU::new();
        // LDA 100
        // TAX
        // DEX
        let program = vec![0xA9, 100, 0xAA, 0xCA];
        cpu.load_and_run(program);

        assert_eq!(cpu.register_x, 99);
    }

    #[test]
    fn test_dey() {
        let mut cpu = CPU::new();
        // LDA 100
        // TAY
        // DEY
        let program = vec![0xA9, 100, 0xA8, 0x88];
        cpu.load_and_run(program);

        assert_eq!(cpu.register_y, 99);
    }

    #[test]
    fn test_eor_immediate() {
        let mut cpu = CPU::new();
        cpu.register_a = 0b1010;
        // LDA 0b1010
        // EOR 0b1001
        // BRK
        let program = vec![0xA9, 0b1010, 0x49, 0b1001, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0b0011, "A should AND to 0b1011");
    }

    #[test]
    fn test_eor_from_memory() {
        let mut cpu = CPU::new();
        cpu.register_a = 0b1010;
        // LDA 0b1001
        // STA 0x10
        // LDA 0b1010
        // EOR 0x10
        // BRK
        let program = vec![0xA9, 0b1001, 0x85, 0x10, 0xA9, 0b1010, 0x4D, 0x10, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0b0011, "AND should read from 0x10");
    }

    #[test]
    fn test_eor_handles_zero() {
        let mut cpu = CPU::new();
        // LDA 0b0110
        // AND 0b0110
        // BRK
        let program = vec![0xA9, 0b0110, 0x49, 0b0110, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0b0000, "A should AND to 0s");
        assert!(cpu.status.zero, "Zero flag should be set");
    }

    #[test]
    fn test_nop_increments_counter() {
        let mut cpu = CPU::new();

        // set an initial value for the PC by loading an empty program and resetting the state
        cpu.load(Vec::new());
        cpu.reset();
        let initial_pc = cpu.program_counter;

        // NOP
        // BRK
        let program = vec![0xEA, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.program_counter,
            initial_pc + 2,
            "The PC should be incremented by 1 (to read NOP) and then another (to move on to the next instruction)"
        );
    }

    #[test]
    fn test_ora_immediate() {
        let mut cpu = CPU::new();
        cpu.register_a = 0b1010;
        // LDA 0b1010
        // ORA 0b1001
        // BRK
        let program = vec![0xA9, 0b1010, 0x09, 0b1001, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0b1011, "A should OR to 0b1011");
    }

    #[test]
    fn test_ora_from_memory() {
        let mut cpu = CPU::new();
        cpu.register_a = 0b1010;
        // LDA 0b1001
        // STA 0x10
        // LDA 0b1010
        // ORA 0x10
        // BRK
        let program = vec![0xA9, 0b1001, 0x85, 0x10, 0xA9, 0b1010, 0x0D, 0x10, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0b1011, "OR should read from 0x10");
    }

    #[test]
    fn test_ora_handles_zero() {
        let mut cpu = CPU::new();
        // LDA 0b0000
        // AND 0b0000
        // BRK
        let program = vec![0xA9, 0b0000, 0x29, 0b0000, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.register_a, 0b0000, "A should OR to 0s");
        assert!(cpu.status.zero, "Zero flag should be set");
    }

    #[test]
    fn test_pha_pushes_a_to_stack() {
        let mut cpu = CPU::new();
        // LDA 0b1111_1111
        // PHA
        // BRK
        let program = vec![0xA9, 0b1111_1111, 0x48, 0x00];

        cpu.load_and_run(program);

        let stack_val = cpu.read_from_stack();

        assert_eq!(
            stack_val, 0b1111_1111,
            "the value of the stack should be loaded from the A register"
        );
    }

    #[test]
    fn test_rol_a_rolls_left() {
        let mut cpu = CPU::new();
        // LDA 0b1010_0101
        // ROL A
        // BRK
        let program = vec![0xA9, 0b1010_0101, 0x2A, 0x00];
        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 0b0100_1010,
            "A register should be bit shifted one left"
        );
        assert!(
            cpu.status.carry,
            "carry status should receive the 1 from the 7th bit, pre shift"
        )
    }

    #[test]
    fn test_rol_a_rolls_left_reads_initial_carry() {
        let mut cpu = CPU::new();
        // LDA 0b0010_0101
        // SEC
        // ROL A
        // BRK
        let program = vec![0xA9, 0b0010_0101, 0x38, 0x2A, 0x00];
        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 0b0100_1011,
            "A register should be bit shifted one left, and read the LSB from carry"
        );
        assert!(
            !cpu.status.carry,
            "carry status should receive the 1 from the 7th bit, pre shift"
        )
    }

    #[test]
    fn test_rol_rolls_left_from_memory() {
        let mut cpu = CPU::new();
        // LDA 0b1010_0101
        // STA 0x10
        // ROL 0x10
        // BRK
        let program = vec![0xA9, 0b1010_0101, 0x85, 0x10, 0x2E, 0x10, 0x00];
        cpu.load_and_run(program);

        assert_eq!(
            cpu.mem_read(0x10),
            0b0100_1010,
            "memory value should be bit shifted one left"
        );
        assert!(
            cpu.status.carry,
            "carry status should receive the 1 from the 7th bit, pre shift"
        )
    }

    #[test]
    fn test_ror_a_rolls_right() {
        let mut cpu = CPU::new();
        // LDA 0b1010_0101
        // ROR A
        // BRK
        let program = vec![0xA9, 0b1010_0101, 0x6A, 0x00];
        cpu.load_and_run(program);

        println!("A: {:#010b}", cpu.register_a);

        assert_eq!(
            cpu.register_a, 0b0101_0010,
            "A register should be bit shifted one right"
        );
        assert!(
            cpu.status.carry,
            "carry status should receive the 1 from the 0th bit, pre shift"
        )
    }

    #[test]
    fn test_ror_a_rolls_right_and_reads_from_carry() {
        let mut cpu = CPU::new();
        // LDA 0b1010_0100
        // SEC
        // ROR A
        // BRK
        let program = vec![0xA9, 0b1010_0100, 0x38, 0x6A, 0x00];
        cpu.load_and_run(program);

        println!("A: {:#010b}", cpu.register_a);

        assert_eq!(
            cpu.register_a, 0b1101_0010,
            "A register should be bit shifted one right"
        );
        assert!(
            !cpu.status.carry,
            "carry status should receive the 0 from the 0th bit, pre shift"
        )
    }

    #[test]
    fn test_ror_rolls_right_from_memory() {
        let mut cpu = CPU::new();
        // LDA 0b1010_0101
        // STA 0x10
        // ROR 0x10
        // BRK
        let program = vec![0xA9, 0b1010_0101, 0x85, 0x10, 0x66, 0x10, 0x00];
        cpu.load_and_run(program);

        assert_eq!(
            cpu.mem_read(0x10),
            0b0101_0010,
            "memory value should be bit shifted one right"
        );
        assert!(
            cpu.status.carry,
            "carry status should receive the 1 from the 0th bit, pre shift"
        )
    }

    #[test]
    fn test_sbc_subs_data_immediate_with_carry_set() {
        let mut cpu = CPU::new();
        // SEC
        // LDA #$05
        // SUB #$04
        // BRK
        let program = vec![0x38, 0xA9, 0x05, 0xE9, 0x04, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 0x01,
            "The A register should hold the difference between the given value and A"
        );
        assert!(!cpu.status.negative);
    }

    #[test]
    fn test_sbc_subs_data_immediate_with_carry_set_supports_negative() {
        let mut cpu = CPU::new();
        // SEC
        // LDA #$04
        // SUB #$05
        // BRK
        let program = vec![0x38, 0xA9, 0x04, 0xE9, 0x05, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 0xFF,
            "The A register should hold the difference between the given value and A"
        );
        assert!(
            cpu.status.negative,
            "The negative flag should be set for results < 0"
        );
    }

    #[test]
    fn test_sbc_subs_data_immediate_without_carry_set() {
        let mut cpu = CPU::new();
        // LDA #$06
        // SUB #$04
        // BRK
        let program = vec![0xA9, 0x06, 0xE9, 0x04, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 0x01,
            "The A register should hold the difference between a given value and A and 1 (for the empty carry set"
        );
        assert!(!cpu.status.negative);
    }

    #[test]
    fn test_sbc_immediate_handles_zero() {
        let mut cpu = CPU::new();
        // SEC
        // LDA #$05
        // SUB #$05
        // BRK
        let program = vec![0x38, 0xA9, 0x05, 0xE9, 0x05, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 0x00,
            "The A register should hold the difference between the given value and A"
        );
        assert!(!cpu.status.negative);
        assert!(cpu.status.zero);
    }

    #[test]
    fn test_sbc_adds_data_from_memory() {
        let mut cpu = CPU::new();
        // SEC
        // LDA #$04
        // STA $10
        // LDA #$05
        // SUB $10
        // BRK
        let program = vec![0x38, 0xA9, 0x04, 0x85, 0x10, 0xA9, 0x05, 0xE5, 0x10, 0x00];

        cpu.load_and_run(program);

        assert_eq!(
            cpu.register_a, 0x01,
            "The A register should hold the difference between the value at the addr and A"
        );
        assert!(!cpu.status.negative);
    }

    #[test]
    fn test_sec_sets_carry() {
        let mut cpu = CPU::new();
        // SEC
        // BRK
        let program = vec![0x38, 0x00];
        cpu.load_and_run(program);

        assert!(cpu.status.carry);
    }

    #[test]
    fn test_clc_clears_carry() {
        let mut cpu = CPU::new();
        // SEC
        // CLC
        // BRK
        let program = vec![0x38, 0x18, 0x00];
        cpu.load_and_run(program);

        assert!(!cpu.status.carry);
    }

    #[test]
    fn test_sed_sets_decimal() {
        let mut cpu = CPU::new();
        // SED
        // BRK
        let program = vec![0xF8, 0x00];
        cpu.load_and_run(program);

        assert!(cpu.status.decimal);
    }

    #[test]
    fn test_cld_clears_decimal() {
        let mut cpu = CPU::new();
        // SEC
        // CLC
        // BRK
        let program = vec![0xF8, 0xD8, 0x00];
        cpu.load_and_run(program);

        assert!(!cpu.status.decimal);
    }

    #[test]
    fn test_sei_sets_interrupt() {
        let mut cpu = CPU::new();
        // SEI
        // BRK
        let program = vec![0x78, 0x00];
        cpu.load_and_run(program);

        assert!(cpu.status.interrupt_disable);
    }

    #[test]
    fn test_cli_clears_interrupt() {
        let mut cpu = CPU::new();
        // SEI
        // CLI
        // BRK
        let program = vec![0x78, 0x58, 0x00];
        cpu.load_and_run(program);

        assert!(!cpu.status.interrupt_disable);
    }

    #[test]
    fn test_stx_loads_data() {
        let mut cpu = CPU::new();
        // LDA 0xFF
        // TAX
        // STX 0x10
        // BRK
        let program = vec![0xA9, 0xFF, 0xAA, 0x86, 0x10, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.mem_read(0x10), 0xFF);
    }

    #[test]
    fn test_sty_loads_data() {
        let mut cpu = CPU::new();
        // LDA 0xFF
        // TAY
        // STY 0x10
        // BRK
        let program = vec![0xA9, 0xFF, 0xA8, 0x84, 0x10, 0x00];

        cpu.load_and_run(program);

        assert_eq!(cpu.mem_read(0x10), 0xFF);
    }
}
