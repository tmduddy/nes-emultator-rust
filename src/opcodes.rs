use crate::cpu::AddressingMode;
use std::collections::HashMap;

#[derive(Debug)]
pub struct OpCode {
    pub opcode: u8,
    pub instruction: &'static str,
    pub byte_count: u8,
    pub cycle_count: u8,
    pub addressing_mode: AddressingMode,
}

impl OpCode {
    pub fn new(
        opcode: u8,
        instruction: &'static str,
        byte_count: u8,
        cycle_count: u8,
        addressing_mode: AddressingMode,
    ) -> OpCode {
        OpCode {
            opcode,
            instruction,
            byte_count,
            cycle_count,
            addressing_mode,
        }
    }
}

lazy_static! {
    pub static ref CPU_OPS_CODES: Vec<OpCode> = vec![
        // ADC (Add with Carry)
        OpCode::new(0x69, "ADC", 2, 2, AddressingMode::Immediate),
        OpCode::new(0x65, "ADC", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x75, "ADC", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x6d, "ADC", 3, 4, AddressingMode::Absolute),
        OpCode::new(0x7d, "ADC", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0x79, "ADC", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0x61, "ADC", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x71, "ADC", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        // AND (Logical AND)
        OpCode::new(0x29, "AND", 2, 2, AddressingMode::Immediate),
        OpCode::new(0x25, "AND", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x35, "AND", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x2d, "AND", 3, 4, AddressingMode::Absolute),
        OpCode::new(0x3d, "AND", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0x39, "AND", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0x21, "AND", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x31, "AND", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        // ASL (Arithmetic Shift Left)
        OpCode::new(0x06, "ASL", 2, 5, AddressingMode::ZeroPage),
        OpCode::new(0x16, "ASL", 2, 6, AddressingMode::ZeroPage_X),
        OpCode::new(0x0e, "ASL", 3, 6, AddressingMode::Absolute),
        OpCode::new(0x1e, "ASL", 3, 7, AddressingMode::Absolute_X),

        // ASL_A (Arithmetic Shift Left [Accumulator Addressing Mode])
        OpCode::new(0x0a, "ASL_A", 1, 2, AddressingMode::ZeroPage),

        // BCC (Branch if Carry Clear)
        OpCode::new(0x90, "BCC", 2, 2/*+1 if branch succeeds +2 if to new page*/, AddressingMode::NoneAddressing),

        // BCS (Branch if Carry Set)
        OpCode::new(0xB0, "BCS", 2, 2/*+1 if branch succeeds +2 if to new page*/, AddressingMode::NoneAddressing),
        
        // BEQ (Branch if Equal)
        OpCode::new(0xF0, "BEQ", 2, 2/*+1 if branch succeeds +2 if to new page*/, AddressingMode::NoneAddressing),

        // BIT (Bit Test)
        OpCode::new(0x24, "BIT", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x2C, "BIT", 3, 4, AddressingMode::Absolute),

        // BMI (Branch if Minus)
        OpCode::new(0x30, "BMI", 2, 2/*+1 if branch succeeds +2 if to new page*/, AddressingMode::NoneAddressing),
       
        // BNE (Branch if Not Equal)
        OpCode::new(0xD0, "BNE", 2, 2/*+1 if branch succeeds +2 if to new page*/, AddressingMode::NoneAddressing),
       
        // BPL (Branch if Positive)
        OpCode::new(0x10, "BPL", 2, 2/*+1 if branch succeeds +2 if to new page*/, AddressingMode::NoneAddressing),
       
        // BRK
        OpCode::new(0x00, "BRK", 1, 7, AddressingMode::NoneAddressing),

        // BVC (Branch if Overflow Clear)
        OpCode::new(0x50, "BVC", 2, 2/*+1 if branch succeeds +2 if to new page*/, AddressingMode::NoneAddressing),

        // BVS (Branch if Overflow Set)
        OpCode::new(0x70, "BVS", 2, 2/*+1 if branch succeeds +2 if to new page*/, AddressingMode::NoneAddressing),

        //CLC (Clear Carry Flag)
        OpCode::new(0x18, "CLC", 1, 2, AddressingMode::NoneAddressing),

        //CLD (Clear Decimal Mode)
        OpCode::new(0xD8, "CLD", 1, 2, AddressingMode::NoneAddressing),

        //CLI (Clear Interrupt Disable)
        OpCode::new(0x58, "CLI", 1, 2, AddressingMode::NoneAddressing),

        //CLV (Clear Overflow Flag)
        OpCode::new(0xB8, "CLV", 1, 2, AddressingMode::NoneAddressing),
        
        // CMP (Compare)
        OpCode::new(0xC9, "CMP", 2, 2, AddressingMode::Immediate),
        OpCode::new(0xC5, "CMP", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xD5, "CMP", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0xCd, "CMP", 3, 4, AddressingMode::Absolute),
        OpCode::new(0xDd, "CMP", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0xD9, "CMP", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0xC1, "CMP", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0xD1, "CMP", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        // CPX (Compare with X Register)
        OpCode::new(0xE0, "CPX", 2, 2, AddressingMode::Immediate),
        OpCode::new(0xE4, "CPX", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xEC, "CPX", 3, 4, AddressingMode::Absolute),
        
        // CPY (Compare with Y Register)
        OpCode::new(0xC0, "CPY", 2, 2, AddressingMode::Immediate),
        OpCode::new(0xC4, "CPY", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xCC, "CPY", 3, 4, AddressingMode::Absolute),

        // DEC (Decrement Memory) 
        OpCode::new(0xC6, "DEC", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xD6, "DEC", 2, 3, AddressingMode::ZeroPage_X),
        OpCode::new(0xCE, "DEC", 3, 4, AddressingMode::Absolute),
        OpCode::new(0xDE, "DEC", 3, 4, AddressingMode::Absolute_X),

        // DEX (Decrement X)
        OpCode::new(0xCA, "DEX", 1, 2, AddressingMode::NoneAddressing),

        // DEY (Decrement Y)
        OpCode::new(0x88, "DEY", 1, 2, AddressingMode::NoneAddressing),

        // TAX
        OpCode::new(0xaa, "TAX", 1, 2, AddressingMode::NoneAddressing),
        
        // TAY
        OpCode::new(0xA8, "TAY", 1, 2, AddressingMode::NoneAddressing),

        //INX
        OpCode::new(0xe8, "INX", 1, 2, AddressingMode::NoneAddressing),

        // LDA
        OpCode::new(0xa9, "LDA", 2, 2, AddressingMode::Immediate),
        OpCode::new(0xa5, "LDA", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xb5, "LDA", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0xad, "LDA", 3, 4, AddressingMode::Absolute),
        OpCode::new(0xbd, "LDA", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0xb9, "LDA", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0xa1, "LDA", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0xb1, "LDA", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        // STA
        OpCode::new(0x85, "STA", 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x95, "STA", 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x8d, "STA", 3, 4, AddressingMode::Absolute),
        OpCode::new(0x9d, "STA", 3, 5, AddressingMode::Absolute_X),
        OpCode::new(0x99, "STA", 3, 5, AddressingMode::Absolute_Y),
        OpCode::new(0x81, "STA", 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x91, "STA", 2, 6, AddressingMode::Indirect_Y),
    ];
    pub static ref OPCODES_MAP: HashMap<u8, &'static OpCode> = {
        let mut map = HashMap::new();
        for opcode in &*CPU_OPS_CODES {
            map.insert(opcode.opcode, opcode);
        }
        map
    };
}
