use crate::cpu::AddressingMode;
use std::collections::HashMap;
use lazy_static::lazy_static;


pub struct OpCode {
    pub code: u8,
    pub mnemonic: &'static str,
    pub len: u8,
    pub cycles: u8,
    pub mode: AddressingMode,
}

impl OpCode {
    fn new(code: u8, mnemonic: &'static str, len: u8, cycles: u8, mode: AddressingMode) -> Self {
        OpCode {
            code,
            mnemonic,
            len,
            cycles,
            mode,
        }
    }
}

lazy_static! {
    pub static ref CPU_OPS_CODES: Vec<OpCode> = vec![
    OpCode::new(0x00, "BRK", 1, 7, AddressingMode::NoneAddressing),
    OpCode::new(0xea, "NOP", 1, 2, AddressingMode::NoneAddressing),

    // Arithmetic
    OpCode::new(0x69, "ADC", 2, 2, AddressingMode::Immediate),
    OpCode::new(0x65, "ADC", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0x75, "ADC", 2, 4, AddressingMode::ZeroPage_X),
    OpCode::new(0x6d, "ADC", 3, 4, AddressingMode::Absolute),
    OpCode::new(0x7d, "ADC", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
    OpCode::new(0x79, "ADC", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
    OpCode::new(0x61, "ADC", 2, 6, AddressingMode::Indirect_X),
    OpCode::new(0x71, "ADC", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

    OpCode::new(0xe9, "SBC", 2, 2, AddressingMode::Immediate),
    OpCode::new(0xe5, "SBC", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0xf5, "SBC", 2, 4, AddressingMode::ZeroPage_X),
    OpCode::new(0xed, "SBC", 3, 4, AddressingMode::Absolute),
    OpCode::new(0xfd, "SBC", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
    OpCode::new(0xf9, "SBC", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
    OpCode::new(0xe1, "SBC", 2, 6, AddressingMode::Indirect_X),
    OpCode::new(0xf1, "SBC", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

    OpCode::new(0x29, "AND", 2, 2, AddressingMode::Immediate),
    OpCode::new(0x25, "AND", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0x35, "AND", 2, 4, AddressingMode::ZeroPage_X),
    OpCode::new(0x2d, "AND", 3, 4, AddressingMode::Absolute),
    OpCode::new(0x3d, "AND", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
    OpCode::new(0x39, "AND", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
    OpCode::new(0x21, "AND", 2, 6, AddressingMode::Indirect_X),
    OpCode::new(0x31, "AND", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

    OpCode::new(0x49, "EOR", 2, 2, AddressingMode::Immediate),
    OpCode::new(0x45, "EOR", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0x55, "EOR", 2, 4, AddressingMode::ZeroPage_X),
    OpCode::new(0x4d, "EOR", 3, 4, AddressingMode::Absolute),
    OpCode::new(0x5d, "EOR", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
    OpCode::new(0x59, "EOR", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
    OpCode::new(0x41, "EOR", 2, 6, AddressingMode::Indirect_X),
    OpCode::new(0x51, "EOR", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

    OpCode::new(0x09, "ORA", 2, 2, AddressingMode::Immediate),
    OpCode::new(0x05, "ORA", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0x15, "ORA", 2, 4, AddressingMode::ZeroPage_X),
    OpCode::new(0x0d, "ORA", 3, 4, AddressingMode::Absolute),
    OpCode::new(0x1d, "ORA", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
    OpCode::new(0x19, "ORA", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
    OpCode::new(0x01, "ORA", 2, 6, AddressingMode::Indirect_X),
    OpCode::new(0x11, "ORA", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

    // Shifts
    OpCode::new(0x0a, "ASL", 1, 2, AddressingMode::NoneAddressing),
    OpCode::new(0x06, "ASL", 2, 5, AddressingMode::ZeroPage),
    OpCode::new(0x16, "ASL", 2, 6, AddressingMode::ZeroPage_X),
    OpCode::new(0x0e, "ASL", 3, 6, AddressingMode::Absolute),
    OpCode::new(0x1e, "ASL", 3, 7, AddressingMode::Absolute_X),

    OpCode::new(0x4a, "LSR", 1, 2, AddressingMode::NoneAddressing),
    OpCode::new(0x46, "LSR", 2, 5, AddressingMode::ZeroPage),
    OpCode::new(0x56, "LSR", 2, 6, AddressingMode::ZeroPage_X),
    OpCode::new(0x4e, "LSR", 3, 6, AddressingMode::Absolute),
    OpCode::new(0x5e, "LSR", 3, 7, AddressingMode::Absolute_X),

    OpCode::new(0x2a, "ROL", 1, 2, AddressingMode::NoneAddressing),
    OpCode::new(0x26, "ROL", 2, 5, AddressingMode::ZeroPage),
    OpCode::new(0x36, "ROL", 2, 6, AddressingMode::ZeroPage_X),
    OpCode::new(0x2e, "ROL", 3, 6, AddressingMode::Absolute),
    OpCode::new(0x3e, "ROL", 3, 7, AddressingMode::Absolute_X),

    OpCode::new(0x6a, "ROR", 1, 2, AddressingMode::NoneAddressing),
    OpCode::new(0x66, "ROR", 2, 5, AddressingMode::ZeroPage),
    OpCode::new(0x76, "ROR", 2, 6, AddressingMode::ZeroPage_X),
    OpCode::new(0x6e, "ROR", 3, 6, AddressingMode::Absolute),
    OpCode::new(0x7e, "ROR", 3, 7, AddressingMode::Absolute_X),

    OpCode::new(0xe6, "INC", 2, 5, AddressingMode::ZeroPage),
    OpCode::new(0xf6, "INC", 2, 6, AddressingMode::ZeroPage_X),
    OpCode::new(0xee, "INC", 3, 6, AddressingMode::Absolute),
    OpCode::new(0xfe, "INC", 3, 7, AddressingMode::Absolute_X),

    OpCode::new(0xe8, "INX", 1, 2, AddressingMode::NoneAddressing),

    OpCode::new(0xc8, "INY", 1, 2, AddressingMode::NoneAddressing),

    OpCode::new(0xc6, "DEC", 2, 5, AddressingMode::ZeroPage),
    OpCode::new(0xd6, "DEC", 2, 6, AddressingMode::ZeroPage_X),
    OpCode::new(0xce, "DEC", 3, 6, AddressingMode::Absolute),
    OpCode::new(0xde, "DEC", 3, 7, AddressingMode::Absolute_X),

    OpCode::new(0xca, "DEX", 1, 2, AddressingMode::NoneAddressing),

    OpCode::new(0x88, "DEY", 1, 2, AddressingMode::NoneAddressing),

    OpCode::new(0xc9, "CMP", 2, 2, AddressingMode::Immediate),
    OpCode::new(0xc5, "CMP", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0xd5, "CMP", 2, 4, AddressingMode::ZeroPage_X),
    OpCode::new(0xcd, "CMP", 3, 4, AddressingMode::Absolute),
    OpCode::new(0xdd, "CMP", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
    OpCode::new(0xd9, "CMP", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
    OpCode::new(0xc1, "CMP", 2, 6, AddressingMode::Indirect_X),
    OpCode::new(0xd1, "CMP", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

    OpCode::new(0xe0, "CPX", 2, 2, AddressingMode::Immediate),
    OpCode::new(0xe4, "CPX", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0xec, "CPX", 3, 4, AddressingMode::Absolute),

    OpCode::new(0xc0, "CPY", 2, 2, AddressingMode::Immediate),
    OpCode::new(0xc4, "CPY", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0xcc, "CPY", 3, 4, AddressingMode::Absolute),

    // Branching
    // TODO: JMP
    // TODO: JSR
    // TODO: RTS
    // TODO: RTI
    // TODO: BNE
    // TODO: BVS
    // TODO: BVC
    // TODO: BMI
    // TODO: BEQ
    // TODO: BCS
    // TODO: BCC
    // TODO: BPL
    // TODO: BIT

    // Stores and loads
    OpCode::new(0xa9, "LDA", 2, 2, AddressingMode::Immediate),
    OpCode::new(0xa5, "LDA", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0xb5, "LDA", 2, 4, AddressingMode::ZeroPage_X),
    OpCode::new(0xad, "LDA", 3, 4, AddressingMode::Absolute),
    OpCode::new(0xbd, "LDA", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
    OpCode::new(0xb9, "LDA", 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
    OpCode::new(0xa1, "LDA", 2, 6, AddressingMode::Indirect_X),
    OpCode::new(0xb1, "LDA", 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),
    // TODO: LDX
    // TODO: LDY
    OpCode::new(0x85, "STA", 2, 3, AddressingMode::ZeroPage),
    OpCode::new(0x95, "STA", 2, 4, AddressingMode::ZeroPage_X),
    OpCode::new(0x8d, "STA", 3, 4, AddressingMode::Absolute),
    OpCode::new(0x9d, "STA", 3, 5, AddressingMode::Absolute_X),
    OpCode::new(0x99, "STA", 3, 5, AddressingMode::Absolute_Y),
    OpCode::new(0x81, "STA", 2, 6, AddressingMode::Indirect_X),
    OpCode::new(0x91, "STA", 2, 6, AddressingMode::Indirect_Y),
    // TODO: STX
    // TODO: STY

    // Clear flags
    // TODO: CLD
    // TODO: CLI
    // TODO: CLV
    // TODO: CLC
    // TODO: SEC
    // TODO: SEI
    // TODO: SED
    OpCode::new(0xaa, "TAX", 1, 2, AddressingMode::NoneAddressing),
    // TODO: TAY
    // TODO: TSX
    // TODO: TXA
    // TODO: TXS
    // TODO: TYA

    // Stack
    // TODO: PHA
    // TODO: PLA
    // TODO: PHP
    // TODO: PLP

    ];

    pub static ref OPCODES_MAP: HashMap<u8, &'static OpCode> = {
        let mut map = HashMap::new();
        for cpuop in &*CPU_OPS_CODES {
            map.insert(cpuop.code, cpuop);
        }
        map
    };
}
