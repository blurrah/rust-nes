use crate::cpu::AddressingMode;
use std::collections::HashMap;

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

    // TODO: SBC
    // TODO: AND
    // TODO: EOR
    // TODO: ORA

    // Shifts
    // TODO: ASL
    // TODO: LSR
    // TODO: ROL
    // TODO: ROR
    // TODO: INC
    OpCode::new(0xe8, "INX", 1, 2, AddressingMode::NoneAddressing),
    // TODO: INY
    // TODO: DEC
    // TODO: DEX
    // TODO: DEY
    // TODO: CMP
    // TODO: CPX
    // TODO: CPY

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
