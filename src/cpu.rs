use std::collections::HashMap;
use crate::opcodes;
use bitflags::bitflags;

const PROGRAM_COUNTER_START: u16 = 0xFFFC;
const PROGRAM_MEMORY_START: u16 = 0x8000;

bitflags! {
    pub struct StatusFlags: u8 {
        const CARRY = 0b0000_0001;
        const ZERO = 0b0000_0010;
        const INTERRUPT_DISABLE = 0b0000_0100;
        const DECIMAL_MODE = 0b0000_1000; // Ricoh chip doesn't support this
        const BREAK = 0b0001_0000;
        const BREAK2 = 0b0010_0000; // Might be unused
        const OVERFLOW = 0b0100_0000;
        const NEGATIVE = 0b1000_0000;
    }
}

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

trait Mem {
    fn mem_read(&self, address: u16) -> u8;
    fn mem_read_u16(&mut self, pos: u16) -> u16;
    fn mem_write(&mut self, address: u16, value: u8);
    fn mem_write_u16(&mut self, pos: u16, value: u16);
}

/// Memory implementation for CPU
impl Mem for CPU {
    fn mem_read(&self, address: u16) -> u8 {
        self.memory[address as usize]
    }

    fn mem_read_u16(&mut self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | lo
    }

    fn mem_write(&mut self, address: u16, value: u8) {
        self.memory[address as usize] = value;
    }

    fn mem_write_u16(&mut self, pos: u16, value: u16) {
        let lo = (value & 0xff) as u8;
        let hi = (value >> 8) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

pub struct CPU {
    /// Accumulator register
    pub register_a: u8,
    /// Register x
    pub register_x: u8,
    /// Register y
    pub register_y: u8,

    pub status: StatusFlags,

    pub program_counter: u16,
    memory: [u8; 0xffff],
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: StatusFlags::from_bits_truncate(0b100100),
            program_counter: 0,
            memory: [0; 0xffff],
        }
    }

    fn get_operand_address(&mut self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::ZeroPage_X => {
                let zero_page_address = self.mem_read(self.program_counter);
                let address = zero_page_address.wrapping_add(self.register_x);
                address as u16
            }
            AddressingMode::ZeroPage_Y => {
                let zero_page_address = self.mem_read(self.program_counter);
                let address = zero_page_address.wrapping_add(self.register_y);
                address as u16
            }
            AddressingMode::Absolute_X => {
                let address = self.mem_read_u16(self.program_counter);
                address.wrapping_add(self.register_x as u16)
            }
            AddressingMode::Absolute_Y => {
                let address = self.mem_read_u16(self.program_counter);
                address.wrapping_add(self.register_y as u16)
            }
            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);
                let pointer = base.wrapping_add(self.register_x);
                let lo = self.mem_read(pointer as u16) as u16;
                let hi = self.mem_read(pointer.wrapping_add(1) as u16) as u16;
                (hi << 8) | lo
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);
                let lo = self.mem_read(base as u16) as u16;
                let hi = self.mem_read(base.wrapping_add(1) as u16) as u16;
                let address = (hi << 8) | lo;
                address.wrapping_add(self.register_y as u16)
            }
            AddressingMode::NoneAddressing => panic!("Mode {:?} is not supported", mode),
        }
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            self.status.insert(StatusFlags::ZERO);
        } else {
            self.status.remove(StatusFlags::ZERO)
        }

        if result & 0b1000_0000 != 0 {
            self.status.insert(StatusFlags::NEGATIVE);
        } else {
            self.status.remove(StatusFlags::NEGATIVE)
        }
    }


    /// Handle the LDA (load accumulator) instruction
    fn lda(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// Handle the STA (store accumulator in memory) instruction
    fn sta(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        self.mem_write(address, self.register_a);
    }

    /// Handle the TAX (transfer accumulator to index x) instruction
    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    /// Handle the INX (increment index x) instruction
    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    /// Handle the ADC (add with carry) instruction
    fn adc(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        self.add_to_register_a(value);
    }

    /// Handle the SBC (subtract with carry) instruction
    fn sbc(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        // Thank god for rust and their wrapping operations
        self.add_to_register_a(value.wrapping_neg().wrapping_sub(1) as u8);
    }

    /// Handle the AND (bitwise and) instruction
    fn and(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        self.register_a &= value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        self.register_a ^= value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn ora(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        self.register_a |= value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /// Handle the ASL (arithmetic shift left) instruction for the accumulator
    ///
    /// This is a special case because it doesn't take an operand and just runs on the accumulator
    fn asl_accumulator(&mut self) {
        let value = self.register_a;
        let result = value << 1;

        self.status.set(StatusFlags::CARRY, value >> 7 == 1);

        self.set_register_a(result);
    }

    fn asl(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        let result = value << 1;
        self.mem_write(address, result);

        self.status.set(StatusFlags::CARRY, value >> 7 == 1);

        self.update_zero_and_negative_flags(result);
    }

    fn lsr_accumulator(&mut self) {
        let value = self.register_a;
        let result = value >> 1;

        self.status.set(StatusFlags::CARRY, value & 1 == 1);

        self.set_register_a(result);
    }

    fn lsr(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        let result = value >> 1;
        self.mem_write(address, result);

        self.status.set(StatusFlags::CARRY, value & 1 == 1);

        self.update_zero_and_negative_flags(result);
    }

    fn rol_accumulator(&mut self) {
        let value = self.register_a;
        let result = value << 1 | self.status.contains(StatusFlags::CARRY) as u8;

        self.status.set(StatusFlags::CARRY, value >> 7 == 1);

        self.set_register_a(result);
    }

    fn rol(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        let result = value << 1 | self.status.contains(StatusFlags::CARRY) as u8;
        self.mem_write(address, result);

        self.status.set(StatusFlags::CARRY, value >> 7 == 1);

        self.update_zero_and_negative_flags(result);
    }

    fn ror_accumulator(&mut self) {
        let value = self.register_a;
        let result = value >> 1 | (self.status.contains(StatusFlags::CARRY) as u8) << 7;

        self.status.set(StatusFlags::CARRY, value & 1 == 1);

        self.set_register_a(result);
    }

    fn ror(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        let result = value >> 1 | (self.status.contains(StatusFlags::CARRY) as u8) << 7;
        self.mem_write(address, result);

        self.status.set(StatusFlags::CARRY, value & 1 == 1);

        self.update_zero_and_negative_flags(result);
    }

    fn inc(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        let result = value.wrapping_add(1);
        self.mem_write(address, result);

        self.update_zero_and_negative_flags(result);
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        let result = value.wrapping_sub(1);
        self.mem_write(address, result);

        self.update_zero_and_negative_flags(result);
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn cmp(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        self.status.set(StatusFlags::CARRY, self.register_a >= value);


        self.update_zero_and_negative_flags(self.register_a.wrapping_sub(value));
    }

    fn cpx(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        self.status.set(StatusFlags::CARRY, self.register_x >= value);

        self.update_zero_and_negative_flags(self.register_x.wrapping_sub(value));
    }

    fn cpy(&mut self, mode: &AddressingMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read(address);

        self.status.set(StatusFlags::CARRY, self.register_y >= value);

        self.update_zero_and_negative_flags(self.register_y.wrapping_sub(value));
    }

    fn add_to_register_a(&mut self, value: u8) {
        let sum = self.register_a as u16 + value as u16 + self.status.contains(StatusFlags::CARRY) as u16;

        // If result overflows the maximum (255) then we need to set the carry flag
        if sum > 0xff {
            self.status.insert(StatusFlags::CARRY);
        } else {
            self.status.remove(StatusFlags::CARRY);
        }

        let result = sum as u8;

        if (value ^ result) & (result ^ self.register_a) & 0x80 != 0 {
            self.status.insert(StatusFlags::OVERFLOW);
        } else {
            self.status.remove(StatusFlags::OVERFLOW);
        }

        self.set_register_a(result)
    }

    fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = StatusFlags::from_bits_truncate(0b100100);

        self.program_counter = self.mem_read_u16(PROGRAM_COUNTER_START);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memory[PROGRAM_MEMORY_START as usize .. (PROGRAM_MEMORY_START as usize + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(PROGRAM_COUNTER_START, PROGRAM_MEMORY_START as u16)
    }

    // Actually run the program in a loop
    pub fn run(&mut self) {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;

        loop {
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = opcodes.get(&code).expect(&format!("OpCode {:x} is not recognized", code));

            match code {
                // LDA (load accumulator) opcodes
                0xa9 | 0xa5 | 0xb5 | 0xad | 0xbd | 0xb9 | 0xa1 | 0xb1 => {
                    self.lda(&opcode.mode);
                }
                /* ADC */
                0x69 | 0x65 | 0x75 | 0x6d | 0x7d | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }
                /* SBC */
                0xe9 | 0xe5 | 0xf5 | 0xed | 0xfd | 0xf9 | 0xe1 | 0xf1 => {
                    self.sbc(&opcode.mode);
                }
                // STA (store accumulator) opcodes
                0x85 | 0x95 | 0x8d | 0x9d | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }
                // AND (bitwise and) opcodes
                0x29 | 0x25 | 0x35 | 0x2d | 0x3d | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }
                // EOR (bitwise exclusive or) opcodes
                0x49 | 0x45 | 0x55 | 0x4d | 0x5d | 0x59 | 0x41 | 0x51 => {
                    self.eor(&opcode.mode);
                }
                // ORA (bitwise or) opcodes
                0x09 | 0x05 | 0x15 | 0x0d | 0x1d | 0x19 | 0x01 | 0x11 => {
                    self.ora(&opcode.mode);
                }
                // ASL (arithmetic shift left) opcode
                0x0a => self.asl_accumulator(),
                0x06 | 0x16 | 0x0e | 0x1e => self.asl(&opcode.mode),
                // LSR (logical shift right) opcode
                0x4a => self.lsr_accumulator(),
                0x46 | 0x56 | 0x4e | 0x5e => self.lsr(&opcode.mode),
                // ROL (rotate left) opcode
                0x2a => self.rol_accumulator(),
                0x26 | 0x36 | 0x2e | 0x3e => self.rol(&opcode.mode),
                // ROR (rotate right) opcode
                0x6a => self.ror_accumulator(),
                0x66 | 0x76 | 0x6e | 0x7e => self.ror(&opcode.mode),
                // TAX (Transfer accumulator to index x) opcode
                0xAA => self.tax(),
                // INC (increment memory) opcode
                0xE6 | 0xF6 | 0xEE | 0xFE => self.inc(&opcode.mode),
                // INX (increment index x) opcode
                0xE8 => self.inx(),
                // INY (increment index y) opcode
                0xC8 => self.iny(),
                // DEC (decrement memory) opcode
                0xC6 | 0xD6 | 0xCE | 0xDE => self.dec(&opcode.mode),
                // DEX (decrement index x) opcode
                0xCA => self.dex(),
                // DEY (decrement index y) opcode
                0x88 => self.dey(),
                // CMP (compare accumulator) opcode
                0xC9 | 0xC5 | 0xD5 | 0xCD | 0xDD | 0xD9 | 0xC1 | 0xD1 => self.cmp(&opcode.mode),
                // CPX (compare index x) opcode
                0xE0 | 0xE4 | 0xEC => self.cpx(&opcode.mode),
                // CPY (compare index y) opcode
                0xC0 | 0xC4 | 0xCC => self.cpy(&opcode.mode),
                // BRK (break) opcode
                0x00 => return,
                // NOP (no operation) opcode
                0xEA => (),
                _ => todo!(),
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_0xa9_lda_immediate_load_data() {
        let mut cpu = CPU::new();
        // Run LDA with 0x05 as the parameter, ending with a break
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 5);
        assert!(cpu.status & StatusFlags::ZERO == StatusFlags { bits: 0 });
        assert!(cpu.status & StatusFlags::NEGATIVE == StatusFlags { bits: 0 });
    }

    #[test]
    fn test_0xa9_lda_immediate_zero_flag() {
        let mut cpu = CPU::new();
        // Run LDA with 0x00 as the parameter, ending with a break
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert_eq!(cpu.register_a, 0x00);
        assert!(cpu.status & StatusFlags::ZERO == StatusFlags { bits: 2 });
    }

    #[test]
    fn test_lda_from_memory() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);
        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let mut cpu = CPU::new();
        // Run LDA with 0x05 as the parameter, transfer it to x, ending with a break
        cpu.load_and_run(vec![0xa9, 0x05, 0xaa, 0x00]);
        assert_eq!(cpu.register_x, 5);
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);
        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::new();
        // fill accumulator with 0xff, store it in x, and try to increment it above 0xff
        // which should fail
        cpu.load_and_run(vec![0xa9, 0xff, 0xaa, 0xe8, 0xe8, 0x00]);
        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_adc() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x69, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 10);
    }

    #[test]
    /// Test that the carry flag is set when the result of an addition is greater than 255
    fn test_adc_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0x69, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 0);
        assert!(cpu.status.contains(StatusFlags::CARRY));
    }

    #[test]
    fn test_adc_overflow() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x7f, 0x69, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 0x80);
        assert!(cpu.status.contains(StatusFlags::OVERFLOW));
    }

    #[test]
    fn test_sbc() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0xe9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 255);
        assert!(!cpu.status.contains(StatusFlags::CARRY));
    }

    #[test]
    fn test_sbc_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x06, 0xe9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0);
        assert!(cpu.status.contains(StatusFlags::CARRY));
    }

    #[test]
    fn test_sbc_overflow() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x7f, 0xe9, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 0x7e);
        assert!(cpu.status.contains(StatusFlags::OVERFLOW));
    }

    #[test]
    fn test_and() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x29, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 1);
    }

    #[test]
    fn test_eor() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x49, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 4);
    }

    #[test]
    fn test_ora() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x09, 0x01, 0x00]);
        assert_eq!(cpu.register_a, 5);
    }

    #[test]
    fn test_asl() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x0a, 0x00]);
        assert_eq!(cpu.register_a, 10);
    }

    #[test]
    /// Test that no operation does nothing and sets status to zero
    fn test_nop() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xea, 0x00]);
        assert_eq!(cpu.register_a, 0);
        // Default flags
        assert!(cpu.status.contains(StatusFlags::from_bits_truncate(0b100100)));
    }
}
