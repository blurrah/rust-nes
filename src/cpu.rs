use std::collections::HashMap;
use crate::opcodes;

const PROGRAM_COUNTER_START: u16 = 0xFFFC;
const PROGRAM_MEMORY_START: u16 = 0x8000;

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

    pub status: u8,

    pub program_counter: u16,
    memory: [u8; 0xffff],
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: 0,
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
            self.status = self.status | 0b0000_0010;
        } else {
            self.status = self.status & 0b1111_1101;
        }

        if result & 0b1000_0000 != 0 {
            self.status = self.status | 0b1000_0000;
        } else {
            self.status = self.status & 0b0111_1111;
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

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = 0;

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
                // STA (store accumulator) opcodes
                0x85 | 0x95 | 0x8d | 0x9d | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }
                // TAX (Transfer accumulator to index x) opcode
                0xAA => self.tax(),
                // INX (increment index x) opcode
                0xE8 => self.inx(),
                // BRK (break) opcode
                0x00 => return,
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
        assert!(cpu.status & 0b0000_0010 == 0);
        assert!(cpu.status & 0b1000_0000 == 0);
    }

    #[test]
    fn test_0xa9_lda_immediate_zero_flag() {
        let mut cpu = CPU::new();
        // Run LDA with 0x00 as the parameter, ending with a break
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert_eq!(cpu.register_a, 0x00);
        assert!(cpu.status & 0b0000_0010 == 0b10);
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
}