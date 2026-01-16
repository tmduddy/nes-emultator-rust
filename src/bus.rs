use crate::{Memory, rom::Rom};

const RAM: u16 = 0x0000;
const RAM_MIRRORS_END: u16 = 0x1FFF;
const PPU_REG: u16 = 0x2000;
const PPU_REG_MIRRORS_END: u16 = 0x3FFF;

#[derive(Debug)]
pub struct Bus {
    cpu_vram: [u8; 2048],
    rom: Rom,
}

impl Bus {
    pub fn new(rom: Rom) -> Self {
        Bus {
            cpu_vram: [0; 2048],
            rom,
        }
    }

    fn read_prg_rom(&self, mut addr: u16) -> u8 {
        addr -= 0x8000;
        if self.rom.prg_rom.len() == 0x4000 && addr >= 0x4000 {
            addr %= 0x4000;
        }
        self.rom.prg_rom[addr as usize]
    }
}

impl Memory for Bus {
    fn mem_read(&self, addr: u16) -> u8 {
        match addr {
            RAM..=RAM_MIRRORS_END => {
                let mirror_down_addr = addr & 0b0000_0111_1111_1111;
                self.cpu_vram[mirror_down_addr as usize]
            }
            PPU_REG..=PPU_REG_MIRRORS_END => {
                let _mirror_down_addr = addr & 0b0010_0000_0000_0111;
                todo!("PPU is not supported yet")
            }
            0x8000..=0xFFFF => self.read_prg_rom(addr),
            _ => {
                println!("Invalid memory access at {}", addr);
                0
            }
        }
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        match addr {
            RAM..=RAM_MIRRORS_END => {
                let mirror_down_addr = addr & 0b0000_0111_1111_1111;
                self.cpu_vram[mirror_down_addr as usize] = data;
            }
            PPU_REG..=PPU_REG_MIRRORS_END => {
                let _mirror_down_addr = addr & 0b0010_0000_0000_0111;
                todo!("PPU is not supported yet")
            }
            0x8000..=0xFFFF => {
                panic!("Attempted to write to Cartridge ROM space");
            }
            _ => {
                println!("Invalid memory write-access at {}", addr);
            }
        }
    }
}
