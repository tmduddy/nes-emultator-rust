use crate::Memory;

const RAM: u16 = 0x0000;
const RAM_MIRRORS_END: u16 = 0x1FFF;
const PPU_REG: u16 = 0x2000;
const PPU_REG_MIRRORS_END: u16 = 0x3FFF;

#[derive (Debug)]
pub struct Bus {
    pub cpu_vram: [u8; 2048],
}

impl Bus {
    pub fn new() -> Self {
        Bus {
            cpu_vram: [0; 2048],
        }
    }
}

impl Default for Bus {
    fn default() -> Self {
        Bus::new()
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
            _ => {
                println!("Ignoring memory access at {}", addr);
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
            _ => {
                println!("Ignoring memory write-access at {}", addr);
            }
        }
    }
}
