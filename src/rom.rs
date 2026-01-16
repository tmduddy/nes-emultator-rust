const NES_TAG: [u8; 4] = [0x4E, 0x45, 0x53, 0x1A];
const PRG_ROM_PAGE_SIZE: usize = 0x4000;
const CHR_ROM_PAGE_SIZE: usize = 0x2000;

#[derive(Debug, PartialEq)]
pub enum Mirroring {
    Vertical,
    Horizontal,
    FourScreen,
}

/// ROM dump files following the iNES format simulate the basic functions of a physical NES
/// cartridge. This struct has fields that mimic the two physical memory chips, one for PRG_ROM
/// which the CPU has direct access to, but the PPU does not, and CHR_ROM which the PPU has direct
/// access to but the CPU does not.
#[derive(Debug)]
pub struct Rom {
    /// ## prg_rom
    ///
    /// Holds onto the program code for the game. Expected to be directly accessed by the CPU.
    ///
    /// in iNES files this is represented as some number of 16kB ROM banks as noted by the header.
    pub prg_rom: Vec<u8>,

    /// ## chr_rom
    ///
    /// Holds onto the visual graphics data. Expected to be directly accessed by the PPU.
    ///
    /// in iNES files this is represented as some number of 8kB VROM banks, as noted by the header.
    pub chr_rom: Vec<u8>,

    /// ## mapper
    ///
    /// This represents the mapper type in use. For now we'll only support Mapper 0.
    /// 0 -> "no mapper", the CPU reads both CHR and PRG ROM as is.
    pub mapper: u8,

    /// ## screen_mirroring
    ///
    /// This determines how the graphics data should be parsed and remains consistent throughout
    /// the duration of any given cartridge / ROM.
    pub screen_mirroring: Mirroring,
}

impl Rom {
    pub fn new(raw: &[u8]) -> Result<Rom, String> {
        if raw[0..4] != NES_TAG {
            return Err("File is not in iNES 1.0 format".to_string());
        }

        let mapper = raw[7] & 0b1111_0000 | (raw[6] >> 4);

        let ines_ver = (raw[7] >> 2) & 0b11;
        if ines_ver != 0 {
            return Err("NES2.0 format is not supported!".to_string());
        }

        let four_screen = raw[6] & 0b1000 != 0;
        let vertical_mirroring = raw[6] & 0b11 != 0;
        let screen_mirroring = match(four_screen, vertical_mirroring) {
            (true, _) => Mirroring::FourScreen,
            (false, true) => Mirroring::Vertical,
            (false, false) => Mirroring::Horizontal,
        };

        let prg_rom_size = raw[4] as usize * PRG_ROM_PAGE_SIZE;
        let chr_rom_size = raw[5] as usize * CHR_ROM_PAGE_SIZE;

        let skip_trainer = raw[6] & 0b100 != 0;

        let prg_rom_start = 16 + if skip_trainer {512} else {0};
        let prg_rom_end = prg_rom_start + prg_rom_size;
        
        let chr_rom_start = prg_rom_start + prg_rom_size;
        let chr_rom_end = chr_rom_start + chr_rom_size;


        Ok(Rom {
            prg_rom: raw[prg_rom_start..prg_rom_end].to_vec(),
            chr_rom: raw[chr_rom_start..chr_rom_end].to_vec(),
            mapper,
            screen_mirroring,
        })
    }
}
