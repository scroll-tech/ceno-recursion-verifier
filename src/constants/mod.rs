pub const OPCODE_KEYS: [&str; 14] = [
    "ADD", "ADDI", "ANDI", "BEQ", "BLTU", "BNE", "JALR", "LW", "ORI", "SB", "SRAI", "SRLI", "SUB",
    "SW",
];

pub const TABLE_KEYS: [&str; 13] = [
    "OPS_And",
    "OPS_Ltu",
    "OPS_Or",
    "OPS_Pow",
    "OPS_Xor",
    "PROGRAM",
    "RAM_Memory_PubIOTable",
    "RAM_Memory_StaticMemTable",
    "RAM_Register_RegTable",
    "RANGE_U14",
    "RANGE_U16",
    "RANGE_U5",
    "RANGE_U8",
];