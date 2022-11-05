pub fn u32_from_le_slice(data: &[u8]) -> u32 {
	u32::from_le_bytes([data[0], data[1], data[2], data[3]])
}
