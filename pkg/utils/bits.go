package utils

import "crypto/sha256"

func ByteBits(b byte) []bool {
	r := make([]bool, 0, 8)
	for i := 0; i < 8; i++ {
		r = append(r, b&0x80 > 0)
		b = b << 1
	}
	return r
}

func Bits(bytes [sha256.Size]byte) []bool {
	r := make([]bool, 0, len(bytes)*8)
	for i := 0; i < len(bytes); i++ {
		r = append(r, ByteBits(bytes[i])...)
	}
	return r
}
