package utils

import (
	"encoding/binary"
)

func Uint8(x int) byte {
	buf := make([]byte, 0, 4)
	binary.BigEndian.AppendUint32(buf, uint32(x))
	return buf[4]
}

func Uint32(x uint32) []byte {
	buf := make([]byte, 0, 4)
	binary.BigEndian.AppendUint32(buf, x)
	return buf
}
