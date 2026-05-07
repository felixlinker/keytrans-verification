package utils

import (
	"encoding/binary"
)

//@ trusted
func Uint8(x int) byte {
	buf := make([]byte, 0, 4)
	buf = binary.BigEndian.AppendUint32(buf, uint32(x))
	return buf[3]
}

//@ trusted
//@ ensures acc(res)
func Uint32(x uint32) (res []byte) {
	buf := make([]byte, 0, 4)
	buf = binary.BigEndian.AppendUint32(buf, x)
	return buf
}

// @ trusted
// @ ensures acc(res)
func Uint64(x uint64) (res []byte) {
	buf := make([]byte, 0, 8)
	buf = binary.BigEndian.AppendUint64(buf, x)
	return buf
}
