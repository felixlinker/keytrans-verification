package utils

import (
	"bytes"
	"encoding/binary"
	"errors"
)

func Uint8(x int) byte {
	buf := make([]byte, 0, 4)
	buf = binary.BigEndian.AppendUint32(buf, uint32(x))
	return buf[3]
}

// @ ensures acc(res)
func Uint32(x uint32) (res []byte) {
	buf := make([]byte, 0, 4)
	buf = binary.BigEndian.AppendUint32(buf, x)
	return buf
}

func ReadUint32(buf *bytes.Buffer) (ui uint32, err error) {
	p := make([]byte, 4)
	if n, e := buf.Read(p); n != len(p) || e != nil {
		if e == nil {
			err = errors.New("wrong number of bytes read")
		} else {
			err = e
		}
	} else {
		ui = binary.BigEndian.Uint32(p /*@, perm(1/2) @*/)
	}
	return
}

// @ ensures acc(res)
func Uint64(x uint64) (res []byte) {
	buf := make([]byte, 0, 8)
	buf = binary.BigEndian.AppendUint64(buf, x)
	return buf
}

func ReadUint64(buf *bytes.Buffer) (ui uint64, err error) {
	p := make([]byte, 8)
	if n, e := buf.Read(p); n != len(p) || e != nil {
		if e == nil {
			err = errors.New("wrong number of bytes read")
		} else {
			err = e
		}
	} else {
		ui = binary.BigEndian.Uint64(p /*@, perm(1/2) @*/)
	}
	return
}
