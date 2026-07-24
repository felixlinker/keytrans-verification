package utils

import (
	"bytes"
	"encoding/binary"
)

func Uint8(x int) byte {
	buf := make([]byte, 0, 4)
	buf = binary.BigEndian.AppendUint32(buf, uint32(x))
	return buf[3]
}

func ReadUint16(buf *bytes.Buffer) (ui uint16, err error) {
	p := make([]byte, 2)
	if n, e := buf.Read(p); n != len(p) || e != nil {
		err = BufferError(e)
	} else {
		ui = binary.BigEndian.Uint16(p /*@, perm(1/2) @*/)
	}
	return
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
		err = BufferError(e)
	} else {
		ui = binary.BigEndian.Uint32(p /*@, perm(1/2) @*/)
	}
	return
}

// @ ensures acc(res) && 0 < len(res)
func Uint64(x uint64) (res []byte) {
	buf := make([]byte, 0, 8)
	buf = binary.BigEndian.AppendUint64(buf, x)
	return buf
}

func ReadUint64(buf *bytes.Buffer) (ui uint64, err error) {
	p := make([]byte, 8)
	if n, e := buf.Read(p); n != len(p) || e != nil {
		err = BufferError(e)
	} else {
		ui = binary.BigEndian.Uint64(p /*@, perm(1/2) @*/)
	}
	return
}

// @ ensures err == nil ==> acc(r)
func ReadUint64s(buf *bytes.Buffer) (r []uint64, err error) {
	if lengthByte, e := buf.ReadByte(); e != nil {
		err = e
	} else {
		length := int(uint8(lengthByte))
		// @ assume 0 <= length
		r = make([]uint64, 0, length)

		// @ invariant acc(r)
		for i := 0; i < length && err == nil; i++ {
			if ui, e := ReadUint64(buf); e != nil {
				err = e
			} else {
				r = append( /*@ perm(1/2), @*/ r, ui)
			}
		}
	}
	return
}
