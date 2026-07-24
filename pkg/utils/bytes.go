package utils

import (
	"bytes"
	"encoding/binary"
	"errors"
)

// @ requires noPerm < p
// @ preserves acc(BytesMem(bs), p)
func AllZero(bs []byte /*@, ghost p perm @*/) (r bool) {
	r = true
	// @ unfold acc(BytesMem(bs), p)
	// @ invariant acc(bs, p) && 0 <= i && i <= len(bs)
	for i := 0; i < len(bs); i++ {
		if bs[i] != 0 {
			r = false
		}
	}
	// @ fold acc(BytesMem(bs), p)
	return
}

// @ requires 0 <= lenBytes && lenBytes <= 4
// @ ensures err == nil ==> p != nil && acc(p)
func ReadBytes(buf *bytes.Buffer, lenBytes int) (p []byte, err error) {
	lenBuf := make([]byte, lenBytes)
	// @ assert acc(lenBuf)
	if n, e := buf.Read(lenBuf); n != len(lenBuf) || e != nil {
		if e == nil {
			err = errors.New("wrong amount of bytes read")
		} else {
			err = e
		}
	} else {
		length := binary.BigEndian.Uint32(lenBuf /*@, perm(1/2) @*/)
		// @ assume 0 <= length
		p = make([]byte, int(length))
		if len(p) == 0 {
			p = []byte{}
		}
		if n, e := buf.Read(p); n != len(p) || e != nil {
			if e == nil {
				err = errors.New("wrong amount of bytes read")
			} else {
				e = err
			}
		}
	}
	return
}

// @ requires 1 <= amount
// @ ensures err == nil ==> p != nil && acc(p)
func ReadBytesFixed(buf *bytes.Buffer, amount int) (p []byte, err error) {
	p = make([]byte, amount)
	if len(p) == 0 {
		p = []byte{}
	}
	if n, e := buf.Read(p); n != len(p) || e != nil {
		if e == nil {
			err = errors.New("wrong amount of bytes read")
		} else {
			e = err
		}
	}
	return
}

// @ requires 1 <= amount
// @ ensures p != nil && err == nil ==> acc(p)
func ReadBytesFixedIf(buf *bytes.Buffer, amount int) (p []byte, err error) {
	if n, e := buf.ReadByte(); e != nil {
		err = e
	} else if n == 1 {
		p, err = ReadBytesFixed(buf, amount)
	}
	return
}
