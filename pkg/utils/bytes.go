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

// @ requires 1 <= lenBytes && lenBytes <= 4
// @ ensures 0 <= length
func ReadLen(buf *bytes.Buffer, lenBytes int) (length int, err error) {
	lenBuf := make([]byte, lenBytes)
	// @ assert acc(lenBuf)
	if n, e := buf.Read(lenBuf); n != lenBytes || e != nil {
		if e == nil {
			err = errors.New("wrong amount of bytes read")
		} else {
			err = e
		}
	} else {
		if len(lenBuf) < 4 {
			pad := make([]byte, 4-len(lenBuf))
			lenBuf = append( /*@ perm(1/2), @*/ pad, lenBuf...)
		}
		length = int(binary.BigEndian.Uint32(lenBuf /*@, perm(1/2) @*/))
		// @ assume 0 <= length
	}
	return
}

// @ requires 1 <= lenBytes && lenBytes <= 4
// @ ensures p != nil ==> acc(p)
func ReadBytes(buf *bytes.Buffer, lenBytes int) (p []byte, err error) {
	if length, e := ReadLen(buf, lenBytes); e != nil {
		err = e
	} else {
		// @ assume 0 <= length
		p = make([]byte, length)
		if n, e := buf.Read(p); n != len(p) || e != nil {
			if e == nil {
				err = errors.New("wrong amount of bytes read")
			} else {
				err = e
			}
		}
	}
	return
}
