package utils

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"errors"
)

func AllZero(bs [sha256.Size]byte) bool {
	return bs == [sha256.Size]byte{}
}

// @ requires 0 <= lenBytes && lenBytes <= 32/8
// @ ensures p != nil ==> acc(p)
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
