package utils

import (
	"bytes"
	"errors"
)

// ReadOptional reads an optional value "encoded with a presence-signaling
// octet, followed by the value itself if present. When decoding, a presence
// octet with a value other than 0 or 1 MUST be rejected as malformed."
// (https://datatracker.ietf.org/doc/html/draft-ietf-keytrans-protocol-06#section-2.1.1)
func ReadOptional(buf *bytes.Buffer) (present bool, err error) {
	if b, e := buf.ReadByte(); e != nil {
		err = e
	} else if b == 0 {
		present = false
	} else if b == 1 {
		present = true
	} else {
		err = errors.New("malformed optional: presence octet must be 0 or 1")
	}
	return
}
