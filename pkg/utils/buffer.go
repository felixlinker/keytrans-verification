package utils

import "errors"

// @ ensures err != nil
func BufferError(inErr error) (err error) {
	if inErr == nil {
		err = errors.New("wrong number of bytes read")
	} else {
		err = inErr
	}
	return
}
