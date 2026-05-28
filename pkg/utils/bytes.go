package utils

import "crypto/sha256"

func AllZero(bs [sha256.Size]byte) bool {
	return bs == [sha256.Size]byte{}
}
