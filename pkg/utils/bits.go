package utils

import "crypto/sha256"

// @ ensures acc(r)
// @ ensures len(r) == 8
func ByteBits(b byte) (r []bool) {
	r = make([]bool, 8)
	// @ ghost p := perm(1)
	// @ invariant len(r) == 8
	// @ invariant 0 <= i && i <= len(r)
	// @ invariant acc(r)
	for i := 0; i < len(r); i++ {
		r[i] = b&0x80 > 0
		b = b << 1
	}
	return r
}

// @ ensures acc(r)
// @ ensures len(bytes) > 0 ==> len(r) > 0
func Bits(bytes [sha256.Size]byte) (r []bool) {
	r = make([]bool, 0, len(bytes)*8)
	// @ ghost p := perm(1)
	// @ invariant 0 <= i && i <= len(bytes)
	// @ invariant 0 < i ==> len(r) > 0
	// @ invariant acc(r, p)
	for i := 0; i < len(bytes); i++ {
		r = append( /*@ p, @*/ r, ByteBits(bytes[i])...)
	}
	return r
}
