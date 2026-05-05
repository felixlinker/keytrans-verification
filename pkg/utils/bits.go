package utils

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

// @ requires noPerm < p
// @ preserves acc(bytes, p)
// @ ensures acc(r)
// @ ensures len(r) == len(bytes)*8
func Bits(bytes []byte /*@, ghost p perm @*/) (r []bool) {
	r = make([]bool, 0, len(bytes)*8)
	// @ invariant 0 <= i && i <= len(bytes)
	// @ invariant len(r) == i*8
	// @ invariant acc(bytes, p) && acc(r)
	for i := 0; i < len(bytes); i++ {
		r = append( /*@ perm(1), @*/ r, ByteBits(bytes[i])...)
	}
	return r
}
