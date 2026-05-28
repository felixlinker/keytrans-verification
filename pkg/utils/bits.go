package utils

// @ requires 0 <= i && i < 8
// @ decreases
// @ pure
func byteBit(b byte, i int) bool {
	return (b>>i)&0x80 > 0
}

/*@
ghost
requires 0 <= i && i <= j && j <= 8
decreases j-i
pure func byteBits_Rec(b byte, i int, j int) (r seq[bool]) {
	return i == j ? seq[bool]{} : seq[bool]{ byteBit(b, i) } ++ byteBits_Rec(b, i + 1, j)
}

ghost
decreases
pure func ByteBits_Pure(b byte) (r seq[bool]) {
	return byteBits_Rec(b, 0, 8)
}

ghost
requires acc(bs, _)
requires 0 <= i && i <= len(bs)
ensures len(r) == len(bs)-i
ensures forall j int :: 0 <= j && j < len(r) ==> r[j] == bs[i+j]
decreases len(bs)-i
pure func BitsSeq_Rec(bs []bool, i int) (r seq[bool]) {
	return len(bs) == i ? seq[bool]{} : (seq[bool]{bs[i]} ++ BitsSeq_Rec(bs, i+1))
}

ghost
requires acc(bs, _)
ensures len(bs) == len(r)
ensures forall j int :: 0 <= j && j < len(r) ==> r[j] == bs[j]
decreases
pure func BitsSeq(bs []bool) (r seq[bool]) {
	return BitsSeq_Rec(bs, 0)
}
@*/

// @ ensures acc(r)
// @ ensures len(r) == 8
// @ ensures BitsSeq(r) == ByteBits_Pure(b)
func ByteBits(b byte) (r []bool) {
	r = []bool{}
	// @ ghost rseq := seq[bool]{}

	// @ invariant 0 <= i && i <= 8
	// @ invariant len(r) == 8-i && len(rseq) == 8-i
	// @ invariant acc(r)
	// @ invariant rseq == byteBits_Rec(b, i, 8)
	// @ invariant forall j int :: 0 <= j && j < len(r) ==> r[j] == rseq[j]
	for i := 8; 0 < i; i-- {
		r = append( /*@ perm(1/2), @*/ []bool{byteBit(b, i-1)}, r...)
		// @ rseq = seq[bool]{byteBit(b, i-1)} ++ rseq
	}
	// @ assert rseq == ByteBits_Pure(b)
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
