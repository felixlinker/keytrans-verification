package utils

// @ requires 0 <= i && i < 8
// @ decreases
// @ pure
func byteBit(b byte, i int) bool {
	return (b<<i)&0x80 > 0
}

/*@
ghost
requires 0 <= i && i <= j && j <= 8
ensures len(r) == j-i
decreases j-i
pure func byteBits_Rec(b byte, i int, j int) (r seq[bool]) {
	return i == j ? seq[bool]{} : seq[bool]{ byteBit(b, i) } ++ byteBits_Rec(b, i + 1, j)
}

ghost
ensures len(r) == 8
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
pure func byteBitsSeq_Rec(bs []bool, i int) (r seq[bool]) {
	return len(bs) == i ? seq[bool]{} : (seq[bool]{bs[i]} ++ byteBitsSeq_Rec(bs, i+1))
}

ghost
requires acc(bs, _)
ensures len(bs) == len(r)
ensures forall j int :: 0 <= j && j < len(r) ==> r[j] == bs[j]
decreases
pure func BitsSeq(bs []bool) (r seq[bool]) {
	return byteBitsSeq_Rec(bs, 0)
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

/*@
ghost
requires acc(bs, _)
requires 0 <= i && i <= len(bs)
decreases len(bs)-i
pure func bitsPure_Rec(bs []byte, i int) (r seq[bool]) {
	return len(bs) == i ? seq[bool]{} : ByteBits_Pure(bs[i]) ++ bitsPure_Rec(bs, i+1)
}

ghost
requires acc(bs, _)
decreases
pure func Bits_Pure(bs []byte) (r seq[bool]) {
	return bitsPure_Rec(bs, 0)
}
@*/

// @ requires noPerm < p
// @ preserves acc(bytes, p)
// @ ensures acc(r)
// @ ensures len(r) == len(bytes)*8
// @ ensures BitsSeq(r) == Bits_Pure(bytes)
func Bits(bytes []byte /*@, ghost p perm @*/) (r []bool) {
	r = make([]bool, 0, len(bytes)*8)
	// @ ghost rseq := seq[bool]{}

	// @ invariant 0 <= i && i <= len(bytes)
	// @ invariant len(r) == (len(bytes)-i)*8
	// @ invariant len(rseq) == (len(bytes)-i)*8
	// @ invariant acc(bytes, p) && acc(r)
	// @ invariant rseq == bitsPure_Rec(bytes, i)
	// @ invariant forall j int :: 0 <= j && j < len(r) ==> r[j] == rseq[j]
	for i := len(bytes); 0 < i; i-- {
		r = append( /*@ perm(1/2), @*/ ByteBits(bytes[i-1]), r...)
		// @ rseq = ByteBits_Pure(bytes[i-1]) ++ rseq
	}
	// @ assert rseq == Bits_Pure(bytes)
	return r
}

/*@
pred BitsSliceInv(s [][]bool) {
	forall i int :: 0 <= i && i < len(s) ==> acc(&s[i]) && acc(s[i])
}
@*/

// @ requires noPerm < p
// @ preserves acc(s, p)
// @ requires 0 <= start && start <= len(s)
// @ ensures BitsSliceInv(r)
func FlippedTails(s []bool, start int /*@, ghost p perm @*/) (r [][]bool) {
	r = make([][]bool, 0)
	// @ fold BitsSliceInv(r)
	// @ invariant start <= i && i <= len(s)
	// @ invariant acc(s, p) && BitsSliceInv(r) && len(r) == i-start
	for i := start; i < len(s); i++ {
		tmp /*@@@*/ := make([]bool, i+1)
		copy(tmp, s[:i+1] /*@, p/2 @*/)
		tmp[i] = !tmp[i]
		// @ unfold BitsSliceInv(r)
		r = append( /*@ p/2, @*/ r, tmp)
		// @ fold BitsSliceInv(r)
	}
	return
}
