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
@*/

// @ ensures acc(r)
// @ ensures len(r) == 8
// @ ensures GetBitsContent(r) == ByteBits_Pure(b)
func ByteBits(b byte) (r []bool) {
	r = []bool{}
	// @ rseq := seq[bool]{}

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
requires 0 <= i && i <= len(bs)
decreases len(bs)-i
pure func bitsPure_Rec(bs seq[byte], i int) (r seq[bool]) {
	return len(bs) == i ? seq[bool]{} : ByteBits_Pure(bs[i]) ++ bitsPure_Rec(bs, i+1)
}

ghost
decreases
pure func BitsSeq(bs seq[byte]) (r seq[bool]) {
	return bitsPure_Rec(bs, 0)
}
@*/

// @ requires noPerm < p
// @ preserves acc(BytesMem(bytes), p)
// @ ensures acc(r)
// @ ensures len(r) == len(bytes)*8
// @ ensures GetBitsContent(r) == BitsSeq(GetBytesContent(bytes))
func Bits(bytes []byte /*@, ghost p perm @*/) (r []bool) {
	r = make([]bool, 0, len(bytes)*8)
	// @ rseq := seq[bool]{}
	// @ pureBs := GetBytesContent(bytes)

	// @ invariant 0 <= i && i <= len(bytes)
	// @ invariant len(r) == (len(bytes)-i)*8
	// @ invariant len(rseq) == (len(bytes)-i)*8
	// @ invariant acc(BytesMem(bytes), p) && acc(r)
	// @ invariant pureBs == GetBytesContent(bytes)
	// @ invariant rseq == bitsPure_Rec(pureBs, i)
	// @ invariant forall j int :: 0 <= j && j < len(r) ==> r[j] == rseq[j]
	for i := len(bytes); 0 < i; i-- {
		// @ unfold acc(BytesMem(bytes), p)
		r = append( /*@ perm(1/2), @*/ ByteBits(bytes[i-1]), r...)
		// @ fold acc(BytesMem(bytes), p)
		// @ rseq = ByteBits_Pure(pureBs[i-1]) ++ rseq
	}
	// @ assert rseq == BitsSeq(pureBs)
	return r
}

/*@
ghost
requires 0 <= start
decreases len(s) - start
pure func FlippedTailsPure(s seq[bool], start int) (r seq[seq[bool]]) {
	return start >= len(s) ?
		seq[seq[bool]]{} :
		(seq[seq[bool]]{ s[:start] ++ seq[bool]{ !s[start] } }) ++ FlippedTailsPure(s, start+1)
}
@*/

/*@
pred BytesSliceInv(s [][]byte) {
	forall i int :: 0 <= i && i < len(s) ==> acc(&s[i]) && acc(BytesMem(s[i]))
}

pred BitsSliceInv(s [][]bool) {
	forall i int :: 0 <= i && i < len(s) ==> acc(&s[i]) && acc(s[i])
}
@*/

// @ requires noPerm < p
// @ preserves acc(s, p)
// @ requires 0 <= start
// @ ensures BitsSliceInv(r)
func FlippedTails(s []bool, start int /*@, ghost p perm @*/) (r [][]bool) {
	r = make([][]bool, 0)
	// @ fold BitsSliceInv(r)
	// @ invariant start <= i
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
