package utilsrel

import "github.com/felixlinker/keytrans-verification/pkg/utils"

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(x), p)
// @ ensures r != nil && acc(utils.BytesMem(r))
// @ ensures utils.BytesEqual(x, r)
// @ ensures low(utils.GetBytesContent(x)) == low(utils.GetBytesContent(r))
func CopyLow(x []byte /*@, ghost p perm @*/) (r []byte) {
	r = utils.Copy(x /*@, p @*/)
	// @ assert low(len(r)) == low(len(x))
	// @ assert low(len(r)) ==> (unfolding acc(utils.BytesMem(x), p) in unfolding utils.BytesMem(r) in forall i int :: {r[i]} {x[i]} 0 <= i && i < len(r) ==> low(r[i]) == low(x[i]))
	return
}

// Concatenate two byte slices and prove that if the length of the first byte
// slice is low, then the resulting byte slices is low if and only if both
// arguments are low.
// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(bs1), p) && acc(utils.BytesMem(bs2), p)
// @ ensures len(r) == len(bs1) + len(bs2)
// @ ensures utils.BytesMem(r)
// @ ensures low(len(bs1)) ==> (low(len(r)) == low(len(bs2)))
// @ ensures low(len(bs1)) ==> (low(utils.GetBytesContent(r)) == (low(utils.GetBytesContent(bs1)) && low(utils.GetBytesContent(bs2))))
func Concat(bs1 []byte, bs2 []byte /*@, ghost p perm @*/) (r []byte) {
	r = CopyLow(bs1 /*@, p @*/)

	// @ invariant 0 <= i && i <= len(bs2)
	// @ invariant len(r) == len(bs1) + i
	// @ invariant utils.BytesMem(r) && r != nil
	// @ invariant acc(utils.BytesMem(bs1), p) && acc(utils.BytesMem(bs2), p)
	// @ invariant utils.GetBytesContent(r) == utils.GetBytesContent(bs1) ++ utils.GetBytesContent(bs2)[:i]
	for i := 0; i < len(bs2); i++ {
		// @ unfold utils.BytesMem(r)
		// @ unfold acc(utils.BytesMem(bs2), p)
		r = append( /*@ perm(1/2), @*/ r, bs2[i])
		// @ fold acc(utils.BytesMem(bs2), p)
		// @ fold utils.BytesMem(r)
	}

	// @ assert len(r) == len(bs1) + len(bs2)
	// @ assert utils.GetBytesContent(r) == utils.GetBytesContent(bs1) ++ utils.GetBytesContent(bs2)
	/*@
	ghost if low(len(bs1)) {
		assert low(len(r)) == low(len(bs2))
		unfold utils.BytesMem(r)
		unfold acc(utils.BytesMem(bs1), p)
		unfold acc(utils.BytesMem(bs2), p)
		assert forall i int :: {r[i]} {bs1[i]} 0 <= i && i < len(bs1) ==> r[i] == bs1[i]
		assert forall j int :: {r[len(bs1)+j]} {bs2[j]} 0 <= j && j < len(bs2) ==> r[len(bs1)+j] == bs2[j]
		fold utils.BytesMem(r)
		fold acc(utils.BytesMem(bs2), p)
		fold acc(utils.BytesMem(bs1), p)
	}
	@*/
	return
}
