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

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(bs1), p) && acc(utils.BytesMem(bs2), p)
// @ ensures len(r) == len(bs1) + len(bs2)
// @ ensures utils.BytesMem(r)
// @ ensures low(len(bs1)) ==> (low(len(r)) == low(len(bs2)))
// @ ensures low(len(bs1)) ==> (low(utils.GetBytesContent(r)) == (low(utils.GetBytesContent(bs1)) && low(utils.GetBytesContent(bs2))))
func Concat(bs1 []byte, bs2 []byte /*@, ghost p perm @*/) (r []byte) {
	r = CopyLow(bs1 /*@, p @*/)
	// @ unfold utils.BytesMem(r)
	// @ unfold acc(utils.BytesMem(bs2), p)
	r = append( /*@ p, @*/ r, bs2...)
	// @ fold acc(utils.BytesMem(bs2), p)
	if len(r) == 0 {
		r = []byte{}
	}
	// @ assert low(len(bs1)) ==> (low(len(r)) == low(len(bs2)))
	// @ unfold acc(utils.BytesMem(bs1), p)
	// @ unfold acc(utils.BytesMem(bs2), p)
	// @ assert forall i int :: {r[i]} {bs1[i]} 0 <= i && i < len(bs1) ==> r[i] == bs1[i]
	// @ assert forall j int :: {r[len(bs1)+j]} {bs2[j]} 0 <= j && j < len(bs2) ==> r[len(bs1)+j] == bs2[j]
	// @ ghost utils.GetConcatContent(r, bs1, bs2, p)
	// @ ghost leftContent := utils.GetBytesContent(bs1)
	// @ ghost rightContent := utils.GetBytesContent(bs2)
	/*@
	ghost if low(len(bs1)) {
		both := leftContent ++ rightContent
		assert leftContent == both[:len(leftContent)]
		assert rightContent == both[len(leftContent):]
		assert low(both) ==> low(both[:len(leftContent)])
		assert low(both) ==> low(both[len(leftContent):])
	}
	@*/
	return
}
