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
	// // @ assert len(r) == len(bs1) + len(bs2)
	if len(r) == 0 {
		r = []byte{}
	}
	// @ assert low(len(bs1)) ==> (low(len(r)) == low(len(bs2)))
	// @ assert low(len(bs1)) && low(len(r)) ==> (unfolding acc(utils.BytesMem(bs1), p) in forall i int :: {r[i]} {bs1[i]} 0 <= i && i < len(bs1) ==> low(r[i]) == low(bs1[i]))
	// @ assert low(len(bs1)) && low(len(r)) ==> (unfolding acc(utils.BytesMem(bs2), p) in forall i int :: {r[i]} {bs2[i]} len(bs1) <= i && i < len(r) ==> low(r[i]) == low(bs2[i-len(bs1)]))
	// @ fold utils.BytesMem(r)
	// @ assert (low(utils.GetBytesContent(r)) ==> (low(len(r)) && unfolding utils.BytesMem(r) in forall i int :: {r[i]} 0 <= i && i < len(r) ==> low(r[i])))
	// @ assert ((low(len(r)) && unfolding utils.BytesMem(r) in forall i int :: {r[i]} 0 <= i && i < len(r) ==> low(r[i])) ==> low(utils.GetBytesContent(r)))
	// @ assert (low(len(bs1)) ==> (low(utils.GetBytesContent(r)) ==> low(len(r)) && low(utils.GetBytesContent(bs1))))
	// @ assert (low(len(bs1)) ==> (low(utils.GetBytesContent(r)) ==> low(len(r)) && low(utils.GetBytesContent(bs2))))
	// // @ assert low(len(bs1)) ==> ((low(len(r)) && low(utils.GetBytesContent(r))) == (low(utils.GetBytesContent(bs1)) && low(utils.GetBytesContent(bs2))))
	return
}
