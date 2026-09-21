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

