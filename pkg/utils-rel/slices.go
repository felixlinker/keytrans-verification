package utilsrel

import "github.com/felixlinker/keytrans-verification/pkg/utils"

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(bs1), p) && acc(utils.BytesMem(bs2), p)
// @ ensures len(r) == len(bs1) + len(bs2)
// @ ensures utils.BytesMem(r)
// @ ensures low(utils.GetBytesContent(r)) == (low(utils.GetBytesContent(bs1)) && low(utils.GetBytesContent(bs2)))
func Concat(bs1 []byte, bs2 []byte /*@, ghost p perm @*/) (r []byte) {
	r = utils.Copy(bs1 /*@, p @*/)
	// @ unfold utils.BytesMem(r)
	// @ unfold acc(utils.BytesMem(bs2), p)
	r = append( /*@ p, @*/ r, bs2...)
	// @ fold acc(utils.BytesMem(bs2), p)
	if len(r) == 0 {
		r = []byte{}
	}
	// @ fold utils.BytesMem(r)
	return
}
