package misc

import "github.com/felixlinker/keytrans-verification/pkg/utils"

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

/*@
pred SliceMapInv(m map[uint64][]byte) {
	acc(m) && (forall k uint64 :: k elem m ==> utils.BytesMem(m[k]))
}
@*/

// @ requires utils.BytesMem(v)
// @ preserves SliceMapInv(m)
func MapSet(k uint64, v []byte, m map[uint64][]byte) {
	// @ unfold acc(SliceMapInv(m))
	m[k] = v
	// TODO:
	// @ inhale acc(SliceMapInv(m))
}

// @ requires noPerm < p
// @ preserves acc(SliceMapInv(m), p)
// @ ensures ok ==> utils.BytesMem(r)
func MapGet(m map[uint64][]byte, k uint64 /*@, ghost p perm @*/) (r []byte, ok bool) {
	var tmp []byte
	// @ unfold acc(SliceMapInv(m), p)
	if tmp, ok = m[k]; ok {
		r = utils.Copy(tmp /*@, p @*/)
	}
	// @ fold acc(SliceMapInv(m), p)
	return
}
