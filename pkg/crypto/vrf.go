package crypto

import (
	"bytes"

	vrf "github.com/Bren2010/katie/crypto/vrf/edwards25519"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// @ requires noPerm < p
// @ preserves acc(label, p)
// @ ensures   acc(res)
func encode(label []byte, version uint64 /*@, ghost p perm @*/) (res []byte) {
	buf := bytes.NewBuffer([]byte{})
	buf.WriteByte(utils.Uint8(len(label)))
	buf.Write(label)
	buf.Write(utils.Uint64(version))
	return buf.Bytes()
}

// @ requires noPerm < p
// @ preserves acc(pk, p) && acc(label, p) && acc(prf, p)
// @ ensures ok ==> len(r) == 32 && acc(r)
func VRF_verify(pk []byte, label []byte, version uint64, prf []byte /*@, ghost p perm @*/) (r []byte, ok bool) {
	if pk, err := vrf.NewPublicKey(pk /*@, p @*/); err != nil {
		return nil, false
	} else if out, err := pk.Verify(encode(label, version /*@, p @*/), prf /*@, p @*/); out == nil || err != nil {
		return nil, false
	} else {
		// Truncation required in https://www.ietf.org/archive/id/draft-ietf-keytrans-protocol-04.html#name-kt-cipher-suites
		return out[:32], true
	}
}
