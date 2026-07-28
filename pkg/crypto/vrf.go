package crypto

import (
	"bytes"

	vrf "github.com/Bren2010/katie/crypto/vrf/edwards25519"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

// @ requires noPerm < p
// @ preserves acc(label, p)
// @ ensures   acc(res)
func encode(label []byte, version uint64 /*@, ghost p perm @*/) (res []byte) {
	buf := bytes.NewBuffer([]byte{})
	buf.WriteByte(utils.Uint8(len(label)))
	buf.Write(label)
	buf.Write(utils.Uint32(uint32(version)))
	return buf.Bytes()
}

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(pk), p) && acc(utils.BytesMem(label), p) && acc(utils.BytesMem(prf), p)
// @ ensures ok ==> utils.BytesMem(r) && len(r) == 32
func VRF_verify(pk []byte, label []byte, version uint64, prf []byte /*@, ghost p perm @*/) (r []byte, ok bool) {
	// @ unfold acc(utils.BytesMem(pk), p)
	// @ unfold acc(utils.BytesMem(label), p)
	// @ unfold acc(utils.BytesMem(prf), p)
	if pk, err := vrf.NewPublicKey(pk /*@, p @*/); err != nil {
		ok = false
	} else if out, err := pk.Verify(encode(label, version /*@, p @*/), prf /*@, p @*/); out == nil || err != nil {
		ok = false
	} else {
		// Truncation required in https://www.ietf.org/archive/id/draft-ietf-keytrans-protocol-04.html#name-kt-cipher-suites
		r = out[:32]
		// @ fold utils.BytesMem(r)
		ok = true
	}
	// @ fold acc(utils.BytesMem(pk), p)
	// @ fold acc(utils.BytesMem(label), p)
	// @ fold acc(utils.BytesMem(prf), p)
	return
}
