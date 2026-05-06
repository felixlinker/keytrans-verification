package crypto

import (
	"bytes"

	"github.com/ProtonMail/go-ecvrf/ecvrf"
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
// @ ensures ok ==> len(r) == 64 && acc(r)
func VRF_verify(pk []byte, label []byte, version uint64, prf []byte /*@, ghost p perm @*/) (r []byte, ok bool) {
	if pk, err := ecvrf.NewPublicKey(pk /*@, p @*/); err != nil {
		return nil, false
	} else if ok, out, err := pk.Verify(encode(label, version /*@, p @*/), prf /*@, p @*/); !ok || out == nil || err != nil {
		return nil, false
	} else {
		return out, true
	}
}
