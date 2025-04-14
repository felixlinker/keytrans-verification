package crypto

import (
	"bytes"
	"crypto/sha256"

	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type VrfInput struct {
	Label   []byte // max length is 2^8-1, i.e., length can be stored in one byte
	Version uint32
}

/*@
pred (input VrfInput) Inv() {
	acc(input.Label) && len(input.Label) <= 255
}
@*/

//@ trusted
//@ preserves input.Inv()
//@ ensures   acc(res)
func encode(input VrfInput) (res []byte) {
	buf := bytes.NewBuffer([]byte{})
	buf.WriteByte(utils.Uint8(len(input.Label)))
	buf.Write(input.Label)
	buf.Write(utils.Uint32(input.Version))
	return buf.Bytes()
}

//@ trusted
//@ preserves acc(sk) && input.Inv()
func VRF_hash(sk []byte, input VrfInput) [32]byte {
	return sha256.Sum256(encode(input))
}

//@ trusted
//@ preserves acc(sk) && input.Inv()
func VRF_prove(sk []byte, input VrfInput) [32]byte {
	return VRF_hash(sk, input)
}

func VRF_proof_to_hash(prf [32]byte) [32]byte {
	return prf
}

//@ trusted
//@ preserves acc(pk) && input.Inv()
func VRF_verify(pk []byte, input VrfInput, prf [32]byte) (bool, [32]byte) {
	return VRF_hash(nil, input) == prf, VRF_proof_to_hash(prf)
}
