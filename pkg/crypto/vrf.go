package crypto

import (
	"bytes"
	"crypto/sha256"

	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type VrfInput struct {
	Label   []byte // max length is 2^8-1, i.e., length can be stored in one byte
	Version uint64
}

/*@
pred (input VrfInput) Inv() {
	acc(input.Label) && len(input.Label) <= 255
}
@*/

// @ trusted
// @ preserves input.Inv()
// @ ensures   acc(res)
func encode(input VrfInput) (res []byte) {
	buf := bytes.NewBuffer([]byte{})
	buf.WriteByte(utils.Uint8(len(input.Label)))
	buf.Write(input.Label)
	buf.Write(utils.Uint64(input.Version))
	return buf.Bytes()
}

// @ trusted
// @ preserves acc(sk) && input.Inv()
func VRF_hash(sk []byte, input VrfInput) [32]byte {
	return sha256.Sum256(encode(input))
}

// @ trusted
// @ preserves acc(sk) && input.Inv()
func VRF_prove(sk []byte, input VrfInput) [32]byte {
	return VRF_hash(sk, input)
}

// @ trusted
// @ preserves acc(prf)
func VRF_proof_to_hash(prf []byte) [32]byte {
	var out [32]byte
	copy(out[:], prf)
	return out
}

// @ trusted
// @ preserves acc(pk) && input.Inv()
func VRF_verify(pk []byte, input VrfInput, prf []byte) (r [32]byte, ok bool) {
	hash := VRF_hash(nil, input)
	proofHash := VRF_proof_to_hash(prf)
	return proofHash, hash == proofHash
}
