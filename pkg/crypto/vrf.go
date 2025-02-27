package crypto

import (
	"bytes"
	"crypto/sha256"

	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type VrfInput struct {
	label   []byte // max length is 2^8-1, i.e., length can be stored in one byte
	version uint32
}

func encode(input VrfInput) []byte {
	buf := bytes.NewBuffer([]byte{})
	buf.WriteByte(utils.Uint8(len(input.label)))
	buf.Write(input.label)
	buf.Write(utils.Uint32(input.version))
	return buf.Bytes()
}

func VRF_hash(sk []byte, input VrfInput) [32]byte {
	return sha256.Sum256(encode(input))
}

func VRF_prove(sk []byte, input VrfInput) []byte {
	return encode(input)
}

func VRF_proof_to_hash(proof []byte) [32]byte {
	return sha256.Sum256(proof)
}

func VRF_verify(pk []byte, input VrfInput, proof []byte) (bool, [32]byte) {
	return bytes.Equal(encode(input), proof), VRF_proof_to_hash(proof)
}
