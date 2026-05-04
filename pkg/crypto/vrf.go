package crypto

import (
	"bytes"
	"crypto/sha256"

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
// @ preserves acc(sk, p) && acc(label, p)
func VRF_hash(sk []byte, label []byte, version uint64 /*@, ghost p perm @*/) (r [32]byte) {
	r = sha256.Sum256(encode(label, version /*@, p @*/) /*@, p @*/)
	return r
}

// @ requires noPerm < p
// @ preserves acc(sk, p) && acc(label, p)
func VRF_prove(sk []byte, label []byte, version uint64 /*@, ghost p perm @*/) [32]byte {
	return VRF_hash(sk, label, version /*@, p @*/)
}

// @ trusted
// @ preserves acc(prf)
func VRF_proof_to_hash(prf []byte) [32]byte {
	var out [32]byte
	copy(out[:], prf)
	return out
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(pk) && acc(label, p) && acc(prf, p)
func VRF_verify(pk []byte, label []byte, version uint64, prf []byte /*@, ghost p perm @*/) (r [32]byte, ok bool) {
	hash := VRF_hash(nil, label, version)
	proofHash := VRF_proof_to_hash(prf)
	return proofHash, hash == proofHash
}
