package crypto

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type CommitmentValue struct {
	Opening []byte
	Label   []byte
	Version uint64
	Update  *proofs.UpdateValue
}

/*@
pred (cv *CommitmentValue) Inv() {
	acc(cv) && acc(cv.Opening) && acc(cv.Label) && acc(cv.Update.Inv())
}
@*/

// @ preserves noPerm < p && acc(cv.Inv(), p)
// @ ensures acc(r)
func (cv *CommitmentValue) Marshal( /*@ ghost p perm @*/ ) (r []byte) {
	buf := bytes.NewBuffer(nil)
	// @ unfold acc(cv.Inv(), p)
	buf.Write(cv.Opening)
	buf.WriteByte(utils.Uint8(len(cv.Label)))
	buf.Write(cv.Label)
	// We represent version as uint64 to do less type casting, but spec uses
	// uint32
	buf.Write(utils.Uint32(uint32(cv.Version)))
	buf.Write(cv.Update.Marshal( /*@ p @*/ ))
	// @ fold acc(cv.Inv(), p)
	return buf.Bytes()
}

// @ preserves noPerm < p && acc(commitment, p) && acc(cv.Inv(), p)
func VerifyCommitmentValue(commitment []byte, cv *CommitmentValue /*@, ghost p perm @*/) bool {
	// TODO: Make package variable, but I don't know how to handle the memory
	// permission of that
	// See https://www.ietf.org/archive/id/draft-ietf-keytrans-protocol-04.html#section-15.1-8.3.1
	kc := []byte{0xd8, 0x21, 0xf8, 0x79, 0x0d, 0x97, 0x70, 0x97, 0x96, 0xb4, 0xd7, 0x90, 0x33, 0x57, 0xc3, 0xf5}

	mac := hmac.New(sha256.New, kc /*@, perm(1/2) @*/)
	mac.Write(cv.Marshal( /*@ p @*/ ) /*@, p @*/)
	return hmac.Equal(commitment, mac.Sum(nil /*@, noPerm @*/) /*@, p @*/)
}
