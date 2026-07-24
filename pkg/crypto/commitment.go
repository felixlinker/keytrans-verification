package crypto

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"

	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

type UpdateValue struct {
	Value []byte
}

/*@
pred (u *UpdateValue) Inv() {
	acc(u) && acc(u.Value)
}
@*/

// @ requires noPerm < p
// @ preserves acc(v.Inv(), p)
func (v *UpdateValue) Marshal( /*@ ghost p perm @*/ ) (r []byte) {
	// @ unfold acc(v.Inv(), p)
	buf := bytes.NewBuffer(nil)
	buf.Write(utils.Uint32(uint32(len(v.Value))))
	buf.Write(v.Value)
	// @ fold acc(v.Inv(), p)
	return buf.Bytes()
}

// @ requires acc(v)
// @ ensures err == nil ==> acc(v.Inv())
func (v *UpdateValue) Unmarshal(buf *bytes.Buffer) (err error) {
	if p, e := utils.ReadBytes(buf, 32/8); e != nil {
		err = e
	} else {
		v.Value = p
		// @ fold acc(v.Inv())
	}
	return
}

type CommitmentValue struct {
	Opening []byte
	Label   []byte
	Version uint64
	Update  *UpdateValue
}

/*@
pred (cv *CommitmentValue) Inv() {
	acc(cv) && acc(utils.BytesMem(cv.Opening)) && acc(utils.BytesMem(cv.Label)) && acc(cv.Update.Inv())
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

// @ preserves noPerm < p && acc(utils.BytesMem(commitment), p) && acc(cv.Inv(), p)
func VerifyCommitmentValue(commitment []byte, cv *CommitmentValue /*@, ghost p perm @*/) bool {
	// See https://www.ietf.org/archive/id/draft-ietf-keytrans-protocol-04.html#section-15.1-8.3.1
	kc := []byte{0xd8, 0x21, 0xf8, 0x79, 0x0d, 0x97, 0x70, 0x97, 0x96, 0xb4, 0xd7, 0x90, 0x33, 0x57, 0xc3, 0xf5}

	// @ unfold acc(utils.BytesMem(commitment), p)
	mac := hmac.New(sha256.New, kc /*@, perm(1/2) @*/)
	mac.Write(cv.Marshal( /*@ p @*/ ) /*@, p @*/)
	r := hmac.Equal(commitment, mac.Sum(nil /*@, noPerm @*/) /*@, p @*/)
	// @ fold acc(utils.BytesMem(commitment), p)
	return r
}

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(prefix_tree), p)
// @ ensures acc(utils.BytesMem(r))
func LogEntryHash(timestamp uint64, prefix_tree []byte /*@, ghost p perm @*/) (r []byte) {
	// @ unfold acc(utils.BytesMem(prefix_tree), p)
	input := append( /*@ p, @*/ utils.Uint64(timestamp), prefix_tree...)
	// @ fold acc(utils.BytesMem(prefix_tree), p)
	// @ fold acc(utils.BytesMem(input))
	return Sum(input /*@, p @*/)
}
