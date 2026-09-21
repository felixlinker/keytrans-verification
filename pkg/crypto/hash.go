package crypto

import (
	"crypto/sha256"
	// @ "github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(input), p)
// @ ensures  output != nil && utils.BytesMem(output)
func sum(input []byte /*@, ghost p perm @*/) (output []byte) {
	// @ unfold acc(utils.BytesMem(input), p)
	digest /*@@@*/ := sha256.Sum256(input /*@, p @*/)
	// @ fold acc(utils.BytesMem(input), p)
	output = digest[:]
	// @ fold utils.BytesMem(output)
	return
}

/*@
// HashOf is the pure, uninterpreted model of the hash function. Being a
// function, it is deterministic by construction: equal inputs give equal
// outputs, so `low(x) ==> low(HashOf(x))` holds for free and needs no
// assumption. Only the converse is cryptographic content; see
// AssumeCollisionResistance below.
ghost
decreases
pure func HashOf(input seq[byte]) (output seq[byte])

// The single cryptographic assumption of this development: the hash function
// is injective. This is false for any real hash (the domain is larger than the
// 32-byte codomain), so it idealises collision resistance -- an adversary that
// could exhibit a collision would invalidate the proofs that rest on this.
// Stated over the pure model rather than assumed inside Sum, so that it is
// greppable, citable, and used only where a proof explicitly invokes it.
ghost
ensures HashOf(a) == HashOf(b) ==> a == b
decreases
func AssumeCollisionResistance(a seq[byte], b seq[byte]) {
	assume HashOf(a) == HashOf(b) ==> a == b
}
@*/

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(input), p)
// @ ensures  output != nil && utils.BytesMem(output)
// @ ensures  utils.GetBytesContent(output) == HashOf(utils.GetBytesContent(input))
func Sum(input []byte /*@, ghost p perm @*/) (output []byte) {
	// Call sum, whose result is modelled by the pure function HashOf.
	output = sum(input /*@, p @*/)
	// @ assume utils.GetBytesContent(output) == HashOf(utils.GetBytesContent(input))
	return
}
