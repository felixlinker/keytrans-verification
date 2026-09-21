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
//
// TWO THINGS MUST NOT CHANGE, or the axioms become contradictory and every
// proof resting on them turns vacuous:
//
//  1. This stays a LEMMA taking the two sequences, never a global
//     `forall a, b :: HashOf(a) == HashOf(b) ==> a == b`. Injectivity of a
//     function from an unbounded domain into fixed-width digests is false by
//     pigeonhole; keeping it per-instance means the solver never holds the
//     quantified form and cannot run that argument.
//  2. HashOf gets NO postcondition about the length of its output, for the
//     same reason -- the cardinality argument needs a bound on the codomain.
//
// Checked: with both facts supplied to the solver for a single pair, `false`
// is still not provable. It would be with the quantified form. Note also that
// Z3 is not a cardinality reasoner, so an inconsistency introduced here may
// stay latent and surface unpredictably rather than failing loudly.
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
