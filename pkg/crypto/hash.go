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
// Pure model of the hash. Being a function, low(x) ==> low(HashOf(x)).
ghost
decreases
pure func HashOf(input seq[byte]) (output seq[byte])

// Two distinct inputs with the same digest. Theorems that need equal digests
// to imply equal preimages are conditioned on this not holding.
ghost
decreases
pure func IsCollision(a seq[byte], b seq[byte]) bool {
	return a != b && HashOf(a) == HashOf(b)
}

// Tautology; no injectivity is assumed.
ghost
ensures HashOf(a) == HashOf(b) && !IsCollision(a, b) ==> a == b
decreases
func NoCollisionMeansEqual(a seq[byte], b seq[byte]) {
}
@*/

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(input), p)
// @ ensures  output != nil && utils.BytesMem(output)
// @ ensures  utils.GetBytesContent(output) == HashOf(utils.GetBytesContent(input))
func Sum(input []byte /*@, ghost p perm @*/) (output []byte) {
	output = sum(input /*@, p @*/)
	// @ assume utils.GetBytesContent(output) == HashOf(utils.GetBytesContent(input))
	return
}
