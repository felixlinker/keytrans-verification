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
// assumption. The converse is not assumed at all: see IsCollision below.
ghost
decreases
pure func HashOf(input seq[byte]) (output seq[byte])

// A collision: two distinct inputs with the same digest. Real hash functions
// have collisions -- the domain is unbounded and digests are fixed width --
// so a development may not assume they do not exist. Instead theorems are
// conditioned on no collision having occurred, which is the standard
// game-based phrasing and is honest about what is being claimed.
ghost
decreases
pure func IsCollision(a seq[byte], b seq[byte]) bool {
	return a != b && HashOf(a) == HashOf(b)
}

// Equal digests and no collision give equal preimages.
//
// This is a tautology, not an assumption: !IsCollision(a, b) unfolds to
// !(a != b && HashOf(a) == HashOf(b)), which together with the equal digests
// forces a == b. Nothing here claims the hash is injective, so there is no
// cardinality claim for the pigeonhole principle to contradict -- unlike an
// assumed `HashOf(a) == HashOf(b) ==> a == b`, which is inconsistent with any
// bound on the digest width and would make every proof resting on it vacuous.
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
	// Call sum, whose result is modelled by the pure function HashOf.
	output = sum(input /*@, p @*/)
	// @ assume utils.GetBytesContent(output) == HashOf(utils.GetBytesContent(input))
	return
}
