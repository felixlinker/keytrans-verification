package crypto

import (
	"crypto/sha256"
	// @ "github.com/felixlinker/keytrans-verification/pkg/utils"
)

// @ requires  noPerm < p
// @ preserves acc(utils.BytesMem(input), p)
// @ ensures   utils.BytesMem(output)
func sum(input []byte /*@, ghost p perm @*/) (output []byte) {
	// @ unfold acc(utils.BytesMem(input), p)
	digest /*@@@*/ := sha256.Sum256(input /*@, p @*/)
	// @ fold acc(utils.BytesMem(input), p)
	output = digest[:]
	// @ fold utils.BytesMem(output)
	return
}

/*@
// Pure model of hashing. Being a (pure) function, lowness of input directly
// implies lowness of the hash.
ghost
decreases
pure func HashOf(input seq[byte]) (output seq[byte])

// Instead of assuming injectivity for hashing, `IsCollision` keeps track of
// whether a collision occurred. This allows us to state properties under the
// assumption that no collision occurred.
ghost
decreases
pure func IsCollision(a seq[byte], b seq[byte]) bool {
	return a != b && HashOf(a) == HashOf(b)
}

ghost
ensures HashOf(a) == HashOf(b) && !IsCollision(a, b) ==> a == b
decreases
func NoCollisionMeansEqual(a seq[byte], b seq[byte]) {
	// no body needed
}
@*/

// @ requires  noPerm < p
// @ preserves acc(utils.BytesMem(input), p)
// @ ensures   utils.BytesMem(output)
// @ ensures   utils.GetBytesContent(output) == HashOf(utils.GetBytesContent(input))
func Sum(input []byte /*@, ghost p perm @*/) (output []byte) {
	output = sum(input /*@, p @*/)
	// @ assume utils.GetBytesContent(output) == HashOf(utils.GetBytesContent(input))
	return
}
