package crypto

import (
	"crypto/sha256"
	// @ "github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(input), p)
// @ ensures  utils.BytesMem(output)
func sum(input []byte /*@, ghost p perm @*/) (output []byte) {
	// @ unfold acc(utils.BytesMem(input), p)
	digest /*@@@*/ := sha256.Sum256(input /*@, p @*/)
	// @ fold acc(utils.BytesMem(input), p)
	output = digest[:]
	// @ fold utils.BytesMem(output)
	return
}

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(input), p)
// @ ensures  utils.BytesMem(output)
// @ ensures low(utils.GetBytesContent(input)) == low(utils.GetBytesContent(output))
// @ trusted
func Sum(input []byte /*@, ghost p perm @*/) (output []byte) {
	// Call sum, which is proven except for the bijectivity assumption.
	return sum(input /*@, p @*/)
}
