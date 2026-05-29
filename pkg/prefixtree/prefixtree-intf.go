package prefixtree

//@ import "github.com/felixlinker/keytrans-verification/pkg/utils"

/*@
// this captures our assumption that GetCommitment is deterministic
ghost
decreases
// returns bool: true = commitment exists (inclusion), false = no commitment (non-inclusion)
pure func GetCommitmentExists(label seq[byte], version uint64, rootHash seq[byte]) (commitmentExists bool)
@*/

type PT interface {
	//@ pred Inv()

	// Returns non-nil if we can prove that the prefix tree contains a key for the
	// label and version pair provided. Returns nil if we can prove that the
	// prefix tree does not contain a key for the label and version pair provided.
	// Returns error in any other case.
	// @ requires  noPerm < p
	// @ preserves acc(Inv(), p)
	// @ preserves acc(utils.BytesMem(label), p)
	// @ preserves acc(utils.BytesMem(rootHash), p)
	// @ requires  0 <= version
	// @ ensures   err == nil && res != nil ==> acc(res)
	// @ ensures   err == nil ==> (res != nil) == GetCommitmentExists(utils.getBytesContent(label), version, utils.getBytesContent(rootHash))
	// @ decreases
	GetCommitment(label []byte, version uint64, rootHash []byte /*@, ghost p perm@*/) (res []byte, err error)
}
