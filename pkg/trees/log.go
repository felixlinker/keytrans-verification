package trees

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/search"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type logTree struct {
	index uint64
	size  uint64
	value *[sha256.Size]byte
	left  *logTree
	right *logTree
}

/*@
pred (t *logTree) Inv() {
	acc(t) && 1 <= t.size &&
	(t.value != nil ==> acc(t.value)) &&
	(t.left != nil ==> acc(t.left.Inv())) &&
	(t.right != nil ==> acc(t.right.Inv())) &&
	(t.left == nil) == (t.right == nil)
}
@*/

// @ preserves acc(t.Inv())
func (t *logTree) cut() {
	// @ unfold acc(t.Inv())
	t.left = nil
	t.right = nil
	// @ fold acc(t.Inv())
}

// Remove all nodes from the tree that are not on the frontier, and memorize
// the hash values of all balanced subtrees.
// @ preserves acc(t.Inv())
func (t *logTree) Prune() {
	t.prune(search.Frontier( /*@ unfolding acc(t.Inv()) in @*/ t.size))
}

// @ preserves acc(t.Inv())
// @ requires acc(keeping)
// @ ensures acc(r) && len(r) <= len(keeping)
func (t *logTree) prune(keeping []uint64) (r []uint64) {
	// @ unfold acc(t.Inv())
	if t.left == nil || t.right == nil {
		i := 0
		// @ fold acc(t.Inv())
		// @ invariant 0 <= i && i <= len(keeping)
		// @ invariant acc(keeping) && acc(t.Inv())
		for ; i < len(keeping) && keeping[i] < /*@ unfolding acc(t.Inv()) in @*/ t.index+t.size; i++ {
		}
		// Help gobra realize the relation between keeping and its subslice
		// @ assert forall j int :: {&keeping[i:][j]} 0 <= j && j < len(keeping[i:]) ==> &keeping[i:][j] == &keeping[i+j]
		// @ assert acc(keeping[i:])
		return keeping[i:]
	} else {
		// @ assert t.left != nil && t.right != nil // Test tree invariant
		// Recurse if tree is unbalanced or we must preserve children
		if t.size != utils.LargestSmallerPower(t.size) || (0 < len(keeping) && keeping[0] < t.index+t.size) {
			keeping = t.left.prune(keeping)
			// @ unfold acc(t.left.Inv())
			keeping = t.right.prune(keeping)
			// @ fold acc(t.left.Inv())
			// @ fold acc(t.Inv())
			return keeping
		} else {
			// We do not modify keeping in this branch. The below assert checks that
			// this is justified: Either, the slice is empty, or the to-be-kept items
			// are outside this subtree.
			// @ assert 0 == len(keeping) || t.index+t.size <= keeping[0]
			// @ fold acc(t.Inv())
			t.cut()
			return keeping
		}
	}
}

// @ ensures acc(t.Inv())
func Singleton() (t *logTree) {
	tree /*@@@*/ := logTree{
		size:  1,
		value: nil,
		left:  nil,
		right: nil,
	}
	// @ fold (&tree).Inv()
	return &tree
}

// @ requires forall i int :: 0 <= i && i < len(leafs) ==> acc(&leafs[i]) && acc(leafs[i])
// @ ensures acc(t.Inv())
func FullTree(leafs []*[sha256.Size]byte) (t *logTree) {
	t = Singleton()
	// @ invariant 0 <= i && i <= len(leafs)
	// @ invariant forall j int :: i <= j && j < len(leafs) ==> acc(&leafs[j]) && acc(leafs[j])
	// @ invariant acc(t.Inv())
	for i := 0; i < len(leafs); i++ {
		t.setLeaf(uint64(i), leafs[i])
	}
	return t
}

// Grow the tree until it can store idx.
// @ preserves acc(t.Inv())
func (t *logTree) fit(offset uint64, idx uint64) {
	// @ invariant acc(t.Inv())
	for /*@ unfolding acc(t.Inv()) in @*/ t.index+t.size <= idx {
		// @ unfold acc(t.Inv())
		lsp := utils.LargestSmallerPower(t.size)
		if lsp == t.size {
			// tree is already fully balanced; move both children into left child

			newLeft := Singleton()
			// @ unfold acc(newLeft.Inv())
			newLeft.index = t.index
			newLeft.size = t.size
			newLeft.value = t.value
			newLeft.left = t.left
			newLeft.right = t.right
			// @ fold acc(newLeft.Inv())

			t.index = t.size - 1
			t.value = nil
			t.left = newLeft
			t.right = Singleton()
			// new right child contains one node; effectively, this tree now contains
			// 2^n+1 nodes. We will grow the right child as necessary next.
			// @ assert unfolding acc(t.right.Inv()) in (t.left == nil) == (t.right == nil)
		}

		// Do we need to double in size or just fit to the next index?
		if lsp*2 <= idx {
			t.size = lsp * 2
		} else {
			t.size = idx + 1
		}

		// Grow right subtree; left subtree will already be balanced or nil
		if t.right != nil {
			// set right to be full-balanced subtree
			t.right.fit(
				/*@ unfolding acc(t.left.Inv()) in @*/ t.left.index+t.left.size,
				/*@ unfolding acc(t.left.Inv()) in @*/ t.size-t.left.size,
			)
		}

		// @ fold acc(t.Inv())
	}
}

// @ requires l != nil ==> acc(l)
// @ requires 0 <= idx
// @ preserves acc(t.Inv()) && unfolding acc(t.Inv()) in 1 <= t.size
func (t *logTree) setLeaf(idx uint64, l *[sha256.Size]byte) {
	// First, prune the tree to only keep what the server knows us to keep
	t.Prune()
	t.fit(0, idx)
	// @ unfold acc(t.Inv())

	// Find subtree to set leaf
	if t.size == 1 {
		t.value = l
	} else {
		var sizeLeft uint64
		if t.left == nil || t.right == nil {
			// test invariant; justifies initializing both trees
			// @ assert t.left == nil && t.right == nil
			sizeLeft = utils.TrueLargestSmallerPower(t.size)
			t.left = Singleton()
			// @ unfold t.left.Inv()
			t.left.index = t.index
			t.left.size = sizeLeft

			t.right = Singleton()
			// @ unfold t.right.Inv()
			t.right.index = t.left.index + t.left.size
			t.right.size = t.size - sizeLeft

			// @ fold t.left.Inv()
			// @ fold t.right.Inv()
		}

		if idx < /*@ unfolding acc(t.left.Inv()) in @*/ t.left.index+t.left.size {
			t.left.setLeaf(idx, l)
		} else {
			t.right.setLeaf(idx, l)
		}
	}
	// @ fold acc(t.Inv())
}

// @ preserves acc(t.Inv())
// @ requires acc(value)
// @ ensures !ok ==> acc(value)
func (t *logTree) fillLeftMost(value *[sha256.Size]byte) (ok bool) {
	// @ unfold acc(t.Inv())
	// @ defer fold acc(t.Inv())
	if t.left != nil && t.right != nil {
		if k := t.left.fillLeftMost(value); k {
			return k
		} else {
			return t.right.fillLeftMost(value)
		}
	} else {
		// @ assert t.left == nil && t.right == nil
		if t.value == nil {
			t.value = value
			return true
		} else {
			return false
		}
	}
}

// @ requires acc(prf.Inv())
// @ requires acc(t.Inv()) && unfolding acc(t.Inv()) in 0 < t.size && t.size < newSize
// @ ensures  acc(newT.Inv()) // && unfolding acc(t.Inv()) in newT.size == newSize
func (t *logTree) Grow(newSize uint64, prf *proofs.InclusionProof) (newT *logTree) {
	if /*@ unfolding acc(prf.Inv()) in @*/ prf == nil {
		panic("non-nil prf")
	}

	// We expect that the inclusion proofs include:
	// - all nodes younger on the path from the old root to the frontier
	// - all nodes on the frontier that are below the most recent distinguished log entry or the root

	// Client must have at least the respective prefix roots
	oldFrontier := search.Frontier( /*@ unfolding acc(t.Inv()) in @*/ t.size)
	consistencyPath := search.YoungerNodesToFrontier(oldFrontier[0], newSize)
	// @ invariant 0 <= i && i <= len(consistencyPath)
	// @ invariant acc(t.Inv()) && acc(consistencyPath, perm(1/2))
	for i := 0; i < len(consistencyPath); i++ {
		// TODO: Either move assume to pre-condition or improve gobra
		// @ assume 0 <= consistencyPath[i]
		t.setLeaf(consistencyPath[i], nil)
	}

	// @ unfold acc(prf.Inv())
	// @ invariant acc(prf) && acc(t.Inv()) && acc(consistencyPath, perm(1/2))
	// @ invariant 0 <= i && i <= len(prf.Elements)
	// @ invariant forall j int :: i <= j && j < len(prf.Elements) ==> acc(&prf.Elements[j]) && acc(prf.Elements[j])
	for i := 0; i < len(prf.Elements); i++ {
		t.fillLeftMost(prf.Elements[i])
	}

	return t
}

// @ preserves acc(t.Inv())
// @ ensures err == nil ==> acc(content)
func (t *logTree) hashContent() (content []byte, err error) {
	if e := t.computeHash(); e != nil {
		return nil, err
	} else {
		// @ unfold acc(t.Inv())
		// @ assert t.value != nil
		content := make([]byte, 1)
		if t.size == 1 {
			content[0] = 0x00
		} else {
			content[0] = 0x11
		}
		content = append( /*@ perm(1/2), @*/ content, (*t.value)[:]...)
		// @ fold acc(t.Inv())
		return content, nil
	}
}

// @ preserves acc(t.Inv())
// @ ensures err == nil ==> unfolding acc(t.Inv()) in t.value != nil
func (t *logTree) computeHash() (err error) {
	// @ unfold acc(t.Inv())
	// @ defer fold acc(t.Inv())
	if t.left == nil || t.right == nil {
		if t.value == nil {
			return errors.New("missing value for incomplete subtree or leaf")
		} else {
			return nil
		}
	} else {
		// @ assert t.left != nil && t.right != nil // test invariant
		if t.value == nil {
			if leftContent, e := t.left.hashContent(); e != nil {
				return e
			} else if rightContent, e := t.right.hashContent(); e != nil {
				return e
			} else {
				a /*@@@*/ := sha256.Sum256(append( /*@ perm(1/2), @*/ leftContent, rightContent...) /*@, perm(1/2) @*/)
				t.value = &a
				return nil
			}
		} else {
			return nil
		}
	}
}

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p) && unfolding acc(t.Inv(), p) in 1 <= t.size
func (t *logTree) GetLeafHash(index uint64 /*@, ghost p perm @*/) (commitment *[sha256.Size]byte, err error) {
	// @ unfold acc(t.Inv(), p)
	// @ defer fold acc(t.Inv(), p)
	if t.size == 1 {
		return t.value, nil
	} else if t.left == nil || t.right == nil {
		// Technically, we do not need both subtrees, but we check the invariant
		// that every node should be a leaf or have two children
		return nil, errors.New("missing subtree")
	} else {
		// @ unfold acc(t.left.Inv(), p)
		if index < t.left.size {
			// @ fold acc(t.left.Inv(), p)
			return t.left.GetLeafHash(index /*@, p @*/)
		} else {
			// @ defer fold acc(t.left.Inv(), p)
			return t.right.GetLeafHash(index - t.left.size /*@, p @*/)
		}
	}
}

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p)
func (t *logTree) GetSize( /*@ ghost p perm @*/ ) uint64 {
	return /*@ unfolding acc(t.Inv(), p) in @*/ t.size
}

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p)
func (t *logTree) GetRoot( /*@ ghost p perm @*/ ) *[sha256.Size]byte {
	return /*@ unfolding acc(t.Inv(), p) in @*/ t.value
}
