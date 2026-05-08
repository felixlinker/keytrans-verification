package trees

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/search"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type logTree struct {
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

// @ preserves acc(t.Inv())
func (t *logTree) Prune() {
	// @ unfold acc(t.Inv())
	if t.left != nil && t.right != nil {
		// @ assert t.left != nil && t.right != nil
		t.left.cut()
		t.right.Prune()
	}
	// @ fold acc(t.Inv())
}

// @ ensures acc(t.Inv())
func Empty() (t *logTree) {
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
	t = Empty()
	// @ invariant 0 <= i && i <= len(leafs)
	// @ invariant forall j int :: i <= j && j < len(leafs) ==> acc(&leafs[j]) && acc(leafs[j])
	// @ invariant acc(t.Inv())
	for i := 0; i < len(leafs); i++ {
		t.setLeaf(uint64(i), leafs[i])
	}
	return t
}

// @ requires 0 <= idx
// @ requires acc(t.Inv()) && unfolding acc(t.Inv()) in 1 <= t.size
// @ ensures acc(t.Inv()) && unfolding acc(t.Inv()) in 1 <= t.size && idx < t.size
func (t *logTree) fit(idx uint64) {
	// Enlarge tree first if necessary
	// @ invariant acc(t.Inv())
	for /*@ unfolding acc(t.Inv()) in @*/ t.size <= idx {
		// @ unfold acc(t.Inv())
		newLeft := Empty()
		// @ unfold acc(newLeft.Inv())
		newLeft.size = t.size
		newLeft.value = t.value
		newLeft.left = t.left
		newLeft.right = t.right
		// @ fold acc(newLeft.Inv())

		newRight := Empty()
		// @ unfold acc(newRight.Inv())
		newRight.size = t.size
		// @ fold acc(newRight.Inv())

		if t.size*2 <= idx {
			t.size = t.size * 2
		} else {
			t.size = idx + 1
		}
		t.value = nil
		t.left = newLeft
		t.right = newRight
		// @ fold acc(t.Inv())
	}
}

// @ requires l != nil ==> acc(l)
// @ requires 0 <= idx
// @ requires acc(t.Inv()) && unfolding acc(t.Inv()) in 1 <= t.size
// @ ensures acc(t.Inv()) && unfolding acc(t.Inv()) in 1 <= t.size && idx < t.size
func (t *logTree) setLeaf(idx uint64, l *[sha256.Size]byte) {
	// First, prune the tree to only keep what the server knows us to keep
	t.Prune()
	t.fit(idx)
	// @ unfold acc(t.Inv())

	// Find subtree to set leaf
	if t.size == 1 {
		// @ assert idx == 0 // sanity assert
		t.value = l
	} else {
		var sizeLeft uint64
		if t.left != nil && t.right != nil {
			sizeLeft = /*@ unfolding t.left.Inv() in @*/ t.left.size
		} else if t.left != nil || t.right != nil {
			panic("invariant violated")
		} else {
			sizeLeft = utils.TrueLargestSmallerPower(t.size)
			t.left = Empty()
			// @ unfold t.left.Inv()
			t.left.size = sizeLeft
			// @ fold t.left.Inv()
			t.right = Empty()
			// @ unfold t.right.Inv()
			t.right.size = t.size - sizeLeft
			// @ fold t.right.Inv()
		}

		if idx < sizeLeft {
			t.left.setLeaf(idx, l)
		} else {
			t.right.setLeaf(idx-sizeLeft, l)
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

// @ requires noPerm < p
// @ requires acc(prf.Inv())
// @ requires acc(t.Inv()) && unfolding acc(t.Inv()) in 0 < t.size && t.size < newSize
// @ ensures  acc(newT.Inv()) // && unfolding acc(t.Inv()) in newT.size == newSize
func (t *logTree) Grow(newSize uint64, prf *proofs.InclusionProof /*@, ghost p perm @*/) (newT *logTree) {
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
