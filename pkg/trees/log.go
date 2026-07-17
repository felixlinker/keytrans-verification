package trees

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/search"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

type Log struct {
	index uint64
	size  uint64
	value *[sha256.Size]byte
	left  *Log
	right *Log
}

/*@
pred (t *Log) Inv() {
	acc(t) && 1 <= t.size &&
	(t.value != nil ==> acc(t.value)) &&
	(t.left != nil ==> acc(t.left.Inv())) &&
	(t.right != nil ==> acc(t.right.Inv())) &&
	(t.left == nil) == (t.right == nil)
}
@*/

// @ preserves acc(t.Inv())
func (t *Log) cut() {
	// @ unfold acc(t.Inv())
	t.left = nil
	t.right = nil
	// @ fold acc(t.Inv())
}

// Remove all nodes from the tree that are not on the frontier, and memorize
// the hash values of all balanced subtrees.
// @ requires acc(t.Inv()) && unfolding acc(t.Inv()) in oldSize <= t.size
// @ ensures acc(t.Inv())
func (t *Log) Prune(oldSize uint64) {
	var keep []uint64
	// @ unfold acc(t.Inv())
	if oldSize == 0 {
		keep = search.Frontier(t.size)
	} else {
		// @ assume 0 <= oldSize // property from uint64
		// @ assert 1 <= oldSize
		keep = search.YoungerToMostRecent(oldSize-1, t.size)
	}
	// @ fold acc(t.Inv())
	t.prune(keep)
}

// @ preserves acc(t.Inv())
// @ requires acc(keeping)
// @ ensures acc(r) && len(r) <= len(keeping)
func (t *Log) prune(keeping []uint64) (r []uint64) {
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
		r = keeping[i:]
	} else {
		// @ assert t.left != nil && t.right != nil // Test tree invariant
		// Recurse if tree is unbalanced or we must preserve children
		if t.size != utils.LargestSmallerPower(t.size) || (0 < len(keeping) && keeping[0] < t.index+t.size) {
			keeping = t.left.prune(keeping)
			// @ unfold acc(t.left.Inv())
			keeping = t.right.prune(keeping)
			// @ fold acc(t.left.Inv())
			// @ fold acc(t.Inv())
			r = keeping
		} else {
			// We do not modify keeping in this branch. The below assert checks that
			// this is justified: Either, the slice is empty, or the to-be-kept items
			// are outside this subtree.
			// @ assert 0 == len(keeping) || t.index+t.size <= keeping[0]
			// @ fold acc(t.Inv())
			t.cut()
			r = keeping
		}
	}
	return
}

// @ requires 1 <= size
// @ ensures t != nil && acc(t.Inv())
// @ ensures unfolding acc(t.Inv()) in t.index == index && t.size == size
func Singleton(index uint64, size uint64) (t *Log) {
	tree /*@@@*/ := Log{
		index: index,
		size:  size,
		value: nil,
		left:  nil,
		right: nil,
	}
	// @ fold (&tree).Inv()
	return &tree
}

// @ preserves acc(t.Inv())
// @ ensures copied != nil && acc(copied.Inv())
// @ ensures old(unfolding acc(t.Inv()) in t.size) == (unfolding acc(t.Inv()) in t.size)
// @ ensures old(unfolding acc(t.Inv()) in t.index) == (unfolding acc(t.Inv()) in t.index)
// @ ensures unfolding acc(copied.Inv()) in unfolding acc(t.Inv()) in copied.index == t.index && copied.size == t.size
func (t *Log) copy() (copied *Log) {
	// @ unfold acc(t.Inv())
	copied = Singleton(t.index, t.size)
	// @ unfold acc(copied.Inv())
	copied.value = t.value
	t.value = nil
	copied.left = t.left
	t.left = nil
	copied.right = t.right
	t.right = nil
	// @ fold acc(copied.Inv())
	// @ fold acc(t.Inv())
	return
}

// @ requires forall i int :: 0 <= i && i < len(leaves) ==> acc(&leaves[i]) && acc(leaves[i])
// @ ensures acc(t.Inv())
func FullTree(leaves []*[sha256.Size]byte) (t *Log) {
	t = Singleton(0, 1)
	// @ invariant 0 <= i && i <= len(leaves)
	// @ invariant forall j int :: i <= j && j < len(leaves) ==> acc(&leaves[j]) && acc(leaves[j])
	// @ invariant acc(t.Inv())
	for i := 0; i < len(leaves); i++ {
		t.setLeaf(uint64(i), leaves[i])
	}
	t.computeHash()
	return t
}

// Grow the tree until it can store idx.
// @ preserves acc(t.Inv())
func (t *Log) fit(idx uint64) {
	// @ invariant acc(t.Inv())
	for /*@ unfolding acc(t.Inv()) in @*/ t.index+t.size <= idx {
		// @ unfold acc(t.Inv())
		lsp := utils.LargestSmallerPower(t.size)
		if lsp == t.size && (t.value != nil || (t.left != nil && t.right != nil)) {
			// Tree is already fully balanced; move both children into left child if
			// they exist.
			// @ fold acc(t.Inv())
			newLeft := t.copy()
			// @ unfold acc(t.Inv())
			t.left = newLeft
			// new right child contains one node; effectively, this tree now contains
			// 2^n+1 nodes. We will grow the right child as necessary next.
			t.right = Singleton( /*@ unfolding acc(newLeft.Inv()) in @*/ newLeft.index+newLeft.size, 1)
			// @ assert unfolding acc(t.right.Inv()) in (t.left == nil) == (t.right == nil)
		}

		// Clear hash value; must be done in any case
		t.value = nil

		// Do we need to double in size or just fit to the next index?
		if t.index+(lsp*2) <= idx {
			t.size = lsp * 2
		} else {
			t.size = idx - t.index + 1
		}

		// Grow right subtree; left subtree will already be balanced or nil
		if t.right != nil {
			// set right to be full-balanced subtree
			t.right.fit( /*@ unfolding acc(t.left.Inv()) in @*/ t.index + t.size - 1)
		}

		// @ fold acc(t.Inv())
	}
}

// @ requires l != nil ==> acc(l)
// @ requires 0 <= idx
// @ preserves acc(t.Inv()) && unfolding acc(t.Inv()) in 1 <= t.size
func (t *Log) setLeaf(idx uint64, l *[sha256.Size]byte) {
	t.fit(idx)
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
			t.left = Singleton(t.index, sizeLeft)
			rightIndex := /*@ unfolding acc(t.left.Inv()) in @*/ t.left.index + t.left.size
			t.right = Singleton(rightIndex, t.size-sizeLeft)
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
func (t *Log) fillLeftMost(value *[sha256.Size]byte) (ok bool) {
	// @ unfold acc(t.Inv())
	if t.left != nil && t.right != nil {
		if k := t.left.fillLeftMost(value); k {
			ok = k
		} else {
			ok = t.right.fillLeftMost(value)
		}
	} else {
		// @ assert t.left == nil && t.right == nil
		if t.value == nil {
			t.value = value
			ok = true
		} else {
			ok = false
		}
	}
	// @ fold acc(t.Inv())
	return
}

// @ requires 1 <= newSize
// @ requires acc(prf.Inv())
// @ requires t != nil ==> acc(t.Inv())
// @ ensures  err == nil ==> acc(newT.Inv()) // && unfolding acc(t.Inv()) in newT.size == newSize
func (t *Log) Grow(newSize uint64, prf *proofs.InclusionProof) (newT *Log, err error) {
	if /*@ unfolding acc(prf.Inv()) in @*/ prf == nil {
		panic("non-nil prf")
	}

	// Client must have at least the respective prefix roots
	var consistencyPath []uint64
	oldSize := t.GetSize( /*@ perm(1/2) @*/ )
	if newSize == oldSize {
		// Nothing to do
		newT = t
		err = nil
	} else if newSize < oldSize {
		err = errors.New("new size smaller than old size")
	} else {
		if t == nil {
			t = Singleton(0, 1)
			consistencyPath = search.Frontier(newSize)
		} else {
			consistencyPath = search.YoungerToMostRecent(oldSize-1, newSize)
		}

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
		for i := 0; i < len(prf.Elements) && err == nil; i++ {
			if ok := t.fillLeftMost(prf.Elements[i]); !ok {
				err = errors.New("could not insert proof element")
			}
		}

		if err == nil {
			if err = t.computeHash(); err == nil {
				newT = t
			}
		}
	}
	return
}

// @ preserves acc(t.Inv())
// @ ensures err == nil ==> acc(content)
func (t *Log) hashContent() (content []byte, err error) {
	if e := t.computeHash(); e != nil {
		err = e
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
	}
	return
}

// @ preserves acc(t.Inv())
// @ ensures err == nil ==> unfolding acc(t.Inv()) in t.value != nil
func (t *Log) computeHash() (err error) {
	// @ unfold acc(t.Inv())
	if t.left == nil || t.right == nil {
		if t.value == nil {
			err = errors.New("missing value for incomplete subtree or leaf")
		} // else all good
	} else {
		// @ assert t.left != nil && t.right != nil // test invariant
		if t.value == nil {
			if leftContent, e := t.left.hashContent(); e != nil {
				err = e
			} else if rightContent, e := t.right.hashContent(); e != nil {
				err = e
			} else {
				a /*@@@*/ := sha256.Sum256(append( /*@ perm(1/2), @*/ leftContent, rightContent...) /*@, perm(1/2) @*/)
				t.value = &a
			}
		} // else all good
	}
	// @ fold acc(t.Inv())
	return
}

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p) && unfolding acc(t.Inv(), p) in 1 <= t.size
// @ ensures commitment != nil ==> acc(commitment)
func (t *Log) GetLeafHash(index uint64 /*@, ghost p perm @*/) (commitment *[sha256.Size]byte, err error) {
	// @ unfold acc(t.Inv(), p)
	if t.size == 1 {
		var c /*@@@*/ [sha256.Size]byte
		if t.value != nil {
			c = *t.value
		}
		commitment = &c
	} else if t.left == nil || t.right == nil {
		// Technically, we do not need both subtrees, but we check the invariant
		// that every node should be a leaf or have two children
		err = errors.New("missing subtree")
	} else {
		// @ unfold acc(t.left.Inv(), p)
		if index < t.left.size {
			// @ fold acc(t.left.Inv(), p)
			commitment, err = t.left.GetLeafHash(index /*@, p @*/)
		} else {
			commitment, err = t.right.GetLeafHash(index - t.left.size /*@, p @*/)
			// @ fold acc(t.left.Inv(), p)
		}
	}
	// @ fold acc(t.Inv(), p)
	return
}

// @ requires noPerm < p
// @ preserves t != nil ==> acc(t.Inv(), p)
// @ ensures 0 <= r
// @ ensures (t != nil) == (1 <= r)
func (t *Log) GetSize( /*@ ghost p perm @*/ ) (r uint64) {
	if t == nil {
		r = 0
	} else {
		r = /*@ unfolding acc(t.Inv(), p) in @*/ t.size
	}
	return
}

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p)
func (t *Log) GetRoot( /*@ ghost p perm @*/ ) *[sha256.Size]byte {
	return /*@ unfolding acc(t.Inv(), p) in @*/ t.value
}

// @ preserves acc(t.Inv())
// @ requires elems != nil && forall i int :: {elems[i]} 0 <= i && i < len(elems) ==> acc(&elems[i]) && acc(elems[i])
// @ ensures err == nil ==> r != nil && forall i int :: {r[i]} 0 <= i && i < len(r) ==> acc(&r[i]) && acc(r[i])
func (t *Log) proofFromPruned(cacheSize uint64, elems []*proofs.NodeValue) (r []*proofs.NodeValue, err error) {
	// @ unfold acc(t.Inv())
	if t.left == nil || t.right == nil {
		if t.value == nil {
			err = errors.New("tree missing hash value")
		} else if cacheSize < t.index+t.size {
			// Only include sub trees that the client cannot compute
			v /*@@@*/ := *t.value
			r = append( /*@ perm(1/2), @*/ elems, &v)
		} else {
			// Client can compute this subtree; do not include
			r = elems
		}
	} else if elems, err = t.left.proofFromPruned(cacheSize, elems); err != nil {
	} else {
		r, err = t.right.proofFromPruned(cacheSize, elems)
	}
	// @ fold acc(t.Inv())
	return
}

// @ preserves acc(t.Inv())
// @ ensures err == nil ==> acc(prf.Inv())
func (t *Log) ProofFromPruned(cacheSize uint64) (prf *proofs.InclusionProof, err error) {
	if elems, e := t.proofFromPruned(cacheSize, []*proofs.NodeValue{}); e != nil {
		err = e
	} else {
		incPrf /*@@@*/ := proofs.InclusionProof{
			Elements: elems,
		}
		// @ fold acc(incPrf.Inv())
		prf = &incPrf
	}
	return
}
