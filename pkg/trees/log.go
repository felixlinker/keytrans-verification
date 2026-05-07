package trees

import (
	"crypto/sha256"
	"errors"
)

type LogTree interface {
	GetSize() uint64
	GetRoot() [sha256.Size]byte
	GetLeaf(index uint64) ([sha256.Size]byte, error)
	FullSubtrees() [][sha256.Size]byte
	FrontierCommitments() []*[sha256.Size]byte
}

type logTreeLeaf struct {
	value      [sha256.Size]byte
	commitment *[sha256.Size]byte
}

/*@
pred (l *logTreeLeaf) Inv() {
	acc(l) && (l.commitment != nil ==> acc(l.commitment))
}
@*/

type logTree struct {
	size  uint64
	value [sha256.Size]byte
	leaf  *logTreeLeaf
	left  *logTree
	right *logTree
}

/*@
pred (t *logTree) Inv() {
	acc(t) &&
	(t.leaf != nil ==> acc(t.leaf.Inv())) &&
	(t.left != nil ==> acc(t.left.Inv())) &&
	(t.right != nil ==> acc(t.right.Inv()))
}
@*/

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p)
func (t *logTree) GetLeaf(index uint64 /*@, ghost p perm @*/) (commitment [sha256.Size]byte, err error) {
	// @ unfold acc(t.Inv(), p)
	// @ defer fold acc(t.Inv(), p)
	if t.size == 1 {
		if t.leaf == nil {
			return commitment, errors.New("missing leaf")
		} else {
			// @ unfold acc(t.leaf.Inv(), p)
			// @ defer fold acc(t.leaf.Inv(), p)
			if t.leaf.commitment == nil {
				return commitment, errors.New("missing commitment")
			} else {
				return *t.leaf.commitment, nil
			}
		}
	} else if t.left == nil || t.right == nil {
		// Technically, we do not need both subtrees, but we check the invariant
		// that every node should be a leaf or have two children
		return commitment, errors.New("missing subtree")
	} else {
		// @ unfold acc(t.left.Inv(), p)
		if index < t.left.size {
			// @ fold acc(t.left.Inv(), p)
			return t.left.GetLeaf(index /*@, p @*/)
		} else {
			// @ defer fold acc(t.left.Inv(), p)
			return t.right.GetLeaf(index - t.left.size /*@, p @*/)
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
func (t *logTree) GetRoot( /*@ ghost p perm @*/ ) [sha256.Size]byte {
	return /*@ unfolding acc(t.Inv(), p) in @*/ t.value
}

// TODO: ensure that all elements of r are non-nil, but I keep running into
// gobra walls. Initially, I had planned to have the return type be
// [][sha256.Size]byte

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p)
// @ ensures 0 < len(r) && acc(r)
func (t *logTree) FullSubtrees( /*@ ghost p perm @*/ ) (r []*[sha256.Size]byte) {
	// @ unfold acc(t.Inv(), p)
	// @ defer fold acc(t.Inv(), p)
	if t.left == nil || t.right == nil {
		h /*@@@*/ := t.value
		return []*[sha256.Size]byte{&h}
	} else {
		// @ unfold acc(t.left.Inv(), p)
		// @ defer fold acc(t.left.Inv(), p)
		rec := t.right.FullSubtrees( /*@ p @*/ )
		h /*@@@*/ := t.left.value
		r = []*[sha256.Size]byte{&h}
		return append( /*@ writePerm, @*/ r, rec...)
	}
}
