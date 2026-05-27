package trees

import (
	"bytes"
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type prefixLeaf struct {
	value      [sha256.Size]byte
	vrfOutput  []byte
	commitment *[sha256.Size]byte
}

/*@
pred (l *prefixLeaf) Inv() {
	acc(l) &&
	(l.vrfOutput != nil ==> acc(l.vrfOutput)) &&
	(l.commitment != nil ==> acc(l.commitment))
}
@*/

// @ requires noPerm < p
// @ preserves pl != nil ==> acc(pl.Inv(), p)
// @ ensures pl != nil ==> l != nil && acc(l.Inv())
func commitmentLeaf(pl *proofs.PrefixLeaf /*@, ghost p perm @*/) (l *prefixLeaf) {
	if pl == nil {
		return nil
	}
	// @ unfold acc(pl.Inv(), p)

	// Spec: leaf.value = Hash(0x02 || vrf_output || commitment)
	input := []byte{0x02}
	input = append( /*@ p, @*/ input, pl.Vrf_output...)
	input = append( /*@ p, @*/ input, utils.FromDigest(*pl.Commitment)...)
	value := sha256.Sum256(input /*@, perm(1/2) @*/)
	c /*@@@*/ := *pl.Commitment
	// @ assert c[0] == pl.Commitment[0]
	// The above assert is required so that gobra realizes the assert below.
	// @ assert &c != pl.Commitment
	// @ assert acc(&c)
	l_ /*@@@*/ := prefixLeaf{
		value: value,
		// TODO: Could not use pl.Vrf_output[:], so opted for append.
		// Folding pl.Inv() failed on using [:]
		vrfOutput:  append( /*@ p, @*/ []byte{}, pl.Vrf_output...),
		commitment: &c,
	}
	// @ fold acc(l_.Inv())
	// @ fold acc(pl.Inv(), p)
	return &l_
}

type Prefix struct {
	leaf  *prefixLeaf
	left  *Prefix
	right *Prefix
}

// The invariant intentionally only provides read access to the leaf as we will
// typically create the leaf from a read-only data-structure. This simplifies
// memory safety proofs.
/*@
pred (t *Prefix) Inv() {
	acc(t) &&
	(t.leaf != nil ==> acc(t.leaf.Inv())) &&
	(t.left != nil ==> acc(t.left.Inv())) &&
	(t.right != nil ==> acc(t.right.Inv()))
}
@*/

/*@
pred PrefixesInv(ts []*Prefix) {
	forall i int :: {ts[i]} 0 <= i && i < len(ts) ==> acc(&ts[i]) && acc(ts[i].Inv())
}
@*/

// @ ensures acc(t.Inv())
func mkTree() (t *Prefix) {
	tmp_t /*@@@*/ := Prefix{}
	// @ fold tmp_t.Inv()
	return &tmp_t
}

// @ ensures acc(t.Inv())
func nodeValueLeaf(nodeValue proofs.NodeValue) (t *Prefix) {
	l /*@@@*/ := prefixLeaf{
		value:      nodeValue,
		vrfOutput:  nil,
		commitment: nil,
	}
	// @ fold l.Inv()
	tr /*@@@*/ := Prefix{
		leaf:  &l,
		left:  nil,
		right: nil,
	}
	// @ fold tr.Inv()
	return &tr
}

// @ requires 0 <= depth && depth <= len(steps)
// @ requires acc(t.Inv())
// @ requires leaf != nil ==> acc(leaf.Inv())
// @ preserves acc(steps)
// @ ensures acc(t.Inv())
func (t *Prefix) setLeaf(steps []bool, depth int, leaf *prefixLeaf) {
	// @ unfold t.Inv()
	if depth == 0 {
		t.leaf = leaf
		t.left = nil
		t.right = nil
	} else {
		stepsRec := steps[1:]
		// @ assert forall i int :: {&stepsRec[i]} 0 <= i && i < len(stepsRec) ==> &stepsRec[i] == &steps[i+1]
		if steps[0] {
			if t.right == nil {
				t.right = mkTree()
			}
			t.right.setLeaf(stepsRec, depth-1, leaf)
		} else {
			if t.left == nil {
				t.left = mkTree()
			}
			t.left.setLeaf(stepsRec, depth-1, leaf)
		}
	}
	// @ fold t.Inv()
}

// @ requires noPerm < p
// @ requires acc(proofs.NodeValuesInv(elements), p)
// @ preserves acc(t.Inv())
// @ ensures err == nil ==> acc(proofs.NodeValuesInv(es), p)
func (t *Prefix) fill(elements []*proofs.NodeValue /*@, ghost p perm @*/) (es []*proofs.NodeValue, err error) {
	// @ unfold acc(t.Inv())
	// @ defer fold acc(t.Inv())
	if t.leaf != nil {
		return elements, nil
	}

	var esL []*proofs.NodeValue
	if t.left != nil {
		if esL, err = t.left.fill(elements /*@, p @*/); err != nil {
			return nil, err
		}
	} else if len(elements) == 0 {
		return nil, errors.New("too few elements")
	} else {
		// @ unfold acc(proofs.NodeValuesInv(elements), p)
		t.left = nodeValueLeaf(*elements[0])
		esL = elements[1:]
		// @ assert forall i int :: {&esL[i]} 0 <= i && i < len(esL) ==> &esL[i] == &elements[i+1]
		// @ fold acc(proofs.NodeValuesInv(esL), p)
	}

	if t.right != nil {
		if es, err = t.right.fill(esL /*@, p @*/); err != nil {
			return nil, err
		}
	} else if len(esL) == 0 {
		return nil, errors.New("too few elements")
	} else {
		// @ unfold acc(proofs.NodeValuesInv(esL), p)
		t.right = nodeValueLeaf(*esL[0])
		es = esL[1:]
		// @ assert forall i int :: {&es[i]} 0 <= i && i < len(es) ==> &es[i] == &esL[i+1]
		// @ fold acc(proofs.NodeValuesInv(es), p)
	}

	return es, nil
}

// @ requires noPerm < p && acc(t.Inv(), p)
// @ ensures err == nil ==> acc(t.Inv(), p)
func (t *Prefix) Value( /*@ ghost p perm @*/ ) (r [sha256.Size]byte, err error) {
	r = [sha256.Size]byte{}
	// @ unfold acc(t.Inv(), p)
	if t.leaf != nil {
		// @ unfold acc(t.leaf.Inv(), p)
		r = t.leaf.value
		// @ fold acc(t.leaf.Inv(), p)
	} else if t.left == nil || t.right == nil {
		return r, errors.New("incomplete tree")
	} else if left, errL := t.left.Value( /*@ p @*/ ); errL != nil {
		return r, errL
	} else if right, errR := t.right.Value( /*@ p @*/ ); errR != nil {
		return r, errR
	} else {
		input := make([]byte, 1+sha256.Size+sha256.Size)
		input[0] = 0x03
		// @ invariant 0 <= i && i <= sha256.Size
		// @ invariant acc(input)
		for i := 0; i < sha256.Size; i++ {
			input[1+i] = left[i]
			input[1+sha256.Size+i] = right[i]
		}
		r = sha256.Sum256(input /*@, perm(1/2) @*/)
	}

	// @ fold acc(t.Inv(), p)
	return r, nil
}

// @ requires noPerm < p
// @ preserves acc(searchKey, p)
// @ requires acc(t.Inv(), p)
// @ ensures acc(t.Inv(), p/2)
// @ ensures ok ==> acc(l.Inv(), p/2)
func (t *Prefix) getLeaf(searchKey []bool /*@, ghost p perm @*/) (l *prefixLeaf, ok bool) {
	// @ unfold acc(t.Inv(), p)
	// @ defer fold acc(t.Inv(), p/2)
	if t.leaf != nil || len(searchKey) == 0 {
		return t.leaf, t.leaf != nil
	} else {
		rec := searchKey[1:]
		// @ assert forall i int :: {&rec[i]} 0 <= i && i < len(rec) ==> &rec[i] == &searchKey[i+1]
		if searchKey[0] {
			if t.right == nil {
				return nil, false
			}
			return t.right.getLeaf(rec /*@, p @*/)
		} else {
			if t.left == nil {
				return nil, false
			}
			return t.left.getLeaf(rec /*@, p @*/)
		}
	}
}

// @ requires noPerm < p
// @ requires acc(t.Inv(), p)
// @ preserves acc(searchKey, p)
// @ ensures acc(t.Inv(), p/2)
// @ ensures r != nil ==> acc(r, p/2)
func (t *Prefix) Search(searchKey []byte /*@, ghost p perm @*/) (r *[sha256.Size]byte, ok bool) {
	// TODO: Cannot return r == nil && ok
	if leaf, ok := t.getLeaf(utils.Bits(searchKey /*@, p @*/) /*@, p @*/); !ok {
		return nil, false
	} else {
		// @ unfold acc(leaf.Inv(), p/2)
		if leaf.vrfOutput == nil {
			return nil, false
		} else if leaf.commitment == nil {
			return nil, false
		} else {
			c /*@@@*/ := *leaf.commitment
			return &c, bytes.Equal(leaf.vrfOutput, searchKey /*@, p/2, p @*/)
		}
		// @ fold acc(leaf.Inv(), p/2)
	}
}

// @ requires noPerm < p
// @ requires acc(prf.Inv(), p)
// @ ensures err == nil ==> acc(tree.Inv())
func MkPrefix(prf *proofs.PrefixProof /*@, ghost p perm @*/) (tree *Prefix, err error) {
	tree = &Prefix{}
	// @ fold acc(tree.Inv())

	// @ invariant acc(tree.Inv())
	// @ invariant acc(prf.Inv(), p)
	// @ invariant 0 <= i && i <= len(unfolding acc(prf.Inv(), p) in prf.Results)
	for i := 0; i < len( /*@ unfolding acc(prf.Inv(), p) in @*/ prf.Results); i++ {
		// @ unfold acc(prf.Inv(), p)
		// @ unfold acc(proofs.PrefixSearchResultsInv(prf.Results), p)
		// @ unfold acc(prf.Results[i].Inv(), p)
		result := prf.Results[i]
		// TODO: Should verify `result.result_type`, but I skip this for now as it seems to
		// be redundant information

		var searchKey []byte
		// @ unfold acc(result.Leaf.Inv(), p)
		copy(searchKey, result.Leaf.Vrf_output /*@, p @*/)
		// @ fold acc(result.Leaf.Inv(), p)
		searchKeyBits := utils.Bits(searchKey /*@, perm(1/2) @*/)

		// @ unfold acc(result.Leaf.Inv(), p)
		commitment /*@@@*/ := *result.Leaf.Commitment // Copy commitment
		// @ fold acc(result.Leaf.Inv(), p)
		l /*@@@*/ := proofs.PrefixLeaf{Vrf_output: searchKey, Commitment: &commitment}
		// @ fold acc((&l).Inv(), p)
		// @ assume 0 <= result.Depth && result.Depth <= 255 // help gobra with uint
		// @ assume int(result.Depth) <= len(searchKeyBits) // TODO: make invariant
		tree.setLeaf(searchKeyBits, int(result.Depth), commitmentLeaf(&l /*@, p @*/))

		// @ fold acc(prf.Results[i].Inv(), p)
		// @ fold acc(proofs.PrefixSearchResultsInv(prf.Results), p)
		// @ fold acc(prf.Inv(), p)
	}

	// @ unfold acc(prf.Inv(), p)
	if remaining, err := tree.fill(prf.Elements /*@, p @*/); err != nil {
		return nil, err
	} else if len(remaining) > 0 {
		return nil, errors.New("too many elements provided")
	} else {
		return tree, nil
	}
}
