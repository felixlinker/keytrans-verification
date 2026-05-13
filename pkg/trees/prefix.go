package trees

import (
	"bytes"
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
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

type prefixTree struct {
	leaf  *prefixLeaf
	left  *prefixTree
	right *prefixTree
}

// The invariant intentionally only provides read access to the leaf as we will
// typically create the leaf from a read-only data-structure. This simplifies
// memory safety proofs.
/*@
pred (t *prefixTree) Inv() {
	acc(t) &&
	(t.leaf != nil ==> acc(t.leaf.Inv())) &&
	(t.left != nil ==> acc(t.left.Inv())) &&
	(t.right != nil ==> acc(t.right.Inv()))
}
@*/

// @ ensures acc(t.Inv())
func mkTree() (t *prefixTree) {
	tmp_t /*@@@*/ := prefixTree{}
	// @ fold tmp_t.Inv()
	return &tmp_t
}

// @ ensures acc(t.Inv())
func nodeValueLeaf(nodeValue proofs.NodeValue) (t *prefixTree) {
	l /*@@@*/ := prefixLeaf{
		value:      nodeValue,
		vrfOutput:  nil,
		commitment: nil,
	}
	// @ fold l.Inv()
	tr /*@@@*/ := prefixTree{
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
func (t *prefixTree) setLeaf(steps []bool, depth int, leaf *prefixLeaf) {
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
func (t *prefixTree) fill(elements []*proofs.NodeValue /*@, ghost p perm @*/) (es []*proofs.NodeValue, err error) {
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
func (t *prefixTree) value( /*@ ghost p perm @*/ ) (r [sha256.Size]byte, err error) {
	r = [sha256.Size]byte{}
	// @ unfold acc(t.Inv(), p)
	if t.leaf != nil {
		// @ unfold acc(t.leaf.Inv(), p)
		r = t.leaf.value
		// @ fold acc(t.leaf.Inv(), p)
	} else if t.left == nil || t.right == nil {
		return r, errors.New("incomplete tree")
	} else if left, errL := t.left.value( /*@ p @*/ ); errL != nil {
		return r, errL
	} else if right, errR := t.right.value( /*@ p @*/ ); errR != nil {
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
func (t *prefixTree) getLeaf(searchKey []bool /*@, ghost p perm @*/) (l *prefixLeaf, ok bool) {
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
func (t *prefixTree) search(searchKey []byte /*@, ghost p perm @*/) (r *[sha256.Size]byte, ok bool) {
	if leaf, ok := t.getLeaf(utils.Bits(searchKey /*@, p @*/) /*@, p @*/); !ok {
		return nil, false
	} else {
		// @ unfold acc(leaf.Inv(), p/2)
		if leaf.vrfOutput == nil {
			return nil, false
		} else {
			return leaf.commitment, bytes.Equal(leaf.vrfOutput, searchKey /*@, p/2, p @*/)
		}
	}
}

type prefixDict struct {
	root       *[sha256.Size]byte
	tree       *prefixTree
	label      []byte
	vrfOutputs map[uint64][]byte
}

/*@
pred VOInv(outs map[uint64][]byte) {
	acc(outs) && (forall k uint64 :: k elem outs ==> acc(outs[k]))
}

// Permissions to fields of prefixDict are intentionally wildcards because
// we only require read operations after construction. Exception is for label
// because that will be passed to stdlib which preserves exact permissions.
pred (d *prefixDict) Inv() {
	acc(d) && acc(d.root) && acc(d.tree.Inv()) && acc(d.label) && acc(VOInv(d.vrfOutputs))
}
@*/

// @ requires noPerm < p
// @ requires 0 <= version
// @ preserves acc(label, p) && acc(pk, p) && acc(proofs.BinaryLadderStepsInv(fullLadder), p)
// @ ensures err == nil ==> acc(VOInv(vrfOutputs))
func verifyVRFOutputs(label []byte, version uint64, pk []byte, fullLadder []*proofs.BinaryLadderStep /*@, ghost p perm @*/) (vrfOutputs map[uint64][]byte, err error) {
	steps /*@, idx @*/ := proofs.FullBinaryLadderSteps(version /*@, version @*/)

	if len(steps) != len(fullLadder) {
		return nil, errors.New("wrong number of binary ladder steps")
	}

	vrfOutputs = make(map[uint64][]byte, len(steps))
	// @ fold acc(VOInv(vrfOutputs))
	// @ unfold acc(proofs.BinaryLadderInv(steps))

	// @ invariant 0 <= i && i <= len(fullLadder)
	// @ invariant acc(label, p) && acc(pk, p) && acc(steps) && acc(VOInv(vrfOutputs))
	// @ invariant len(steps) == len(fullLadder)
	// @ invariant acc(proofs.BinaryLadderStepsInv(fullLadder), p)
	for i := 0; i < len(fullLadder); i++ {
		// @ unfold acc(proofs.BinaryLadderStepsInv(fullLadder), p)
		// @ unfold acc((&fullLadder[i]).Inv(), p)
		ladderVersion := steps[i]
		leafData := fullLadder[i]

		if searchKey, ok := crypto.VRF_verify(pk, label, ladderVersion, leafData.Proof /*@, p @*/); !ok {
			// @ fold acc((&fullLadder[i]).Inv(), p)
			// @ fold acc(proofs.BinaryLadderStepsInv(fullLadder), p)
			return nil, errors.New("VRF verification failed")
		} else {
			// @ unfold acc(VOInv(vrfOutputs))
			// Copy searchKey so that we retain full access to the map
			vrfOutputs[ladderVersion] = append( /*@ perm(1), @*/ []byte{}, searchKey...)
			// @ fold acc(VOInv(vrfOutputs))
		}
		// @ fold acc((&fullLadder[i]).Inv(), p)
		// @ fold acc(proofs.BinaryLadderStepsInv(fullLadder), p)
	}

	return vrfOutputs, nil
}

// @ requires noPerm < p
// @ requires 0 <= version
// @ requires acc(prf.Inv(), p)
// @ preserves acc(VOInv(vrfOutputs), p)
// @ ensures err == nil ==> acc(tree.Inv())
func buildTree(version uint64, prf *proofs.PrefixProof, vrfOutputs map[uint64][]byte /*@, ghost p perm @*/) (tree *prefixTree, err error) {
	// @ ghost var idx int
	steps /*@, idx @*/ := proofs.FullBinaryLadderSteps(version /*@, version @*/)
	// @ unfold acc(proofs.BinaryLadderInv(steps))
	if len(steps) != len( /*@ unfolding acc(prf.Inv(), p) in @*/ prf.Results) {
		return nil, errors.New("not enough ladder steps or prefix search results")
	}

	tree = &prefixTree{}
	// @ fold acc(tree.Inv())

	// @ invariant acc(tree.Inv())
	// @ invariant acc(steps) && acc(prf.Inv(), p) && acc(VOInv(vrfOutputs), p)
	// @ invariant len(steps) == len(unfolding acc(prf.Inv(), p) in prf.Results)
	// @ invariant 0 <= i && i <= len(steps)
	for i := 0; i < len(steps); i++ {
		// @ unfold acc(prf.Inv(), p)
		// @ unfold acc(proofs.PrefixSearchResultsInv(prf.Results), p)
		// @ unfold acc(prf.Results[i].Inv(), p)
		ladderVersion := steps[i]
		result := prf.Results[i]
		// TODO: Should verify `result.result_type`, but I skip this for now as it seems to
		// be redundant information

		var searchKey []byte
		if ladderVersion <= version {
			// @ unfold acc(VOInv(vrfOutputs), p)
			if k, ok := vrfOutputs[ladderVersion]; !ok {
				// @ fold acc(VOInv(vrfOutputs), p)
				// @ fold acc(prf.Results[i].Inv(), p)
				// @ fold acc(proofs.PrefixSearchResultsInv(prf.Results), p)
				// @ fold acc(prf.Inv(), p)
				return nil, errors.New("missing vrf output")
			} else {
				copy(searchKey, k /*@, p @*/)
			}
			// @ fold acc(VOInv(vrfOutputs), p)
		} else {
			// @ unfold acc(result.Leaf.Inv(), p)
			copy(searchKey, result.Leaf.Vrf_output /*@, p @*/)
			// @ fold acc(result.Leaf.Inv(), p)
		}
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

// @ requires 0 <= version
// @ requires noPerm < p
// @ requires acc(prf.Inv(), p)
// @ preserves acc(label, p) && acc(pk, p) && acc(proofs.BinaryLadderStepsInv(fullLadder), p)
// @ ensures err == nil ==> acc(d.Inv())
func Dict(label []byte, version uint64, pk []byte, prf *proofs.PrefixProof, fullLadder []*proofs.BinaryLadderStep /*@, ghost p perm @*/) (d *prefixDict, err error) {
	if vrfOutputs, e := verifyVRFOutputs(label, version, pk, fullLadder /*@, p @*/); e != nil {
		return nil, e
	} else if tree, e := buildTree(version, prf, vrfOutputs /*@, p @*/); e != nil {
		return nil, e
	} else if root /*@@@*/, err := tree.value( /*@ perm(1/2) @*/ ); err != nil {
		return nil, err
	} else {
		d /*@@@*/ := prefixDict{
			vrfOutputs: vrfOutputs,
			tree:       tree,
			root:       &root,
		}
		copy(d.label, label /*@, p @*/)
		// @ fold acc((&d).Inv())
		return &d, nil
	}
}

// @ requires noPerm < p
// @ preserves acc(d.Inv(), p)
func (d *prefixDict) GetRoot( /*@ ghost p perm @*/ ) [sha256.Size]byte {
	return /*@ unfolding acc(d.Inv(), p) in @*/ *d.root
}

// @ requires noPerm < p
// @ requires acc(d.Inv(), p)
// @ preserves acc(label, p)
// @ ensures acc(d.Inv(), p/2)
// @ ensures r != nil ==> acc(r, p/2)
func (d *prefixDict) GetCommitment(label []byte, version uint64 /*@, ghost p perm @*/) (r *[sha256.Size]byte, err error) {
	// @ unfold acc(d.Inv(), p)
	// @ unfold acc(VOInv(d.vrfOutputs), p)
	r = nil
	if !bytes.Equal(label, d.label /*@, p, p @*/) {
		// @ fold acc(VOInv(d.vrfOutputs), p)
		// @ fold acc(d.Inv(), p/2)
		return r, errors.New("wrong label")
	} else if searchKey, ok := d.vrfOutputs[version]; !ok {
		// @ fold acc(VOInv(d.vrfOutputs), p)
		// @ fold acc(d.Inv(), p/2)
		return r, errors.New("no proof for version")
	} else if r, ok := d.tree.search(searchKey /*@, p @*/); ok {
		// @ fold acc(VOInv(d.vrfOutputs), p)
		// @ fold acc(d.Inv(), p/2)
		return r, nil
	} else {
		// @ fold acc(VOInv(d.vrfOutputs), p)
		// @ fold acc(d.Inv(), p/2)
		return nil, nil
	}
}
