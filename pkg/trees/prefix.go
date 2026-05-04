package trees

import (
	"bytes"
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

type PrefixTree interface {
	GetRoot() [sha256.Size]byte
	GetCommitment(label []byte, version uint64) (*[sha256.Size]byte, error)
}

type prefixLeaf struct {
	value      [sha256.Size]byte
	vrfOutput  *[sha256.Size]byte
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
// @ preserves pl != nil ==> acc(pl, p)
// @ ensures pl != nil ==> l != nil
// @ ensures l != nil ==> acc(l.Inv(), p)
func commitmentLeaf(pl *proofs.PrefixLeaf /*@, ghost p perm @*/) (l *prefixLeaf) {
	if pl == nil {
		return nil
	}

	// Spec: leaf.value = Hash(0x01 || vrf_output || commitment)
	input := []byte{0x01}
	input = append( /*@ perm(1), @*/ input, utils.FromDigest(pl.Vrf_output)...)
	input = append( /*@ perm(1), @*/ input, utils.FromDigest(pl.Commitment)...)
	value := sha256.Sum256(input /*@, perm(1/2) @*/)
	o /*@@@*/ := pl.Vrf_output
	c /*@@@*/ := pl.Commitment
	l_ /*@@@*/ := prefixLeaf{
		value:      value,
		vrfOutput:  &o,
		commitment: &c,
	}
	// @ fold l_.Inv()
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
	(t.leaf != nil ==> acc(t.leaf.Inv(), _)) &&
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
// @ preserves acc(steps)
// @ preserves leaf != nil ==> acc(leaf.Inv(), _)
// @ ensures acc(t.Inv())
func (t *prefixTree) insertLeaf(steps []bool, depth int, leaf *prefixLeaf) {
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
			t.right.insertLeaf(stepsRec, depth-1, leaf)
		} else {
			if t.left == nil {
				t.left = mkTree()
			}
			t.left.insertLeaf(stepsRec, depth-1, leaf)
		}
	}
	// @ fold t.Inv()
}

// @ requires acc(t.Inv())
// @ requires acc(elements, _)
// @ ensures err == nil ==> acc(t.Inv()) && acc(es, _)
func (t *prefixTree) fill(elements []proofs.NodeValue) (es []proofs.NodeValue, err error) {
	// @ unfold t.Inv()
	if t.leaf != nil {
		// @ fold t.Inv()
		return elements, nil
	}

	var esL []proofs.NodeValue
	if t.left != nil {
		if esL, err = t.left.fill(elements); err != nil {
			return nil, err
		}
	} else if len(elements) == 0 {
		return nil, errors.New("too few elements")
	} else {
		t.left = nodeValueLeaf(elements[0])
		esL = elements[1:]
		// @ assert forall i int :: {&esL[i]} 0 <= i && i < len(esL) ==> &esL[i] == &elements[i+1]
	}

	if t.right != nil {
		if es, err = t.right.fill(esL); err != nil {
			return nil, err
		}
	} else if len(esL) == 0 {
		return nil, errors.New("too few elements")
	} else {
		t.right = nodeValueLeaf(esL[0])
		es = esL[1:]
		// @ assert forall i int :: {&es[i]} 0 <= i && i < len(es) ==> &es[i] == &esL[i+1]
	}

	// @ fold t.Inv()
	return es, nil
}

// @ requires noPerm < p && acc(t.Inv(), p)
// @ ensures err == nil ==> acc(t.Inv(), p)
func (t *prefixTree) value( /*@ ghost p perm @*/ ) (r [sha256.Size]byte, err error) {
	r = [sha256.Size]byte{}
	// @ unfold acc(t.Inv(), p)
	if t.leaf != nil {
		// @ unfold acc(t.leaf.Inv(), _)
		r = t.leaf.value
		// @ fold acc(t.leaf.Inv(), _)
	} else if t.left == nil || t.right == nil {
		return r, errors.New("incomplete tree")
	} else if left, errL := t.left.value( /*@ p @*/ ); errL != nil {
		return r, errL
	} else if right, errR := t.right.value( /*@ p @*/ ); errR != nil {
		return r, errR
	} else {
		input := make([]byte, 1+sha256.Size+sha256.Size)
		input[0] = 0x02
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

// @ preserves acc(searchKey, _)
// @ requires acc(t.Inv(), _)
// @ ensures ok ==> acc(t.Inv(), _) && acc(l.Inv(), _)
func (t *prefixTree) getLeaf(searchKey []bool) (l *prefixLeaf, ok bool) {
	// @ unfold acc(t.Inv(), _)
	if t.leaf != nil || len(searchKey) == 0 {
		return t.leaf, t.leaf != nil
	} else {
		rec := searchKey[1:]
		// @ assert forall i int :: {&rec[i]} 0 <= i && i < len(rec) ==> &rec[i] == &searchKey[i+1]
		if searchKey[0] {
			if t.right == nil {
				return nil, false
			}
			return t.right.getLeaf(rec)
		} else {
			if t.left == nil {
				return nil, false
			}
			return t.left.getLeaf(rec)
		}
	}
}

// @ preserves acc(t.Inv(), _)
// @ ensures r != nil ==> acc(r, _)
func (t *prefixTree) search(searchKey [sha256.Size]byte) (r *[sha256.Size]byte, ok bool) {
	if leaf, ok := t.getLeaf(utils.Bits(searchKey)); !ok {
		return nil, false
	} else {
		// @ unfold acc(leaf.Inv(), _)
		if leaf.vrfOutput == nil {
			return nil, false
		} else {
			return leaf.commitment, *leaf.vrfOutput == searchKey
		}
	}
}

type prefixDict struct {
	root       [sha256.Size]byte
	tree       *prefixTree
	label      []byte
	vrfOutputs map[uint64][sha256.Size]byte
}

/*@
// Permissions to fields of prefixDict are intentionally wildcards because
// we only require read operations after construction. Exception is for label
// because that will be passed to stdlib which preserves exact permissions.
pred (d prefixDict) Inv(p perm) {
	noPerm < p && acc(d.tree.Inv(), _) && acc(d.label, p) && acc(d.vrfOutputs, _)
}
@*/

// @ requires 0 <= version
// @ requires noPerm < p
// @ preserves acc(label, p) && acc(prf.Inv(), _) && acc(fullLadder, p)
// @ preserves forall i int :: 0 <= i && i < len(fullLadder) ==> acc(fullLadder[i].Inv(), p)
// @ ensures err == nil ==> acc(d.Inv(p))
func Dict(label []byte, version uint64, prf proofs.PrefixProof, fullLadder []proofs.BinaryLadderStep /*@, ghost p perm @*/) (d prefixDict, err error) {
	// @ ghost var idx int
	steps /*@, idx @*/ := proofs.FullBinaryLadderSteps(version /*@, version @*/)
	if len(steps) != len(fullLadder) || len(steps) != len(prf.Results) {
		return prefixDict{}, errors.New("not enough ladder steps or prefix search results")
	}

	tree := &prefixTree{}
	// @ fold tree.Inv()
	vrfOutputs := make(map[uint64][32]byte, len(steps))

	// @ unfold acc(prf.Inv(), _)
	// @ unfold proofs.BinaryLadderInv(steps)

	// @ invariant tree.Inv()
	// @ invariant 0 <= i && i <= len(fullLadder)
	// @ invariant len(steps) == len(fullLadder) && len(fullLadder) == len(prf.Results)
	// @ invariant acc(label, p) && acc(steps) && acc(proofs.PrefixSearchResultsInv(prf.Results), _) && acc(prf.Elements, _) && acc(vrfOutputs) && acc(fullLadder, p)
	// @ invariant forall i int :: 0 <= i && i < len(fullLadder) ==> acc(fullLadder[i].Inv(), p)
	for i := 0; i < len(fullLadder); i++ {
		// @ unfold acc(proofs.PrefixSearchResultsInv(prf.Results), _)
		ladderVersion := steps[i]
		leafData := fullLadder[i]
		result := prf.Results[i]
		// TODO: Should verify `result.result_type`, but I skip this for now as it seems to
		// be redundant information

		// @ unfold acc(leafData.Inv(), p)
		// TODO: Use server public key
		if searchKey, ok := crypto.VRF_verify(nil, label, version, leafData.Proof /*@, p @*/); !ok {
			// @ fold acc(proofs.PrefixSearchResultsInv(prf.Results), _)
			// @ fold acc(prf.Inv(), _)
			// @ fold acc(leafData.Inv(), p)
			return prefixDict{}, errors.New("VRF verification failed")
		} else {
			vrfOutputs[ladderVersion] = searchKey
			searchKeyBits := utils.Bits(searchKey)
			var toInsert *prefixLeaf
			if ladderVersion <= version {
				toInsert = commitmentLeaf(&proofs.PrefixLeaf{Vrf_output: searchKey, Commitment: leafData.Commitment} /*@, p @*/)
			} else {
				// @ unfold acc(result.Inv(), p)
				toInsert = commitmentLeaf(result.Leaf /*@, p @*/)
				// @ fold acc(result.Inv(), p)
			}
			// TODO: Express as invariant or enhance gobra
			// @ assume 0 <= result.Depth && result.Depth <= 255
			tree.insertLeaf(searchKeyBits, int(result.Depth), toInsert)
		}
		// @ fold acc(leafData.Inv(), p)
		// @ fold acc(proofs.PrefixSearchResultsInv(prf.Results), _)
	}

	remaining, err := tree.fill(prf.Elements)
	// @ fold acc(prf.Inv(), _)
	if len(remaining) > 0 {
		return d, errors.New("too many elements provided")
	} else if err != nil {
		return d, err
	} else if root, err := tree.value( /*@ perm(1/2) @*/ ); err != nil {
		return d, err
	} else {
		// @ unfold tree.Inv()
		d = prefixDict{
			label:      label,
			vrfOutputs: vrfOutputs,
			tree:       tree,
			root:       root,
		}
		// @ fold tree.Inv()
		// @ fold d.Inv(p)
		return d, nil
	}
}

// @ preserves acc(d.Inv(p))
func (d prefixDict) GetRoot( /*@ ghost p perm @*/ ) [sha256.Size]byte {
	return d.root
}

// @ requires noPerm < p
// @ preserves acc(d.Inv(p))
// @ preserves acc(label, p)
// @ ensures r != nil ==> acc(r, _)
func (d prefixDict) GetCommitment(label []byte, version uint64 /*@, ghost p perm @*/) (r *[sha256.Size]byte, err error) {
	// @ unfold d.Inv(p)
	// @ defer fold d.Inv(p)
	r = nil
	if !bytes.Equal(label, d.label /*@, p, p @*/) {
		return r, errors.New("wrong label")
	} else if searchKey, ok := d.vrfOutputs[version]; !ok {
		return r, errors.New("no proof for version")
	} else {
		if r, ok := d.tree.search(searchKey); ok {
			return r, nil
		} else {
			return nil, nil
		}
	}
}
