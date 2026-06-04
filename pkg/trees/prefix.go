package trees

import (
	"bytes"
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/trees/misc"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

type prefixLeaf struct {
	value      [sha256.Size]byte
	searchKey  []byte
	commitment *[sha256.Size]byte
}

/*@
pred (l *prefixLeaf) Inv() {
	acc(l) &&
	(l.searchKey != nil ==> acc(l.searchKey)) &&
	(l.commitment != nil ==> acc(l.commitment))
}
@*/

// @ requires  noPerm < p
// @ preserves pl != nil ==> acc(pl.Inv(), p)
// @ ensures   pl != nil ==> l.Inv()
func commitmentLeaf(pl *proofs.PrefixLeaf /*@, ghost p perm @*/) (l *prefixLeaf) {
	if pl != nil {
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
		l = &prefixLeaf{
			value: value,
			// TODO: Could not use pl.Vrf_output[:], so opted for append.
			// Folding pl.Inv() failed on using [:]
			searchKey:  append( /*@ p, @*/ []byte{}, pl.Vrf_output...),
			commitment: &c,
		}
		// @ fold l.Inv()
		// @ fold acc(pl.Inv(), p)
	}
	return
}

type Prefix struct {
	leaf  *prefixLeaf
	left  *Prefix
	right *Prefix
}

/*@
pred (t *Prefix) Inv() {
	acc(t) &&
	(t.leaf != nil ==> t.leaf.Inv()) &&
	(t.left != nil ==> t.left.Inv()) &&
	(t.right != nil ==> t.right.Inv())
}
@*/

/*@
pred PrefixesInv(ts []*Prefix) {
	forall i int :: {ts[i]} 0 <= i && i < len(ts) ==> acc(&ts[i]) && acc(ts[i].Inv())
}
@*/

// @ ensures t.Inv()
func mkTree() (t *Prefix) {
	t = &Prefix{}
	// @ fold t.Inv()
	return
}

// @ requires noPerm < p
// @ preserves t.Inv()
// @ requires acc(path, p)
// @ requires 0 <= depth
// @ requires leaf.Inv()
func (t *Prefix) insertAtChild(path []bool, depth int, leaf *prefixLeaf /*@, ghost p perm @*/) (err error) {
	// @ unfold t.Inv()
	if depth >= len(path) {
		err = errors.New("path too short for tree depth")
	} else if path[depth] {
		if t.right == nil {
			t.right = mkTree()
		}
		err = t.right.insert(path, depth+1, leaf /*@, p @*/)
	} else {
		if t.left == nil {
			t.left = mkTree()
		}
		err = t.left.insert(path, depth+1, leaf /*@, p @*/)
	}
	// @ fold t.Inv()
	return
}

// @ requires noPerm < p
// @ preserves t.Inv()
// @ requires acc(path, p)
// @ requires 0 <= depth
// @ requires leaf.Inv()
func (t *Prefix) insert(path []bool, depth int, leaf *prefixLeaf /*@, ghost p perm @*/) (err error) {
	// @ unfold t.Inv()
	if t.leaf == nil && t.left == nil && t.right == nil {
		t.leaf = leaf
		// @ fold t.Inv()
	} else if len(path) <= depth {
		// We arrived at the maximum depth; overwrite the respective leaf
		t.leaf = leaf
		// We assume that search keys are all of equal length. We enforce this
		// property by setting the children to nil.
		t.left = nil
		t.right = nil
		// @ fold t.Inv()
	} else {
		// If there already is a leaf, "push it down" into the left or right
		// subtree.
		if t.leaf != nil {
			recLeaf := t.leaf
			t.leaf = nil
			// @ fold t.Inv()

			if /*@ unfolding recLeaf.Inv() in @*/ recLeaf.searchKey == nil {
				err = errors.New("search key error at leaf")
			} else {
				// @ unfold recLeaf.Inv()
				recSearchKey := utils.Bits(recLeaf.searchKey /*@, perm(1/2) @*/)
				// @ fold recLeaf.Inv()
				err = t.insertAtChild(recSearchKey, depth, recLeaf /*@, perm(1/2) @*/)
			}
		}

		if err == nil {
			err = t.insertAtChild(path, depth, leaf /*@, p @*/)
		}
	}
	return
}

// @ preserves t.Inv()
// @ requires leaf.Inv()
func (t *Prefix) Insert(leaf *prefixLeaf) (err error) {
	// @ unfold acc(leaf.Inv(), perm(1/2))
	searchKeyBits := utils.Bits(leaf.searchKey /*@, perm(1/2) @*/)
	// @ fold acc(leaf.Inv(), perm(1/2))
	return t.insert(searchKeyBits, 0, leaf /*@, perm(1/2) @*/)
}

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p)
func (t *Prefix) IsEmpty( /*@ ghost p perm @*/ ) (empty bool) {
	if t == nil {
		empty = true
	} else {
		// @ unfold acc(t.Inv(), p)
		if t.leaf != nil {
			empty = /*@ unfolding acc(t.leaf.Inv(), p) in @*/ t.leaf.searchKey == nil
		} else if t.left == nil && t.right == nil {
			empty = true
		} else {
			empty = t.left.IsEmpty( /*@ p @*/ ) && t.right.IsEmpty( /*@ p @*/ )
		}
		// @ fold acc(t.Inv(), p)
	}
	return
}

// @ ensures t.Inv()
func nodeValueLeaf(nodeValue proofs.NodeValue) (t *Prefix) {
	l := &prefixLeaf{
		value:      nodeValue,
		searchKey:  nil,
		commitment: nil,
	}
	// @ fold l.Inv()
	t = &Prefix{
		leaf:  l,
		left:  nil,
		right: nil,
	}
	// @ fold t.Inv()
	return
}

// @ requires  0 <= depth && depth <= len(steps)
// @ requires  t.Inv() && leaf.Inv()
// @ preserves acc(steps)
// @ ensures   t.Inv()
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

// @ requires  noPerm < p
// @ requires  acc(proofs.NodeValuesInv(elements), p)
// @ preserves t.Inv()
// @ ensures err == nil ==> acc(proofs.NodeValuesInv(es), p)
func (t *Prefix) fill(elements []*proofs.NodeValue /*@, ghost p perm @*/) (es []*proofs.NodeValue, err error) {
	// @ unfold t.Inv()
	if t.leaf != nil {
		es = elements
	} else {
		var esL []*proofs.NodeValue
		if t.left != nil {
			esL, err = t.left.fill(elements /*@, p @*/)
		} else if len(elements) == 0 {
			err = errors.New("too few elements")
		} else {
			// @ unfold acc(proofs.NodeValuesInv(elements), p)
			if !utils.AllZero(*elements[0]) {
				t.left = nodeValueLeaf(*elements[0])
			}
			esL = elements[1:]
			// @ assert forall i int :: {&esL[i]} 0 <= i && i < len(esL) ==> &esL[i] == &elements[i+1]
			// @ fold acc(proofs.NodeValuesInv(esL), p)
		}

		if err == nil {
			if t.right != nil {
				es, err = t.right.fill(esL /*@, p @*/)
			} else if len(esL) == 0 {
				err = errors.New("too few elements")
			} else {
				// @ unfold acc(proofs.NodeValuesInv(esL), p)
				if !utils.AllZero(*esL[0]) {
					t.right = nodeValueLeaf(*esL[0])
				}
				es = esL[1:]
				// @ assert forall i int :: {&es[i]} 0 <= i && i < len(es) ==> &es[i] == &esL[i+1]
				// @ fold acc(proofs.NodeValuesInv(es), p)
			}
		}
	}
	// @ fold t.Inv()
	return
}

// TODO: Write a function that recursively collects a pure map of elements in
// the prefix tree, and proof that value establishes that elements contained in
// both executions must map to the same value if the hash matches.

/*@
ghost
requires  t != nil ==> acc(t.Inv(), _)
ensures   0 <= r
decreases acc(t.Inv(), _)
pure func (t *Prefix) depth() (r uint64) {
	return t == nil ? 0 :
		unfolding acc(t.Inv(), _) in
			let lDepth := t.left == nil ? 0 : t.left.depth() in
			let rDepth := t.right == nil ? 0 : t.right.depth() in
			1 + utils.max(lDepth, rDepth)
}

ghost
requires  t != nil ==> acc(t.Inv(), _)
decreases t.depth()
pure func (t *Prefix) Included() (r seq[seq[bool]]) {
	return (t == nil ?
		// The empty leaf proves inclusion of no prefix
		seq[seq[bool]]{} :
		(unfolding acc(t.Inv(), _) in (t.leaf != nil ?
			(unfolding acc(t.leaf.Inv(), _) in t.leaf.searchKey != nil ?
				seq[seq[bool]]{ utils.Bits_Pure(t.leaf.searchKey) } :
				seq[seq[bool]]{}) :
			(t.left.Included() ++ t.right.Included()))))
}

ghost
requires  t != nil ==> acc(t.Inv(), _)
requires  0 <= depth
decreases t.depth()
pure func (t *Prefix) NotIncludedPrefixes(depth int) (r seq[seq[bool]]) {
	return (t == nil ?
		// The empty leaf proves non-inclusion of every suffix
		seq[seq[bool]]{ seq[bool]{} } :
		(unfolding acc(t.Inv(), _) in (t.leaf != nil ?
			// A leaf proves the non-inclusion of no suffix
			(unfolding acc(t.leaf.Inv(), _) in (t.leaf.searchKey != nil ?
				// No search key proves the non-inclusion of nothing; we are only given a hash
				seq[seq[bool]]{} :
				// A search key proves the non-inclusion of every intermediate infix with the last bit respectively flipped
				utils.FlippedTailsPure(utils.Bits_Pure(t.leaf.searchKey), depth))) :
			(	let left := utils.PrependAll(t.left.NotIncludedPrefixes(depth+1), false) in
				let right := utils.PrependAll(t.right.NotIncludedPrefixes(depth+1), true) in
				left ++ right))))
}

pred NoPrefixMatches(prefixes seq[seq[bool]], values seq[seq[bool]]) {
	forall i, j int :: 0 <= i && i < len(prefixes) && 0 <= j && j < len(values) ==>
		(len(values[j]) < len(prefixes[i]) || prefixes[i] != values[j][:len(prefixes[i])])
}
@*/

// @ requires noPerm < p
// @ requires t != nil ==> acc(t.Inv(), p)
// @ requires low(t.Included())
// @ ensures  t != nil ==> acc(t.Inv(), p)
// // @ ensures low(r) && err == nil ==>
// // @	NoPrefixMatches(rel(t, 0).NotIncludedPrefixes(0), rel(t, 1).Included()) &&
// // @	NoPrefixMatches(rel(t, 1).NotIncludedPrefixes(0), rel(t, 0).Included())
func (t *Prefix) Value( /*@ ghost p perm @*/ ) (r [sha256.Size]byte, err error) {
	r = [sha256.Size]byte{}
	if t != nil {
		// @ unfold acc(t.Inv(), p)
		if t.leaf != nil {
			// @ unfold acc(t.leaf.Inv(), p)
			r = t.leaf.value
			// @ fold acc(t.leaf.Inv(), p)
		} else if t.left == nil && t.right == nil {
			err = errors.New("incomplete tree")
		} else if left, errL := t.left.Value( /*@ p @*/ ); errL != nil {
			err = errL
		} else if right, errR := t.right.Value( /*@ p @*/ ); errR != nil {
			err = errR
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
	}
	return
}

// @ requires  noPerm < p
// @ preserves acc(searchKey, p)
// @ requires  acc(t.Inv(), p)
// @ ensures   acc(t.Inv(), p/2)
// @ ensures   l == nil ==> acc(t.Inv(), p/2)
// @ ensures   l != nil ==> acc(l.Inv(), p/2)
func (t *Prefix) getLeaf(searchKey []bool /*@, ghost p perm @*/) (l *prefixLeaf, ok bool) {
	// @ unfold acc(t.Inv(), p)
	if t.leaf != nil || len(searchKey) == 0 {
		l = t.leaf
		ok = t.leaf != nil
	} else {
		rec := searchKey[1:]
		// @ assert forall i int :: {&rec[i]} 0 <= i && i < len(rec) ==> &rec[i] == &searchKey[i+1]
		if searchKey[0] {
			if t.right == nil {
				l = nil
				ok = true
			} else {
				l, ok = t.right.getLeaf(rec /*@, p @*/)
			}
		} else {
			if t.left == nil {
				l = nil
				ok = true
			} else {
				l, ok = t.left.getLeaf(rec /*@, p @*/)
			}
		}
	}
	// @ fold acc(t.Inv(), l == nil ? p : p/2)
	return
}

// @ requires  noPerm < p
// @ requires  acc(t.Inv(), p)
// @ preserves acc(searchKey, p)
// @ ensures   acc(t.Inv(), p/2)
// @ ensures   r != nil ==> acc(r, p/2)
func (t *Prefix) Search(searchKey []byte /*@, ghost p perm @*/) (r *[sha256.Size]byte, ok bool) {
	// TODO: Cannot return r == nil && ok
	if leaf, leafOk := t.getLeaf(utils.Bits(searchKey /*@, p @*/) /*@, p @*/); !leafOk {
		ok = false
	} else if leaf == nil {
		ok = true
	} else {
		// @ unfold acc(leaf.Inv(), p/2)
		if leaf.searchKey == nil {
			ok = false
		} else if leaf.commitment == nil {
			ok = false
		} else {
			c /*@@@*/ := *leaf.commitment
			r = &c
			ok = bytes.Equal(leaf.searchKey, searchKey /*@, p/2, p @*/)
		}
		// @ fold acc(leaf.Inv(), p/2)
	}
	return
}

// @ requires noPerm < p
// @ requires acc(prf.Inv(), p)
// @ ensures  err == nil ==> tree.Inv()
func MkPrefix(prf *proofs.PrefixProof /*@, ghost p perm @*/) (tree *Prefix, err error) {
	tree = &Prefix{}
	// @ fold tree.Inv()

	// @ invariant tree.Inv()
	// @ invariant acc(prf.Inv(), p)
	// @ invariant 0 <= i && i <= len(unfolding acc(prf.Inv(), p) in prf.Results)
	for i := 0; i < len( /*@ unfolding acc(prf.Inv(), p) in @*/ prf.Results); i++ {
		// @ unfold acc(prf.Inv(), p)
		// @ unfold acc(proofs.PrefixSearchResultsInv(prf.Results), p)
		// @ unfold acc(prf.Results[i].Inv(), p)
		result := prf.Results[i]
		// TODO: Should verify `result.result_type`, but I skip this for now as it seems to
		// be redundant information

		searchKey := make([]byte, len(result.Leaf.Vrf_output))
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
	if remaining, e := tree.fill(prf.Elements /*@, p @*/); e != nil {
		err = e
	} else if len(remaining) > 0 {
		err = errors.New("too many elements provided")
	} // else all good
	return
}

// @ requires noPerm < p
// @ preserves acc(t.Inv())
// @ preserves acc(searchKey, p)
// @ requires 0 <= depth
// @ requires acc(searchKeyPath, p)
func (t *Prefix) prune(searchKey []byte, searchKeyPath []bool, depth int /*@, ghost p perm @*/) (err error) {
	if /*@ unfolding acc(t.Inv()) in @*/ t.leaf != nil {
		// @ unfold acc(t.Inv())
		// @ unfold acc(t.leaf.Inv())
		if t.leaf.searchKey != nil && bytes.Equal(t.leaf.searchKey, searchKey /*@, p, p @*/) {
			t.leaf.searchKey = nil
			t.leaf.commitment = nil
		}
		// @ fold acc(t.leaf.Inv())
		// @ fold acc(t.Inv())
	} else if depth < len(searchKeyPath) {
		if searchKeyPath[depth] {
			// @ unfold acc(t.Inv())
			if t.right != nil {
				err = t.right.prune(searchKey, searchKeyPath, depth+1 /*@, p @*/)
			}
			// @ fold acc(t.Inv())
		} else {
			// @ unfold acc(t.Inv())
			if t.left != nil {
				err = t.left.prune(searchKey, searchKeyPath, depth+1 /*@, p @*/)
			}
			// @ fold acc(t.Inv())
		}

		if err == nil && t.IsEmpty( /*@ perm(1/2) @*/ ) {
			if value, e /*@@@*/ := t.Value( /*@ perm(1/2) @*/ ); e != nil {
				err = e
			} else {
				l /*@@@*/ := prefixLeaf{
					value: value,
				}
				// @ fold acc((&l).Inv())
				// @ unfold acc(t.Inv())
				t.leaf = &l
				t.left = nil
				t.right = nil
				// @ fold acc(t.Inv())
			}
		}
	}
	return
}

// @ requires noPerm < p
// @ preserves acc(t.Inv())
// @ requires acc(utils.BytesSliceInv(searchKeys), p)
func (t *Prefix) Prune(searchKeys [][]byte /*@, ghost p perm @*/) {
	// @ invariant 0 <= i && i <= len(searchKeys)
	// @ invariant acc(t.Inv())
	// @ invariant acc(utils.BytesSliceInv(searchKeys), p)
	for i := 0; i < len(searchKeys); i++ {
		// @ unfold acc(utils.BytesSliceInv(searchKeys), p)
		t.prune(searchKeys[i], utils.Bits(searchKeys[i] /*@, p @*/), 0 /*@, p @*/)
		// @ fold acc(utils.BytesSliceInv(searchKeys), p)
	}
}

// @ ensures acc(prf.Inv())
func emptyTreeProof() (prf *proofs.PrefixProof) {
	val /*@@@*/ := proofs.NodeValue{}
	tmp /*@@@*/ := proofs.PrefixProof{
		Results:  []*proofs.PrefixSearchResult{},
		Elements: []*proofs.NodeValue{&val},
	}
	// @ fold acc(proofs.PrefixSearchResultsInv(tmp.Results))
	// @ fold acc(proofs.NodeValuesInv(tmp.Elements))
	// @ fold acc((&tmp).Inv())
	return &tmp
}

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p)
// @ ensures prf != nil ==> acc(prf.Inv())
func (t *Prefix) proofFromTree(depth uint8 /*@, ghost p perm @*/) (prf *proofs.PrefixProof) {
	// @ unfold acc(t.Inv(), p)
	if t.leaf != nil {
		tmp /*@@@*/ := proofs.PrefixProof{
			Results:  []*proofs.PrefixSearchResult{},
			Elements: []*proofs.NodeValue{},
		}
		// @ fold acc(proofs.PrefixSearchResultsInv(tmp.Results))
		// @ fold acc(proofs.NodeValuesInv(tmp.Elements))
		// @ unfold acc(t.leaf.Inv(), p)
		if t.leaf.searchKey != nil && t.leaf.commitment != nil {
			comm /*@@@*/ := *t.leaf.commitment
			leaf /*@@@*/ := proofs.PrefixLeaf{
				Vrf_output: make([]byte, len(t.leaf.searchKey)),
				Commitment: &comm,
			}
			copy(leaf.Vrf_output, t.leaf.searchKey /*@, p @*/)
			// @ fold acc((&leaf).Inv())
			searchResult /*@@@*/ := proofs.PrefixSearchResult{
				Leaf:  &leaf,
				Depth: depth,
			}
			// @ fold acc((&searchResult).Inv())
			tmp.Results = []*proofs.PrefixSearchResult{&searchResult}
			// @ fold acc(proofs.PrefixSearchResultsInv(tmp.Results))
		} else {
			val /*@@@*/ := t.leaf.value
			tmp.Elements = []*proofs.NodeValue{&val}
			// @ fold acc(proofs.NodeValuesInv(tmp.Elements))
		}
		// @ fold acc(t.leaf.Inv(), p)
		prf = &tmp
		// @ fold acc(prf.Inv())
	} else {
		var prf1, prf2 *proofs.PrefixProof
		if t.left != nil {
			prf1 = t.left.proofFromTree(depth + 1 /*@, p @*/)
		} else {
			prf1 = emptyTreeProof()
		}
		if t.right != nil {
			prf2 = t.right.proofFromTree(depth + 1 /*@, p @*/)
		} else {
			prf2 = emptyTreeProof()
		}
		prf = misc.MergeProofs(prf1, prf2)
	}
	// @ fold acc(t.Inv(), p)
	return prf
}

// @ requires noPerm < p
// @ preserves acc(t.Inv(), p)
// @ ensures prf != nil ==> acc(prf.Inv())
func (t *Prefix) ProofFromTree( /*@ ghost p perm @*/ ) (prf *proofs.PrefixProof) {
	return t.proofFromTree(0 /*@, p @*/)
}
