package prefix

import (
	"bytes"
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/trees/misc"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
	utilsrel "github.com/felixlinker/keytrans-verification/pkg/utils-rel"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

type prefixLeaf struct {
	value      []byte
	searchKey  []byte
	commitment []byte
}

/*@
pred (l *prefixLeaf) Inv() {
	acc(l) &&
	// Either value is not nil, or search key AND commitment are not nil
	(l.value != nil) != (l.searchKey != nil && l.commitment != nil) &&
	(l.value != nil ==> acc(utils.BytesMem(l.value))) &&
	(l.searchKey != nil ==> acc(utils.BytesMem(l.searchKey))) &&
	(l.commitment != nil ==> acc(utils.BytesMem(l.commitment)))
}
@*/

// @ requires  noPerm < p
// @ requires  0 <= depth
// @ preserves acc(l.Inv(), p)
// @ ensures   v != nil && acc(utils.BytesMem(v))
// TODO: I should have all ingredients to prove below ensures, but I get permission errors
// // @ ensures   unfolding acc(l.Inv(), p) in (l.value == nil ==> (low(utils.GetBytesContent(v)) ==> (low(utils.GetBytesContent(l.searchKey)) && low(utils.GetBytesContent(l.commitment)))))
func (l *prefixLeaf) Value( /*@ ghost depth int, ghost p perm @*/ ) (v proofs.NodeValue /*@, ghost incl Incl, ghost notIncl NotIncl @*/) {
	if /*@ unfolding acc(l.Inv(), p) in @*/ l.value != nil {
		// @ unfold acc(l.Inv(), p)
		cop /*@@@*/ := utils.Copy(l.value /*@, p @*/)
		// @ fold acc(l.Inv(), p)
		v = cop
		// A hash value proves nothing about inclusion or non-inclusion
		// @ incl = Incl{}
		// @ notIncl = NotIncl{}
	} else {
		// Spec: leaf.value = Hash(0x02 || vrf_output || commitment)
		// @ unfold acc(l.Inv(), p)
		input1 := []byte{0x02}
		// @ fold utils.BytesMem(input1)
		// @ assert low(utils.GetBytesContent(input1))
		input2 := utilsrel.Concat(l.searchKey, l.commitment /*@, p @*/)
		// @ assert low(utils.GetBytesContent(input2)) == (low(utils.GetBytesContent(l.searchKey)) && low(utils.GetBytesContent(l.commitment)))
		input := utilsrel.Concat(input1, input2 /*@, perm(1/2) @*/)
		// @ assert low(utils.GetBytesContent(input)) == (low(utils.GetBytesContent(l.searchKey)) && low(utils.GetBytesContent(l.commitment)))

		// @ unfold acc(utils.BytesMem(l.searchKey), p)
		// @ incl = Incl{ utils.Bits_Pure(l.searchKey) }
		// @ notIncl = utils.FlippedTailsPure(utils.Bits_Pure(l.searchKey), depth)
		// @ fold acc(utils.BytesMem(l.searchKey), p)

		v = crypto.Sum(input /*@, perm(1/2) @*/)
		// @ ghost pureV := utilsrel.GetBytesContentIsLow(v, perm(1/2))
		// @ assert low(utils.GetBytesContent(v)) == (low(utils.GetBytesContent(l.searchKey)) && low(utils.GetBytesContent(l.commitment)))
		// @ fold acc(l.Inv(), p)
	}
	return
}

// @ requires  noPerm < p
// @ preserves pl != nil ==> acc(pl.Inv(), p)
// @ ensures   pl != nil ==> l.Inv()
func commitmentLeaf(pl *proofs.PrefixLeaf /*@, ghost p perm @*/) (l *prefixLeaf) {
	if pl != nil {
		// @ unfold acc(pl.Inv(), p)
		c /*@@@*/ := utils.Copy(pl.Commitment /*@, p/2 @*/)
		l = &prefixLeaf{
			value:      nil,
			searchKey:  utils.Copy(pl.Vrf_output /*@, p/2 @*/),
			commitment: c,
		}
		// @ fold l.Inv()
		// @ fold acc(pl.Inv(), p)
	}
	return
}

type Tree struct {
	leaf  *prefixLeaf
	left  *Tree
	right *Tree
}

/*@
pred (t *Tree) Inv() {
	acc(t) &&
	(t.leaf != nil ==> t.leaf.Inv()) &&
	(t.left != nil ==> t.left.Inv()) &&
	(t.right != nil ==> t.right.Inv())
}
@*/

/*@
pred PrefixesInv(ts []*Tree) {
	forall i int :: {ts[i]} 0 <= i && i < len(ts) ==> acc(&ts[i]) && acc(ts[i].Inv())
}
@*/

// @ ensures t.Inv()
func mkTree() (t *Tree) {
	t = &Tree{}
	// @ fold t.Inv()
	return
}

// @ requires  noPerm < p
// @ requires  acc(path, p)
// @ requires  0 <= depth
// @ requires  leaf.Inv()
// @ preserves t.Inv()
func (t *Tree) insertAtChild(path []bool, depth int, leaf *prefixLeaf /*@, ghost p perm @*/) (err error) {
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

// If this is a leaf, move the leaf in a newly created child of the node.
// @ requires 0 <= depth
// @ preserves t.Inv()
func (t *Tree) extend(depth int) (err error) {
	if /*@ unfolding t.Inv() in @*/ t.leaf != nil {
		// @ unfold t.Inv()
		recLeaf := t.leaf
		t.leaf = nil
		// @ fold t.Inv()

		if /*@ unfolding recLeaf.Inv() in @*/ recLeaf.searchKey == nil {
			err = errors.New("search key error at leaf")
		} else {
			// @ unfold recLeaf.Inv()
			// @ unfold utils.BytesMem(recLeaf.searchKey)
			recSearchKey := utils.Bits(recLeaf.searchKey /*@, perm(1/2) @*/)
			// @ fold utils.BytesMem(recLeaf.searchKey)
			// @ fold recLeaf.Inv()
			err = t.insertAtChild(recSearchKey, depth, recLeaf /*@, perm(1/2) @*/)
		}
	}
	return
}

// @ requires  noPerm < p
// @ requires  acc(path, p)
// @ requires  0 <= depth
// @ requires  leaf.Inv()
// @ preserves t.Inv()
func (t *Tree) insert(path []bool, depth int, leaf *prefixLeaf /*@, ghost p perm @*/) (err error) {
	if /*@ unfolding t.Inv() in @*/ t.leaf == nil && t.left == nil && t.right == nil {
		// @ unfold t.Inv()
		t.leaf = leaf
		// @ fold t.Inv()
	} else if len(path) <= depth {
		// @ unfold t.Inv()
		// We arrived at the maximum depth; overwrite the respective leaf
		t.leaf = leaf
		// We assume that search keys are all of equal length. We enforce this
		// property by setting the children to nil.
		t.left = nil
		t.right = nil
		// @ fold t.Inv()
	} else {
		// If there already is a leaf, "push it down" into the left or right
		// subtree. If there is no leaf, t.extend() is a noop.
		if e := t.extend(depth); e != nil {
			err = e
		} else {
			err = t.insertAtChild(path, depth, leaf /*@, p @*/)
		}
	}
	return
}

// @ requires  leaf.Inv()
// @ preserves t.Inv()
func (t *Tree) Insert(leaf *prefixLeaf) (err error) {
	if /*@ unfolding acc(leaf.Inv()) in @*/ leaf.searchKey == nil {
		err = errors.New("cannot insert leaf without search key")
	} else {
		// @ unfold acc(leaf.Inv(), perm(1/2))
		// @ unfold acc(utils.BytesMem(leaf.searchKey), perm(1/2))
		searchKeyBits := utils.Bits(leaf.searchKey /*@, perm(1/2) @*/)
		// @ fold acc(utils.BytesMem(leaf.searchKey), perm(1/2))
		// @ fold acc(leaf.Inv(), perm(1/2))
		err = t.insert(searchKeyBits, 0, leaf /*@, perm(1/2) @*/)
	}
	return
}

// @ requires  noPerm < p
// @ preserves t != nil ==> acc(t.Inv(), p)
func (t *Tree) IsEmpty( /*@ ghost p perm @*/ ) (empty bool) {
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

// @ requires noPerm < p
// @ preserves acc(utils.BytesMem(nodeValue), p)
// @ ensures t.Inv()
func nodeValueLeaf(nodeValue proofs.NodeValue /*@, ghost p perm @*/) (t *Tree) {
	t = &Tree{
		leaf: &prefixLeaf{
			value:      utils.Copy(nodeValue /*@, p @*/),
			searchKey:  nil,
			commitment: nil,
		},
		left:  nil,
		right: nil,
	}
	// @ fold t.leaf.Inv()
	// @ fold t.Inv()
	return
}

// @ requires  0 <= depth && depth <= len(steps)
// @ requires  t.Inv() && leaf.Inv()
// @ preserves acc(steps)
// @ ensures   t.Inv()
func (t *Tree) setLeaf(steps []bool, depth int, leaf *prefixLeaf) {
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

// TODO: Verification is rather slow. Speed up.
// @ requires  noPerm < p
// @ requires  acc(proofs.NodeValuesInv(elements), p)
// @ preserves t.Inv()
// @ ensures   err == nil ==> acc(proofs.NodeValuesInv(es), p)
func (t *Tree) fill(elements []proofs.NodeValue /*@, ghost p perm @*/) (es []proofs.NodeValue, err error) {
	// @ unfold t.Inv()
	if t.leaf != nil {
		es = elements
	} else {
		var esL []proofs.NodeValue
		if t.left != nil {
			esL, err = t.left.fill(elements /*@, p @*/)
		} else if len(elements) == 0 {
			err = errors.New("too few elements")
		} else {
			// @ unfold acc(proofs.NodeValuesInv(elements), p)
			if !utils.AllZero(elements[0] /*@, p @*/) {
				t.left = nodeValueLeaf(elements[0] /*@, p @*/)
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
				if !utils.AllZero(esL[0] /*@, p @*/) {
					t.right = nodeValueLeaf(esL[0] /*@, p @*/)
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
pure func (t *Tree) depth() (r uint64) {
	return t == nil ? 0 :
		unfolding acc(t.Inv(), _) in
			let lDepth := t.left == nil ? 0 : t.left.depth() in
			let rDepth := t.right == nil ? 0 : t.right.depth() in
			1 + utils.max(lDepth, rDepth)
}

ghost type Incl = seq[seq[bool]]

ghost
requires  t != nil ==> acc(t.Inv(), _)
decreases t.depth()
pure func (t *Tree) Included() (r Incl) {
	return (t == nil ?
		// The empty leaf proves inclusion of no prefix
		Incl{} :
		(unfolding acc(t.Inv(), _) in (t.leaf != nil ?
			(unfolding acc(t.leaf.Inv(), _) in t.leaf.searchKey != nil ?
				unfolding acc(utils.BytesMem(t.leaf.searchKey), _) in Incl{ utils.Bits_Pure(t.leaf.searchKey) } :
				Incl{}) :
			(t.left.Included() ++ t.right.Included()))))
}

ghost type NotIncl = seq[seq[bool]]

ghost
requires  t != nil ==> acc(t.Inv(), _)
requires  0 <= depth
decreases t.depth()
pure func (t *Tree) NotIncludedPrefixes(depth int) (r NotIncl) {
	return (t == nil ?
		// The empty leaf proves non-inclusion of every suffix
		NotIncl{ seq[bool]{} } :
		(unfolding acc(t.Inv(), _) in (t.leaf != nil ?
			// A leaf proves the non-inclusion of no suffix
			(unfolding acc(t.leaf.Inv(), _) in (t.leaf.searchKey != nil ?
				// No search key proves the non-inclusion of nothing; we are only given a hash
				NotIncl{} :
				// A search key proves the non-inclusion of every intermediate infix with the last bit respectively flipped
				// TODO: Below does not require unfolding of BytesMem, which suggests this branch is unreachable and erroneous
				utils.FlippedTailsPure(utils.Bits_Pure(t.leaf.searchKey), depth))) :
			(	let left := utils.PrependAll(t.left.NotIncludedPrefixes(depth+1), false) in
				let right := utils.PrependAll(t.right.NotIncludedPrefixes(depth+1), true) in
				left ++ right))))
}

pred NoPrefixMatches(prefixes NotIncl, values Incl) {
	forall i, j int :: 0 <= i && i < len(prefixes) && 0 <= j && j < len(values) ==>
		(len(values[j]) < len(prefixes[i]) || prefixes[i] != values[j][:len(prefixes[i])])
}
@*/

// @ requires noPerm < p
// @ requires 0 <= depth
// @ preserves acc(t.Inv(), p)
// @ ensures err == nil ==> r != nil && acc(utils.BytesMem(r))
func (t *Tree) innerNodeValue( /*@ ghost depth int, ghost p perm @*/ ) (r proofs.NodeValue, err error /*@, ghost incl Incl, ghost notIncl NotIncl @*/) {
	// @ unfold acc(t.Inv(), p)
	if t.left == nil && t.right == nil {
		err = errors.New("tree is not inner node")
		// @ fold acc(t.Inv(), p)
	} else if left, errL /*@, inclL, notInclL @*/ := t.left.value( /*@ depth+1, p @*/ ); errL != nil {
		err = errL
		// @ fold acc(t.Inv(), p)
	} else if right, errR /*@, inclR, notInclR @*/ := t.right.value( /*@ depth+1, p @*/ ); errR != nil {
		err = errR
		// @ fold acc(t.Inv(), p)
	} else {
		// @ fold acc(t.Inv(), p)
		input := make([]byte, 1+len(left)+len(right))
		input[0] = 0x03
		// @ unfold acc(utils.BytesMem(left))
		// @ unfold acc(utils.BytesMem(right))
		// @ invariant len(input) == 1+len(left)+len(right)
		// @ invariant 0 <= i && i <= len(left)
		// @ invariant acc(input) && acc(left, perm(1/2)) && acc(right, perm(1/2))
		for i := 0; i < len(left); i++ {
			input[1+i] = left[i]
		}
		// @ invariant len(input) == 1+len(left)+len(right)
		// @ invariant 0 <= i && i <= len(right)
		// @ invariant acc(input) && acc(left, perm(1/2)) && acc(right, perm(1/2))
		for i := 0; i < len(right); i++ {
			input[1+len(left)+i] = right[i]
		}
		// @ fold acc(utils.BytesMem(input))
		r = crypto.Sum(input /*@, perm(1/2) @*/)
		// @ incl = inclL ++ inclR
		// @ notIncl = notInclL ++ notInclR
	}
	return
}

// @ requires noPerm < p
// @ requires t != nil ==> acc(t.Inv(), p)
// @ requires 0 <= depth
// // @ requires low(t.Included())
// @ ensures  t != nil ==> acc(t.Inv(), p)
// @ ensures  err == nil ==> r != nil && acc(utils.BytesMem(r))
// // @ ensures low(r) && err == nil ==>
// // @	NoPrefixMatches(rel(t, 0).NotIncludedPrefixes(0), rel(t, 1).Included()) &&
// // @	NoPrefixMatches(rel(t, 1).NotIncludedPrefixes(0), rel(t, 0).Included())
func (t *Tree) value( /*@ ghost depth int, ghost p perm @*/ ) (r []byte, err error /*@, ghost incl Incl, ghost notIncl NotIncl @*/) {
	if t != nil {
		if /*@ unfolding acc(t.Inv(), p) in @*/ t.leaf != nil {
			// @ unfold acc(t.Inv(), p)
			r /*@, incl, notIncl @*/ = t.leaf.Value( /*@ depth, p @*/ )
			// @ fold acc(t.Inv(), p)
		} else {
			r, err /*@, incl, notIncl @*/ = t.innerNodeValue( /*@ depth, p @*/ )
		}
	} else { // t == nil
		/*@
		ghost
		incl = t.Included()
		notIncl = t.NotIncludedPrefixes(depth)
		 @*/
		r = make(proofs.NodeValue, sha256.Size)
		// @ fold acc(utils.BytesMem(r))
	}
	return
}

// @ requires noPerm < p
// @ requires t != nil ==> acc(t.Inv(), p)
// // @ requires low(t.Included())
// @ ensures  t != nil ==> acc(t.Inv(), p)
// @ ensures  err == nil ==> r != nil && acc(utils.BytesMem(r))
// // @ ensures low(r) && err == nil ==>
// // @	NoPrefixMatches(rel(t, 0).NotIncludedPrefixes(0), rel(t, 1).Included()) &&
// // @	NoPrefixMatches(rel(t, 1).NotIncludedPrefixes(0), rel(t, 0).Included())
func (t *Tree) Value( /*@ ghost p perm @*/ ) (r proofs.NodeValue, err error) {
	// @ ghost var incl, notIncl seq[seq[bool]]
	r, err /*@, incl, notIncl @*/ = t.value( /*@ 0, p @*/ )
	return
}

// @ requires  noPerm < p
// @ preserves acc(searchKey, p)
// @ requires  acc(t.Inv(), p)
// @ ensures   acc(t.Inv(), p/2)
// @ ensures   l == nil ==> acc(t.Inv(), p/2)
// @ ensures   l != nil ==> acc(l.Inv(), p/2)
func (t *Tree) getLeaf(searchKey []bool /*@, ghost p perm @*/) (l *prefixLeaf, ok bool) {
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
// @ preserves acc(utils.BytesMem(searchKey), p)
// @ ensures   acc(t.Inv(), p/2)
// @ ensures   r != nil ==> acc(utils.BytesMem(r), p/2)
func (t *Tree) Search(searchKey []byte /*@, ghost p perm @*/) (r []byte, ok bool) {
	// TODO: Cannot return r == nil && ok
	// @ unfold acc(utils.BytesMem(searchKey), p)
	searchKeyBits := utils.Bits(searchKey /*@, p @*/)
	// @ fold acc(utils.BytesMem(searchKey), p)
	if leaf, leafOk := t.getLeaf(searchKeyBits /*@, p @*/); !leafOk {
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
			r = utils.Copy(leaf.commitment /*@, p/2 @*/)
			// @ unfold acc(utils.BytesMem(leaf.searchKey), p/2)
			// @ unfold acc(utils.BytesMem(searchKey), p)
			ok = bytes.Equal(leaf.searchKey, searchKey /*@, p/2, p @*/)
			// @ fold acc(utils.BytesMem(searchKey), p)
			// @ fold acc(utils.BytesMem(leaf.searchKey), p/2)
		}
		// @ fold acc(leaf.Inv(), p/2)
	}
	return
}

// This function assumes that every prefix search result includes a leaf. This
// can be established by calling proofs.PullLeaves.
// @ requires noPerm < p
// @ requires acc(prf.Inv(), p)
// @ ensures  err == nil ==> tree.Inv()
func MkPrefix(prf *proofs.PrefixProof /*@, ghost p perm @*/) (tree *Tree, err error) {
	tree = &Tree{}
	// @ fold tree.Inv()

	// @ invariant tree.Inv()
	// @ invariant acc(prf.Inv(), p)
	// @ invariant 0 <= i && i <= len(unfolding acc(prf.Inv(), p) in prf.Results)
	for i := 0; i < len( /*@ unfolding acc(prf.Inv(), p) in @*/ prf.Results) && err == nil; i++ {
		// @ unfold acc(prf.Inv(), p)
		// @ unfold acc(proofs.PrefixSearchResultsInv(prf.Results), p)
		// @ unfold acc(prf.Results[i].Inv(), p)
		result := prf.Results[i]
		if result.Leaf == nil {
			// NOTE: That data structure in the draft does not provide the invariant
			// that leafs are never nil, but I establish it in proofs.PullLeaves
			err = errors.New("missing prefix proof leaf")
		} else {
			// @ unfold acc(result.Leaf.Inv(), p)
			searchKey := utils.Copy(result.Leaf.Vrf_output /*@, p @*/)
			// @ unfold utils.BytesMem(searchKey)
			searchKeyBits := utils.Bits(searchKey /*@, perm(1/2) @*/)
			// @ fold utils.BytesMem(searchKey)

			l /*@@@*/ := proofs.PrefixLeaf{
				Vrf_output: searchKey,
				Commitment: utils.Copy(result.Leaf.Commitment /*@, p @*/),
			}
			// @ fold acc(result.Leaf.Inv(), p)
			// @ fold acc((&l).Inv(), p)
			// @ assume 0 <= result.Depth && result.Depth <= 255 // help gobra with uint
			// @ assume int(result.Depth) <= len(searchKeyBits) // TODO: make invariant
			tree.setLeaf(searchKeyBits, int(result.Depth), commitmentLeaf(&l /*@, p @*/))

		}
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

// @ requires 0 <= depth
// @ preserves t.Inv()
func (t *Tree) cutLeaf( /*@ ghost depth int @*/ ) {
	// @ unfold t.Inv()
	if t.leaf != nil {
		var value /*@@@*/ proofs.NodeValue
		// @ ghost var tmp1, tmp2 seq[seq[bool]]
		value /*@, tmp1, tmp2 @*/ = t.leaf.Value( /*@ depth, perm(1/2) @*/ )
		// @ unfold t.leaf.Inv()
		t.leaf.value = value
		t.leaf.searchKey = nil
		t.leaf.commitment = nil
		// @ fold t.leaf.Inv()
	}
	// @ fold t.Inv()
}

// TODO: Verification is rather slow. Optimize.
// @ requires  noPerm < p
// @ requires  0 <= depth
// @ preserves acc(t.Inv())
// @ preserves acc(utils.BytesMem(searchKey), p)
// @ preserves acc(searchKeyPath, p)
func (t *Tree) prune(searchKey []byte, searchKeyPath []bool, depth int /*@, ghost p perm @*/) (err error) {
	if /*@ unfolding t.Inv() in @*/ t.leaf != nil {
		// @ unfold t.Inv()
		// @ unfold t.leaf.Inv()
		if t.leaf.searchKey != nil {
			// @ unfold utils.BytesMem(t.leaf.searchKey)
			// @ unfold acc(utils.BytesMem(searchKey), p)
			cut := bytes.Equal(t.leaf.searchKey, searchKey /*@, perm(1/2), p @*/)
			// @ fold acc(utils.BytesMem(searchKey), p)
			// @ fold utils.BytesMem(t.leaf.searchKey)
			// @ fold t.leaf.Inv()
			// @ fold t.Inv()
			if cut {
				t.cutLeaf( /*@ depth @*/ )
			}
		} /*@ else {
			// @ fold t.leaf.Inv()
			// @ fold t.Inv()
		} @*/
	} else if depth < len(searchKeyPath) {
		// @ unfold t.Inv()
		if searchKeyPath[depth] {
			if t.right != nil {
				err = t.right.prune(searchKey, searchKeyPath, depth+1 /*@, p @*/)
			}
		} else {
			if t.left != nil {
				err = t.left.prune(searchKey, searchKeyPath, depth+1 /*@, p @*/)
			}
		}
		// @ fold t.Inv()

		if err == nil && t.IsEmpty( /*@ perm(1/2) @*/ ) {
			if value, e /*@@@*/ := t.Value( /*@ perm(1/2) @*/ ); e != nil {
				err = e
			} else {
				l := &prefixLeaf{
					value: value,
				}
				// @ fold l.Inv()
				// @ unfold t.Inv()
				t.leaf = l
				t.left = nil
				t.right = nil
				// @ fold t.Inv()
			}
		}
	}
	return
}

// @ requires  noPerm < p
// @ preserves t.Inv()
// @ preserves acc(utils.BytesSliceInv(searchKeys), p)
func (t *Tree) Prune(searchKeys [][]byte /*@, ghost p perm @*/) {
	// @ invariant 0 <= i && i <= len(searchKeys)
	// @ invariant t.Inv()
	// @ invariant acc(utils.BytesSliceInv(searchKeys), p)
	for i := 0; i < len(searchKeys); i++ {
		// @ unfold acc(utils.BytesSliceInv(searchKeys), p)
		// @ unfold acc(utils.BytesMem(searchKeys[i]), p)
		path := utils.Bits(searchKeys[i] /*@, p @*/)
		// @ fold acc(utils.BytesMem(searchKeys[i]), p)
		t.prune(searchKeys[i], path, 0 /*@, p @*/)
		// @ fold acc(utils.BytesSliceInv(searchKeys), p)
	}
}

// @ requires  noPerm < p
// @ preserves acc(leaf.Inv(), p)
// @ ensures   prf.Inv()
func leafTreeProof(leaf *prefixLeaf, depth uint8 /*@, ghost p perm @*/) (prf *proofs.PrefixProof) {
	prf = &proofs.PrefixProof{
		Results:  []*proofs.PrefixSearchResult{},
		Elements: []proofs.NodeValue{},
	}
	// @ fold acc(proofs.PrefixSearchResultsInv(prf.Results))
	// @ fold acc(proofs.NodeValuesInv(prf.Elements))

	// @ unfold acc(leaf.Inv(), p)
	if leaf.searchKey != nil && leaf.commitment != nil {
		searchResult /*@@@*/ := proofs.PrefixSearchResult{
			Leaf: &proofs.PrefixLeaf{
				Vrf_output: utils.Copy(leaf.searchKey /*@, p @*/),
				Commitment: utils.Copy(leaf.commitment /*@, p @*/),
			},
			Depth: depth,
		}
		// @ fold acc(searchResult.Leaf.Inv())
		// @ fold acc((&searchResult).Inv())
		prf.Results = []*proofs.PrefixSearchResult{&searchResult}
		// @ fold acc(proofs.PrefixSearchResultsInv(prf.Results))
	} else {
		prf.Elements = []proofs.NodeValue{utils.Copy(leaf.value /*@, p @*/)}
		// @ assert forall i, j int :: {prf.Elements[i], prf.Elements[j]} 0 <= i && i < j && j < len(prf.Elements) ==> &prf.Elements[i][0] != &prf.Elements[j][0]
		// TODO: folding below predicate currently fails. No idea why, above
		// assertion should be enough
		// @ inhale proofs.NodeValuesInv(prf.Elements)
	}
	// @ fold acc(leaf.Inv(), p)
	// @ fold acc(prf.Inv())
	return
}

// @ ensures prf.Inv()
func emptyTreeProof() (prf *proofs.PrefixProof) {
	prf = &proofs.PrefixProof{
		Results:  []*proofs.PrefixSearchResult{},
		Elements: []proofs.NodeValue{make(proofs.NodeValue, sha256.Size)},
	}
	// @ fold utils.BytesMem(prf.Elements[0])
	// @ fold proofs.PrefixSearchResultsInv(prf.Results)
	// TODO: The usual story. Injectivity.
	// @ inhale proofs.NodeValuesInv(prf.Elements)
	// @ fold prf.Inv()
	return
}

// @ requires  noPerm < p
// @ preserves acc(t.Inv(), p)
// @ ensures prf.Inv()
func (t *Tree) proofFromTree(depth uint8 /*@, ghost p perm @*/) (prf *proofs.PrefixProof) {
	// @ unfold acc(t.Inv(), p)
	if t.leaf != nil {
		prf = leafTreeProof(t.leaf, depth /*@, p @*/)
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

// @ requires  noPerm < p
// @ preserves acc(t.Inv(), p)
// @ ensures   prf.Inv()
func (t *Tree) ProofFromTree( /*@ ghost p perm @*/ ) (prf *proofs.PrefixProof) {
	return t.proofFromTree(0 /*@, p @*/)
}
