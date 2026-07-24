package misc

import (
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

// @ requires acc(proofs.PrefixSearchResultsInv(rs1))
// @ requires acc(proofs.PrefixSearchResultsInv(rs2))
// @ ensures  acc(proofs.PrefixSearchResultsInv(rs))
func mergeResults(rs1, rs2 []*proofs.PrefixSearchResult) (rs []*proofs.PrefixSearchResult) {
	// @ unfold acc(proofs.PrefixSearchResultsInv(rs1))
	// @ unfold acc(proofs.PrefixSearchResultsInv(rs2))
	rs = append( /*@ perm(1/2), @*/ rs1, rs2...)
	// TODO:
	// // @ assert forall i, j int :: {rs[i].Inv(), rs[j].Inv()} 0 <= i && i < j && j < len(rs) ==> unfolding acc(rs[i].Inv()) in unfolding acc(rs[j].Inv()) in rs[i] != rs[j]
	// @ inhale acc(proofs.PrefixSearchResultsInv(rs))
	return
}

// @ requires acc(proofs.NodeValuesInv(ns1))
// @ requires acc(proofs.NodeValuesInv(ns2))
// @ ensures  acc(proofs.NodeValuesInv(ns))
func mergeValues(ns1, ns2 []proofs.NodeValue) (ns []proofs.NodeValue) {
	if ns1 == nil {
		ns = ns2
	} else if ns2 == nil {
		ns = ns1
	} else {
		// @ unfold acc(proofs.NodeValuesInv(ns1))
		// @ unfold acc(proofs.NodeValuesInv(ns2))
		ns = append( /*@ perm(1/2), @*/ ns1, ns2...)
		// TODO:
		// // @ assert forall i, j int :: {ns[i], ns[j]} 0 <= i && i < j && j < len(ns) ==> &ns[i] != &ns[j]
		// @ inhale acc(proofs.NodeValuesInv(ns))
	}
	return
}

// @ requires prf1.Inv()
// @ requires prf2.Inv()
// @ ensures  prf.Inv()
func MergeProofs(prf1, prf2 *proofs.PrefixProof) (prf *proofs.PrefixProof) {
	// @ unfold prf1.Inv()
	// @ unfold prf2.Inv()
	rs := mergeResults(prf1.Results, prf2.Results)
	// @ assert proofs.PrefixSearchResultsInv(rs)
	ns := mergeValues(prf1.Elements, prf2.Elements)
	// @ assert proofs.NodeValuesInv(ns)
	prf = &proofs.PrefixProof{
		Results:  rs,
		Elements: ns,
	}
	// @ fold prf.Inv()
	return
}

/*@
pred SliceMapInv(m map[uint64][]byte) {
	acc(m) && (forall k uint64 :: k elem m ==> utils.BytesMem(m[k]))
}
@*/

// @ requires utils.BytesMem(v)
// @ preserves SliceMapInv(m)
func MapSet(k uint64, v []byte, m map[uint64][]byte) {
	// @ unfold acc(SliceMapInv(m))
	m[k] = v
	// TODO:
	// @ inhale acc(SliceMapInv(m))
}

// @ requires noPerm < p
// @ preserves acc(SliceMapInv(m), p)
// @ ensures ok ==> utils.BytesMem(r)
func MapGet(m map[uint64][]byte, k uint64 /*@, ghost p perm @*/) (r []byte, ok bool) {
	var tmp []byte
	// @ unfold acc(SliceMapInv(m), p)
	if tmp, ok = m[k]; ok {
		r = utils.Copy(tmp /*@, p @*/)
	}
	// @ fold acc(SliceMapInv(m), p)
	return
}
