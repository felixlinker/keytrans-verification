package misc

import "github.com/felixlinker/keytrans-verification/pkg/proofs"

// @ requires acc(proofs.PrefixSearchResultsInv(rs1))
// @ requires acc(proofs.PrefixSearchResultsInv(rs2))
// @ ensures  acc(proofs.PrefixSearchResultsInv(rs))
func mergeResults(rs1, rs2 []*proofs.PrefixSearchResult) (rs []*proofs.PrefixSearchResult) {
	// @ unfold acc(proofs.PrefixSearchResultsInv(rs1))
	// @ unfold acc(proofs.PrefixSearchResultsInv(rs2))
	rs = append( /*@ perm(1/2), @*/ rs1, rs2...)
	// @ assert forall i, j int :: {rs[i].Inv(), rs[j].Inv()} 0 <= i && i < j && j < len(rs) ==> unfolding acc(rs[i].Inv()) in unfolding acc(rs[j].Inv()) in rs[i] != rs[j]
	// @ fold acc(proofs.PrefixSearchResultsInv(rs))
	return
}

// @ requires acc(proofs.NodeValuesInv(ns1))
// @ requires acc(proofs.NodeValuesInv(ns2))
// @ ensures  acc(proofs.NodeValuesInv(ns))
func mergeValues(ns1, ns2 []*proofs.NodeValue) (ns []*proofs.NodeValue) {
	if ns1 == nil {
		ns = ns2
	} else if ns2 == nil {
		ns = ns1
	} else {
		// @ unfold acc(proofs.NodeValuesInv(ns1))
		// @ unfold acc(proofs.NodeValuesInv(ns2))
		ns = append( /*@ perm(1/2), @*/ ns1, ns2...)
		// @ assert forall i, j int :: {ns[i], ns[j]} 0 <= i && i < j && j < len(ns) ==> &ns[i][0] != &ns[j][0] && ns[i] != ns[j]
		// @ fold acc(proofs.NodeValuesInv(ns))
	}
	return
}

// @ requires prf1 != nil ==> acc(prf1.Inv())
// @ requires prf2 != nil ==> acc(prf2.Inv())
// @ ensures  prf != nil  ==> acc(prf.Inv())
func MergeProofs(prf1, prf2 *proofs.PrefixProof) (prf *proofs.PrefixProof) {
	if prf1 == nil {
		prf = prf2
	} else if prf2 == nil {
		prf = prf1
	} else {
		// @ unfold acc(prf1.Inv())
		// @ unfold acc(prf2.Inv())
		rs := mergeResults(prf1.Results, prf2.Results)
		// @ assert acc(proofs.PrefixSearchResultsInv(rs))
		ns := mergeValues(prf1.Elements, prf2.Elements)
		// @ assert acc(proofs.NodeValuesInv(ns))
		tmp /*@@@*/ := proofs.PrefixProof{
			Results:  rs,
			Elements: ns,
		}
		prf = &tmp
		// @ fold acc(prf.Inv())
	}
	return prf
}
