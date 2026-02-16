package client

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

// Minimal reproduction of suspected Gobra bugs in hyper mode.
// Both bugs involve relational assertions (rel()) failing to combine
// individually-provable facts.

/*@
ghost
decreases
ensures res > 0
func GetIntRepro() (res int)
@*/

// Bug 1: Transitivity failure with rel() projections
//
// Given: A == B, (cond ==> B == C), C <= D
// Expected: cond ==> A <= D
// Actual: Gobra cannot derive this even though each step passes individually
//
// @ requires acc(arr)
// @ requires 0 <= idx && idx < len(arr)
// @ requires 0 <= witnessIdx && witnessIdx < len(arr)
func Bug1_TransitivityFailure(arr []uint64, t uint64, idx int, witnessIdx int) {
	step := arr[idx]

	/*@
	// Assume the invariant condition (would come from TStar witness in real code)
	assume rel(arr[rel(witnessIdx,0)],0) <= rel(t,0)

	// Step 1: step == arr[idx] (from assignment)
	assert rel(step,0) == rel(arr[rel(idx,0)],0)

	// Step 2: If idx == witnessIdx, then arr[idx] == arr[witnessIdx] (array lookup)
	assert rel(idx,0) == rel(witnessIdx,0) ==> rel(arr[rel(idx,0)],0) == rel(arr[rel(witnessIdx,0)],0)

	// Step 3: arr[witnessIdx] <= t (from assume above)
	assert rel(arr[rel(witnessIdx,0)],0) <= rel(t,0)

	// By transitivity of steps 1-3:
	//   idx == witnessIdx ==> step == arr[idx] == arr[witnessIdx] <= t
	// So: idx == witnessIdx ==> step <= t
	//
	// BUG: This fails even though it follows from the three assertions above:
	// assert rel(idx,0) == rel(witnessIdx,0) ==> rel(step,0) <= rel(t,0)

	// And this lifted version also fails:
	// assert rel(idx,0) == rel(witnessIdx,0) ==> rel(step <= t, 0)
	@*/

	_ = step
}

// Bug 2: let bindings in loop invariants break establishment in hyper mode
//
// A ==> !B is provable, but !(A && B) || C fails establishment when expressed
// with a let binding, even though they are logically equivalent (when A ==> !B,
// !(A && B) is always true, so the disjunction is trivially true).
//
// @ requires acc(steps)
// @ requires len(steps) > 0
func Bug2_LetBindingEstablishment(steps []uint64, t uint64) {
	//@ assume rel(t,0) != rel(t,1)
	//@ ghost k := GetIntRepro()
	//@ assume rel(t,0) > rel(t,1) ==> 0 <= rel(k,0)

	idx := 0
	determined := false

	// This assertion passes (the antecedent implies the negation of the consequent's LHS):
	//@ assert rel(t,0) > rel(t,1) ==> !(rel(idx,0) > rel(k,0))

	// But this logically equivalent assertion FAILS:
	// (When A ==> !B, then !(A && B) is always true)
	// @ assert !(rel(t,0) > rel(t,1) && (rel(idx,0) > rel(k,0)))

	// The ==> form works as a loop invariant:
	//@ invariant acc(steps)
	//@ invariant 0 <= idx && idx <= len(steps)
	//@ invariant (rel(t,0) > rel(t,1) && rel(idx,0) > rel(k,0)) ==> (rel(determined,0) || rel(determined,1))
	// But the let-binding form FAILS establishment (even though logically equivalent):
	// invariant let kGtIdx := rel(idx,0) > rel(k,0) in !((rel(t,0) > rel(t,1)) && kGtIdx) || (rel(determined,0) || rel(determined,1))
	for ; idx < len(steps); idx++ {
		_ = steps[idx]
		determined = true
	}

	_ = determined
}
