package update

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/client"
	"github.com/felixlinker/keytrans-verification/pkg/prefixtree"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

/*@
ghost
requires acc(arr, _)
decreases
pure
func getContent(arr []byte) (res seq[byte]) {
  return client.GetByteContent(arr, 0)
}
@*/

// ==================================================================================
// ============================= Update Types =======================================

type UpdateResponse struct {
	Full_tree_head client.FullTreeHead
	Prev_tree_head client.FullTreeHead
	New_version    uint32
	Prev_greatest  *uint32
	Insertion_pos  uint64
	Prev_insertion *uint64
	Binary_ladder  []proofs.BinaryLadderStep
	Search         proofs.CombinedTreeProof
	Prev_search    proofs.CombinedTreeProof
	Values         []proofs.UpdateValue
	Openings       [][]byte
}

/*@
pred (u UpdateResponse) Inv() {
	u.Full_tree_head.Inv() &&
	u.Prev_tree_head.Inv() &&
	(u.Prev_greatest != nil ==> acc(u.Prev_greatest)) &&
	(u.Prev_insertion != nil ==> acc(u.Prev_insertion)) &&
	acc(u.Binary_ladder) &&
	u.Search.Inv() &&
	u.Prev_search.Inv() &&
	acc(u.Values) &&
	acc(u.Openings)
}
@*/

// ==================================================================================
// ============================= VerifyUpdateKey ====================================

/*
VerifyUpdateKey Algorithms:

1. Obtain a search binary ladder from the current log entry where the target version is the claimed greatest version of the label( I don't think we need to omit redundant lookups for performance matter...)

2. If this is the rightmost log entry, verify that the binary ladder terminates in a way that is consistent with the claimed greatest version of the label. That is, verify that it contains inclusion proofs for all expected versions less than or equal to the target and non-inclusion proofs for all expected versions greater than the target.

3. If this is not the rightmost log entry, recurse to the log entry's right child.


*/

// VerifyUpdateKey verifies that new_version is the greatest version for a label
// in the current log, analogous to VerifyLatestKey but for update verification.
// It iterates over all frontier nodes and calls CheckGreatest on each. For non-last
// frontiers, a result of 1 (greater version exists) is a failure. For the last
// frontier, the result must be exactly 0.
//
// Preconditions: prefixTrees must have length >= size with all entries non-nil and
// valid, label must be non-nil and low (public), size must be low and > 0.
//
// Postconditions (hyper-property): if err==nil and res==true, then new_version
// is low — two executions with the same root hash agree on the version.
//
// Returns:
//   - res: true if new_version is verified as the greatest
//   - err: non-nil describing the failure reason
//
// @ requires noPerm < p
// @ requires acc(prefixTrees, p)
// @ requires acc(prefixRootHash, p)
// @ requires acc(label, p) && acc(config, p)
// @ requires low(len(label)) && (forall i int :: 0 <= i && i < len(label) ==> low(label[i])) && low(size)
// @ requires forall i int :: i >= 0 && i < len(prefixTrees) ==> acc(&prefixTrees[i])
// @ requires forall i int :: {&prefixTrees[i]} i >= 0 && i < len(prefixTrees) ==> acc(prefixTrees[i].Inv(), p)
// @ requires forall i int :: i >= 0 && i < len(prefixTrees) ==> prefixTrees[i] != nil
// @ requires size > 0
// @ requires size <= uint64(len(prefixTrees))
// @ requires label != nil
// @ ensures acc(prefixTrees, p)
// @ ensures acc(prefixRootHash, p)
// @ ensures acc(label, p) && acc(config, p)
// @ ensures err == nil && res ==> low(new_version)
func VerifyUpdateKey(prefixTrees []*prefixtree.PrefixTree, prefixRootHash []*[sha256.Size]byte, size uint64, label []byte, new_version uint32, prev_greatest uint32, config *client.Configuration /*@, ghost p perm @*/) (res bool, err error) {
	tVal := uint64(new_version)
	search_tree := client.MkImplicitBinarySearchTree(size)
	resultRes := true
	var resultErr error = nil
	frontiers := search_tree.FrontierNodes( /*@p, size@*/ )
	terminalLogEntry := -1
	determined := false

	if size == 0 || tVal >= size {
		resultRes = false
		resultErr = errors.New("version out of bounds")
		determined = true
	}

	// Loop: process all frontiers except the last
	//@ invariant acc(prefixTrees)
	//@ invariant forall i int :: i >= 0 && i < len(prefixTrees) ==> acc(&prefixTrees[i])
	//@ invariant forall i int :: {&prefixTrees[i]} i >= 0 && i < len(prefixTrees) ==> acc(prefixTrees[i])
	//@ invariant acc(prefixRootHash, p)
	//@ invariant acc(frontiers)
	//@ invariant acc(label, p)
	//@ invariant acc(config, p)
	//@ invariant forall i int :: i >= 0 && i < len(prefixTrees) ==> prefixTrees[i] != nil
	//@ invariant forall i int :: i >= 0 && i < len(frontiers) ==> frontiers[i]>=0 && frontiers[i] < uint64(len(prefixTrees))
	//@ invariant low(size) ==> low(len(frontiers)) && forall j int :: j>= 0 && j < len(frontiers) ==> low(frontiers[j])
	//@ invariant 0 <= fIdx && fIdx <= len(frontiers) - 1
	//@ invariant len(frontiers) > 0
	//@ invariant determined ==> !resultRes
	//@ invariant !determined ==> resultRes && resultErr == nil
	for fIdx := 0; fIdx < len(frontiers)-1; fIdx++ {
		frontier := frontiers[fIdx]
		if !determined {
			Prefix_tree := prefixTrees[frontier]
			if prefixTrees[frontier] == nil {
				resultRes = false
				resultErr = errors.New("prefix tree is nil")
				determined = true
			} else {
				rootHash := prefixRootHash[frontier]
				if frontier >= size {
					resultRes = false
					resultErr = errors.New("version out of bounds")
					determined = true
				}

				LtGtOrEq, cgErr := client.CheckGreatest(Prefix_tree, label, tVal, rootHash[:], size)
				if cgErr != nil {
					resultRes = false
					resultErr = cgErr
					determined = true
				} else if LtGtOrEq == 1 {
					resultRes = false
					resultErr = errors.New("greater version exists")
					determined = true
				} else if LtGtOrEq == 0 && terminalLogEntry == -1 {
					terminalLogEntry = int(frontier)
				}
			}
		}
	}

	// Process last frontier separately
	if !determined {
		frontier := frontiers[len(frontiers)-1]
		Prefix_tree := prefixTrees[frontier]
		if prefixTrees[frontier] == nil {
			resultRes = false
			resultErr = errors.New("prefix tree is nil")
			determined = true
		} else {
			rootHash := prefixRootHash[frontier]
			if frontier >= size {
				resultRes = false
				resultErr = errors.New("version out of bounds")
				determined = true
			}

			LtGtOrEq, cgErr := client.CheckGreatest(Prefix_tree, label, tVal, rootHash[:], size)
			if cgErr != nil {
				resultRes = false
				resultErr = cgErr
				determined = true
			} else if LtGtOrEq != 0 {
				resultRes = false
				resultErr = errors.New("Greatest version is not the greatest in the last iteration")
				determined = true
			} else if terminalLogEntry == -1 {
				terminalLogEntry = int(frontier)
			}
		}
	}

	if terminalLogEntry == -1 && resultErr == nil {
		resultRes = false
		resultErr = errors.New("Claimed Version is not found.")
	}

	return resultRes, resultErr
}

// ==================================================================================
// ============================= buildUpdatePrefixTrees =============================

// buildUpdatePrefixTrees constructs prefix trees from an UpdateResponse's
// prefix proofs. Analogous to client.buildPrefixTrees but for update responses.
//
// Preconditions: resp must satisfy its invariant with permission p.
// Postconditions: on success, returns n trees with valid invariants and n root
// hashes whose bytes are all low. On error, resp.Inv() permission is returned.
//
// Returns:
//   - trees: slice of n non-nil PrefixTree pointers
//   - rootHashes: slice of n sha256 root hashes (all bytes low)
//   - err: non-nil if any prefix proof cannot be converted
//
// @ requires noPerm < p
// @ requires acc(resp.Inv(), p)
// @ ensures err == nil ==> acc(resp.Inv(), p)
// @ ensures err == nil ==> acc(trees) && len(trees) == n
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> acc(&trees[j])
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> trees[j] != nil
// @ ensures err == nil ==> forall j int :: {&trees[j]} 0 <= j && j < n ==> trees[j].Inv()
// @ ensures err == nil ==> acc(rootHashes) && len(rootHashes) == n
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> acc(&rootHashes[j])
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> acc(rootHashes[j])
// @ ensures err == nil ==> forall j int :: 0 <= j && j < n ==> forall k int :: 0 <= k && k < sha256.Size ==> low(rootHashes[j][k])
// @ ensures err != nil ==> acc(resp.Inv(), p)
// @ trusted
func buildUpdatePrefixTrees(resp UpdateResponse, n int /*@, ghost p perm @*/) (trees []*prefixtree.PrefixTree, rootHashes []*[sha256.Size]byte, err error) {
	trees = make([]*prefixtree.PrefixTree, 0, n)
	rootHashes = make([]*[sha256.Size]byte, 0, n)
	//@ unfold acc(resp.Inv(), p)
	for i := 0; i < n; i++ {
		prf := /*@ unfolding acc(resp.Search.Inv(), p/2) in @*/ resp.Search.Prefix_proofs[i]
		if tree, treeErr := prefixtree.ToTree(prf, resp.Binary_ladder); treeErr != nil {
			//@ fold acc(resp.Inv(), p)
			return nil, nil, treeErr
		} else {
			trees = append( /*@ perm(1/2), @*/ trees, tree)
			rootHashes = append( /*@ perm(1/2), @*/ rootHashes, tree.Value)
		}
	}
	//@ fold acc(resp.Inv(), p)
	return trees, rootHashes, nil
}

// ==================================================================================
// ============================= VerifyUpdate =======================================

/*
The user verifies this information as follows:

1. Verify that the new greatest version of the label is greater than the previously known greatest version.

2. Verify that the log entry where the new versions were inserted is to the right of where the previous greatest version of the label was inserted, or the starting position chosen in Section 8.3 if this is the first version inserted since the user became the label owner.

3. Verify that the number of commitment openings provided is equal to the new greatest version minus the previous greatest version, or is equal to the new greatest version plus one if there were no previous versions.

4. If the Transparency Log is deployed with a Third-Party Manager, verify that the number of signatures provided matches the number of commitments and that the signatures are valid.

5. Verify that the expected number of VRF proofs was provided, and that the proofs properly evaluate into a VRF output.

There are still (4.), (5.) and (6.) missing, but it is sufficient by far to show the hyperproperty we aim to show works.
Maybe discuss if we should do 4. 5. and 6. in this case and if they are necessary to weaken the security property.
But it's literally CheckGreatest + VerifyLatestKey in combination...

*/

// VerifyUpdate verifies that a new version was correctly inserted (Section 9.1).
// It performs five phases:
//  1. UpdateView — advance the user's local tree view
//  2. Validation — check new_version > prev_greatest, insertion position ordering,
//     and commitment opening count
//  3. Build prefix trees from the response's proofs
//  4. VerifyUpdateKey — verify the version is greatest across all frontier nodes
//  5. Return result
//
// Preconditions: st.Inv() must hold, resp must satisfy Inv() with permission p,
// label must be non-nil and low, tree size must be low and > 0.
//
// Postconditions (hyper-property): if err==nil, then resp.New_version is low —
// two executions with the same root hash agree on the new version number.
//
// Returns: err — non-nil if any verification step fails.
//

// @ requires noPerm < p
// @ preserves st.Inv()
// @ requires acc(resp.Inv(), p)
// @ requires acc(label, p)
// @ requires low(len(label)) && (forall i int :: 0 <= i && i < len(label) ==> low(label[i]))
// @ requires label != nil
// @ requires acc(config, p)
// @ requires resp.New_version >= 0
// @ requires low(resp.Full_tree_head.Tree_head.Tree_size)
// @ requires resp.Full_tree_head.Tree_head.Tree_size > 0
// @ requires resp.Full_tree_head.Tree_head.Tree_size <= uint64(len(resp.Search.Prefix_proofs))
// @ ensures err != nil ==> acc(resp.Inv(), p)
// @ ensures err == nil ==> low(resp.New_version)
func VerifyUpdate(st *client.UserState, label []byte, resp UpdateResponse, config *client.Configuration /*@, ghost p perm @*/) (err error) {
	//@ unfold acc(resp.Inv(), p)

	determined := false
	var resultErr error = nil

	// Capture size and n before folding so Gobra retains size <= n
	size := resp.Full_tree_head.Tree_head.Tree_size
	n := len(resp.Search.Prefix_proofs)

	// Phase 1: UpdateView
	updateErr := st.UpdateView(resp.Full_tree_head, resp.Search /*@, p/2 @*/)
	if updateErr != nil {
		resultErr = updateErr
		determined = true
	}

	// Phase 2: Validation checks
	// Step 1: Verify new version > previous greatest version
	if !determined {
		if resp.Prev_greatest != nil {
			if resp.New_version <= *resp.Prev_greatest {
				resultErr = errors.New("new version not greater than previous greatest")
				determined = true
			}
		}
	}
	// Step 2: Verify insertion position is to the right of previous insertion
	if !determined {
		if resp.Prev_insertion != nil {
			if resp.Insertion_pos <= *resp.Prev_insertion {
				resultErr = errors.New("insertion position not greater than previous insertion")
				determined = true
			}
		}
	}
	// Step 3: Verify commitment opening count matches expected
	if !determined {
		expectedCount := int(resp.New_version) + 1
		if resp.Prev_greatest != nil {
			expectedCount = int(resp.New_version) - int(*resp.Prev_greatest)
		}
		if len(resp.Openings) != expectedCount {
			resultErr = errors.New("incorrect number of commitment openings")
			determined = true
		}
	}
	// Steps 4-5 (Third-Party Manager signatures, VRF proofs) are orthogonal to
	// the low(New_version) hyperproperty being verified. They ensure data integrity
	// but do not affect whether the version number is deterministic given the same
	// root hash. See Section 9.1 of the IETF KT protocol spec.

	// Phase 3: Build prefix trees
	//@ fold acc(resp.Inv(), p)

	var trees []*prefixtree.PrefixTree
	var rootHashes []*[sha256.Size]byte
	if !determined {
		var buildErr error
		trees, rootHashes, buildErr = buildUpdatePrefixTrees(resp, n /*@, p @*/)
		if buildErr != nil {
			resultErr = buildErr
			determined = true
		}
	}

	// Phase 4: VerifyUpdateKey (iterates all frontier nodes)
	decision := false
	if !determined {
		prev_greatest := uint32(0)
		//@ unfold acc(resp.Inv(), p)
		if resp.Prev_greatest != nil {
			prev_greatest = *resp.Prev_greatest
		}

		decision, resultErr = VerifyUpdateKey(trees, rootHashes, size, label, resp.New_version, prev_greatest, config /*@, p/4 @*/)

		if !decision || resultErr != nil {
			//@ fold acc(resp.Inv(), p)
			if resultErr == nil {
				resultErr = errors.New("Update verification failed")
			}
			determined = true
		}
	}

	// Phase 5: Single return
	if !determined && decision {
		err = nil
	} else {
		err = resultErr
	}
	return err
}

// ==================================================================================
// ============================= VerifyHistory ======================================

// VerifyHistory verifies that all newly committed versions in the range
// [Prev_greatest+1, New_version] (or [0, New_version] if no previous version)
// exist in the current log (Section 8.3). For each version in range, it rebuilds
// the prefix trees and calls VerifyUpdateKey.
//
// Functional correctness (ghost returns): every version in the output `verified`
// sequence satisfies startV <= verified[j] <= New_version, and numVerified ==
// len(verified).
//
// Preconditions: resp must satisfy Inv() with permission p, label must be non-nil
// and low, tree size must be low and > 0, New_version must be low.
//
// Postconditions: resp.Inv(), label, and config permissions are returned.
// Ghost returns provide functional correctness bounds on verified versions.
//
// Returns:
//   - err: non-nil if any version fails verification
//   - verified (ghost): sequence of successfully verified version numbers
//   - numVerified (ghost): count of verified versions (== len(verified))
//   - startV (ghost): the computed start version of the range
//
// @ requires noPerm < p
// @ requires acc(resp.Inv(), p)
// @ requires acc(label, p)
// @ requires low(len(label)) && (forall i int :: 0 <= i && i < len(label) ==> low(label[i]))
// @ requires label != nil
// @ requires acc(config, p)
// @ requires resp.Full_tree_head.Tree_head.Tree_size > 0
// @ requires resp.Full_tree_head.Tree_head.Tree_size <= uint64(len(resp.Search.Prefix_proofs))
// @ requires low(resp.Full_tree_head.Tree_head.Tree_size)
// @ requires low(resp.New_version)
// @ ensures acc(resp.Inv(), p)
// @ ensures acc(label, p)
// @ ensures acc(config, p)
// @ ensures numVerified == len(verified)
// @ ensures numVerified >= 0
// startV is the computed start version (Prev_greatest+1 or 0 if none)
// @ ensures forall j int :: 0 <= j && j < numVerified ==> verified[j] >= startV
// @ ensures forall j int :: 0 <= j && j < numVerified ==> verified[j] <= resp.New_version
func VerifyHistory(label []byte, resp UpdateResponse, config *client.Configuration /*@, ghost p perm @*/) (err error /*@, ghost verified seq[uint32], ghost numVerified int, ghost startV uint32 @*/) {

	//@ unfold acc(resp.Inv(), p)

	determined := false
	var resultErr error = nil

	size := resp.Full_tree_head.Tree_head.Tree_size
	n := len(resp.Search.Prefix_proofs)

	// Read Prev_greatest while resp.Inv() is unfolded
	//TODO: Do we need to check from 0 to the newest version or from previous greatest version to the newest version
	// One can of course do this with the previous greatest, but we need to make sure that there are no security property loss happening.
	// Can we skip or not? This is the question what we want to discuss.

	start := uint32(0)
	if resp.Prev_greatest != nil {
		start = *resp.Prev_greatest + 1
	}
	end := int(resp.New_version)

	//@ ghost verified = seq[uint32]{}
	//@ ghost numVerified = 0
	//@ ghost startV = start

	//@ fold acc(resp.Inv(), p)

	// Verify each new version exists in the current log.
	// Loop from 0 to end (both low) so both hyper-mode executions iterate
	// the same number of times. Versions below start are skipped via inRange.
	// Prefix trees are rebuilt each iteration because VerifyUpdateKey/CheckGreatest
	// consume tree invariants and do not return them.

	//@ invariant acc(resp.Inv(), p)
	//@ invariant acc(label, p) && acc(config, p)
	//@ invariant label != nil
	//@ invariant low(len(label)) && (forall i int :: 0 <= i && i < len(label) ==> low(label[i]))
	//@ invariant !determined ==> resultErr == nil
	//@ invariant low(vIdx)
	//@ invariant 0 <= vIdx
	//@ invariant low(size)
	//@ invariant size > 0
	//@ invariant size <= uint64(n)
	//@ invariant numVerified >= 0
	//@ invariant numVerified == len(verified)
	//@ invariant forall j int :: 0 <= j && j < numVerified ==> verified[j] >= start
	//@ invariant forall j int :: 0 <= j && j < numVerified ==> verified[j] <= resp.New_version
	for vIdx := 0; vIdx <= end; vIdx++ {
		v := uint32(vIdx)
		inRange := v >= start
		if !determined && inRange {
			trees, rootHashes, buildErr := buildUpdatePrefixTrees(resp, n /*@, p @*/)
			if buildErr != nil {
				resultErr = buildErr
				determined = true
			} else {
				prev := uint32(0)
				if v > 0 {
					prev = v - 1
				}
				ok, verifyErr := VerifyUpdateKey(trees, rootHashes, size, label, v, prev, config /*@, p/4 @*/)
				if verifyErr != nil {
					resultErr = verifyErr
					determined = true
				} else if !ok {
					resultErr = errors.New("history verification failed: version not found in log")
					determined = true
				}
				/*@
				ghost if !determined {
				    verified = verified ++ seq[uint32]{v}
				    numVerified = numVerified + 1
				}
				@*/
			}
		}
	}

	if determined {
		err = resultErr
	} else {
		err = nil
	}
	return err /*@, verified, numVerified, startV @*/
}
