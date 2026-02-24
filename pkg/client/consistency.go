package client

import (
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// VerifyConsistency checks that the transparency log correctly extended from
// old_size to new_size by verifying that shared full subtree hashes match.
// Implements the append-only structural check from Section 4.2 of the IETF KT spec.
// TODO: Be aware that this implementation is incomplete, does not follow the pruning part of the protocol. So we need to be careful with the stuff. 

// @ requires noPerm < p
// @ requires acc(old_subtrees, p)
// @ requires acc(old_frontier_timestamps, p)
// @ requires acc(new_prefix_roots, p)
// @ requires acc(new_timestamps, p)
// @ requires acc(config, p)
// @ requires low(old_size) && low(new_size)
// @ ensures acc(old_subtrees, p)
// @ ensures acc(old_frontier_timestamps, p)
// @ ensures acc(new_prefix_roots, p)
// @ ensures acc(new_timestamps, p)
// @ ensures acc(config, p)
// @ trusted
func VerifyConsistency(old_size uint64, old_subtrees []proofs.NodeValue, old_frontier_timestamps []uint64, new_size uint64, new_prefix_roots []proofs.NodeValue, new_timestamps []uint64, config *Configuration /*@, ghost p perm @*/) (err error) {
	determined := false
	var resultErr error = nil

	// Step 1: First update — no previous state to check
	if old_size == 0 {
		return nil
	}

	// Step 2: Tree must grow (append-only property)
	if new_size <= old_size {
		resultErr = errors.New("consistency check failed: tree did not grow")
		determined = true
	}

	// Steps 3-4: Build implicit BSTs for old and new trees
	var commonLen int
	if !determined {
		oldSearchTree := MkImplicitBinarySearchTree(old_size)
		newSearchTree := MkImplicitBinarySearchTree(new_size)

		// Step 5: Get old frontier nodes (full subtree positions)
		oldFrontier := oldSearchTree.FrontierNodes( /*@ p, old_size @*/ )

		// Step 6: Find path to old head in new tree
		pathToOldHead, pathErr := newSearchTree.PathTo(old_size - 1 /*@, p/2 @*/)
		if pathErr != nil {
			resultErr = pathErr
			determined = true
		}

		// Step 7: Count common prefix length
		if !determined {
			commonLen = 0
			//@ invariant 0 <= commonLen && commonLen <= len(pathToOldHead) && commonLen <= len(oldFrontier)
			//@ invariant acc(pathToOldHead) && acc(oldFrontier)
			for ; commonLen < len(pathToOldHead) && commonLen < len(oldFrontier) && pathToOldHead[commonLen] == oldFrontier[commonLen]; commonLen++ {
			}

			// Step 8: Verify sufficient data
			if commonLen > len(old_subtrees) || commonLen > len(new_prefix_roots) {
				resultErr = errors.New("consistency check failed: insufficient frontier data")
				determined = true
			}
		}
	}

	// Step 9: Verify shared full subtree hashes match
	// TODO: Section 6.2 — skip expired full subtree comparison when MaximumLifetime is implemented
	if !determined {
		//@ invariant 0 <= j && j <= commonLen
		//@ invariant acc(old_subtrees, p) && acc(new_prefix_roots, p)
		//@ invariant !determined ==> resultErr == nil
		for j := 0; j < commonLen; j++ {
			if !determined {
				if old_subtrees[j] != new_prefix_roots[j] {
					resultErr = errors.New("consistency check failed: frontier hash mismatch")
					determined = true
				}
			}
		}
	}

	// Step 10: Single return point
	if determined {
		err = resultErr
	}
	return
}
