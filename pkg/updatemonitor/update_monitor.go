package updatemonitor

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/client"
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
// ============================= Update & Monitor Types =============================

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

type MonitorResponse struct {
	Full_tree_head client.FullTreeHead
	Binary_ladder  []proofs.BinaryLadderStep
	Search         proofs.CombinedTreeProof
}

/*@
pred (m MonitorResponse) Inv() {
	m.Full_tree_head.Inv() &&
	acc(m.Binary_ladder) &&
	m.Search.Inv()
}
@*/

// ==================================================================================
// ============================= VerifyUpdateKey ====================================

/*
VerifyUpdateKey Algorithms:

1. Obtain a search binary ladder from the current log entry where the target version is the claimed greatest version of the label, omitting redundant lookups.

2. If this is the rightmost log entry, verify that the binary ladder terminates in a way that is consistent with the claimed greatest version of the label. That is, verify that it contains inclusion proofs for all expected versions less than or equal to the target and non-inclusion proofs for all expected versions greater than the target.

3. If this is not the rightmost log entry, recurse to the log entry's right child.

*/

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
// @ ensures acc(label, p) && acc(config, p)
// @ ensures acc(prefixTrees, p) && acc(prefixRootHash, p)
// @ ensures err == nil && res ==> low(new_version)
func VerifyUpdateKey(prefixTrees []*proofs.PrefixTree, prefixRootHash []*[sha256.Size]byte, size uint64, label []byte, new_version uint32, prev_greatest uint32, config *client.Configuration /*@, ghost p perm @*/) (res bool, err error) {
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

				steps /*@, tStarIdx @*/ := client.FullBinaryLadderSteps_with_tstar(tVal)

				//@ ghost var labelSeq seq[byte] = getContent(label)
				//@ ghost var rootHashSeq seq[byte] = getContent(rootHash[:])

				LtGtOrEq, cgErr := client.CheckGreatest(Prefix_tree, steps, label, tVal, rootHash[:], size /*@, tStarIdx, labelSeq, rootHashSeq @*/)
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

			steps /*@, tStarIdx @*/ := client.FullBinaryLadderSteps_with_tstar(tVal)

			//@ ghost var labelSeq seq[byte] = getContent(label)
			//@ ghost var rootHashSeq seq[byte] = getContent(rootHash[:])

			LtGtOrEq, cgErr := client.CheckGreatest(Prefix_tree, steps, label, tVal, rootHash[:], size /*@, tStarIdx, labelSeq, rootHashSeq @*/)
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

// buildUpdatePrefixTrees constructs prefix trees from an UpdateResponse's prefix proofs.
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
func buildUpdatePrefixTrees(resp UpdateResponse, n int /*@, ghost p perm @*/) (trees []*proofs.PrefixTree, rootHashes []*[sha256.Size]byte, err error) {
	trees = make([]*proofs.PrefixTree, 0, n)
	rootHashes = make([]*[sha256.Size]byte, 0, n)
	//@ unfold acc(resp.Inv(), p)
	for i := 0; i < n; i++ {
		prf := /*@ unfolding acc(resp.Search.Inv(), p/2) in @*/ resp.Search.Prefix_proofs[i]
		if tree, treeErr := prf.ToTree(resp.Binary_ladder); treeErr != nil {
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

// buildMonitorPrefixTrees constructs prefix trees from a MonitorResponse's prefix proofs.
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
func buildMonitorPrefixTrees(resp MonitorResponse, n int /*@, ghost p perm @*/) (trees []*proofs.PrefixTree, rootHashes []*[sha256.Size]byte, err error) {
	trees = make([]*proofs.PrefixTree, 0, n)
	rootHashes = make([]*[sha256.Size]byte, 0, n)
	//@ unfold acc(resp.Inv(), p)
	for i := 0; i < n; i++ {
		prf := /*@ unfolding acc(resp.Search.Inv(), p/2) in @*/ resp.Search.Prefix_proofs[i]
		if tree, treeErr := prf.ToTree(resp.Binary_ladder); treeErr != nil {
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
Maybe discuss if we should do 4. 5. and 6. for...

*/

// VerifyUpdate verifies that a new version was correctly inserted (Section 9.1).
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
	if !determined {
		if resp.Prev_greatest != nil {
			//Verify that the new version is greater than the prev_greatest_version
			if resp.New_version <= *resp.Prev_greatest {
				resultErr = errors.New("new version not greater than previous greatest")
				determined = true
			}
		}
	}
	if !determined {
		if resp.Prev_insertion != nil {
			if resp.Insertion_pos <= *resp.Prev_insertion {
				resultErr = errors.New("insertion position not greater than previous insertion")
				determined = true
			}
		}
	}

	// Phase 3: Build prefix trees
	//@ fold acc(resp.Inv(), p)

	var trees []*proofs.PrefixTree
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
		//TODO: We need to implement prev_greatest
		prev_greatest := uint32(0)
		//@ unfold acc(resp.Inv(), p)
		if resp.Prev_greatest != nil {
			prev_greatest = *resp.Prev_greatest
		}

		//@ assert size <= uint64(len(trees))
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
// ============================= VerifyMonitor ======================================

// VerifyMonitor verifies that previously-searched label-version pairs remain in the
// log (Section 8.2 — Contact Monitoring).
// Uses CheckGreatest on all frontier nodes. For monitoring, res == -1 (hole) is a
// failure, while res == 0 or 1 are acceptable (version exists in log).
// The low(Version) property is preserved from the input monitoring map (established
// by prior VerifyLatest/VerifyUpdate calls), not re-proven via TStar.

// @ requires noPerm < p
// @ preserves st.Inv()
// @ requires acc(resp.Inv(), p)
// @ requires acc(label, p)
// @ requires low(len(label)) && (forall i int :: 0 <= i && i < len(label) ==> low(label[i]))
// @ requires acc(monitor_map)
// @ requires acc(config, p)
// @ requires low(resp.Full_tree_head.Tree_head.Tree_size)
// @ requires resp.Full_tree_head.Tree_head.Tree_size > 0
// @ requires resp.Full_tree_head.Tree_head.Tree_size <= uint64(len(resp.Search.Prefix_proofs))
// @ requires resp.Full_tree_head.RootHash != nil
// @ requires low(len(monitor_map))
// @ requires forall j int :: 0 <= j && j < len(monitor_map) ==> low(monitor_map[j].Version)
// @ requires forall j int :: 0 <= j && j < len(monitor_map) ==> low(monitor_map[j].Position)
// @ requires low(config.ReasonableMonitoringWindow)
// @ ensures acc(resp.Inv(), p) && acc(label, p) && acc(config, p)
// @ ensures acc(new_map)
// @ ensures err == nil ==> forall j int :: 0 <= j && j < len(new_map) ==> low(new_map[j].Version)
func VerifyMonitor(st *client.UserState, label []byte, resp MonitorResponse, monitor_map []client.MonitoringMapEntry, config *client.Configuration /*@, ghost p perm @*/) (new_map []client.MonitoringMapEntry, err error) {
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

	// Copy timestamps while resp.Search.Inv() is still accessible
	//@ unfold acc(resp.Search.Inv(), p/2)
	timestamps := make([]uint64, len(resp.Search.Timestamps))
	copy(timestamps, resp.Search.Timestamps /*@, p/4 @*/)
	//@ fold acc(resp.Search.Inv(), p/2)

	// Phase 2: Build prefix trees
	//@ fold acc(resp.Inv(), p)

	var trees []*proofs.PrefixTree
	var rootHashes []*[sha256.Size]byte
	if !determined {
		var buildErr error
		trees, rootHashes, buildErr = buildMonitorPrefixTrees(resp, n /*@, p @*/)
		if buildErr != nil {
			resultErr = buildErr
			determined = true
		}
	}

	// Phase 3: Per-entry direct path inspection (Section 8.2)
	new_map = make([]client.MonitoringMapEntry, 0)
	if !determined {
		search_tree := client.MkImplicitBinarySearchTree(size)
		distinguished := client.ComputeDistinguishedSet(search_tree, timestamps, config.ReasonableMonitoringWindow /*@, 1/2 @*/)
		//@ assert size <= uint64(len(trees))

		// Process entries
		//@ ghost var versions seq[uint32] = seq[uint32]{}


		//@ invariant acc(monitor_map)
		//@ invariant acc(new_map)
		//@ invariant acc(trees)
		//@ invariant acc(rootHashes)
		//@ invariant acc(label, p)
		//@ invariant acc(config, p)
		//@ invariant search_tree != nil && acc(search_tree.Inv(), 1/4)
		//@ invariant acc(distinguished)
		//@ invariant low(len(distinguished))
		//@ invariant forall j int :: 0 <= j && j < len(distinguished) ==> low(distinguished[j])
		//@ invariant size <= uint64(len(trees))
		//@ invariant forall i int :: i >= 0 && i < len(trees) ==> acc(&trees[i])
		//@ invariant forall i int :: {&trees[i]} i >= 0 && i < len(trees) ==> acc(trees[i])
		//@ invariant forall i int :: i >= 0 && i < len(trees) ==> trees[i] != nil
		//@ invariant 0 <= mIdx && mIdx <= len(monitor_map)
		//@ invariant low(mIdx)
		//@ invariant !determined ==> resultErr == nil
		//@ invariant low(versions)
		//@ invariant len(versions) == len(new_map)
		//@ invariant forall j int :: 0 <= j && j < len(new_map) ==> new_map[j].Version == versions[j]
		//@ invariant forall j int :: 0 <= j && j < len(monitor_map) ==> low(monitor_map[j].Version)
		//@ invariant forall j int :: 0 <= j && j < len(monitor_map) ==> low(monitor_map[j].Position)
		for mIdx := 0; mIdx < len(monitor_map); mIdx++ {
			entry := monitor_map[mIdx]
			//@ assert low(entry.Version)
			//@ assert low(entry.Position)
			newPosition := entry.Position

			// All distinguished access is OUTSIDE if !determined so both
			// executions touch distinguished identically (preserves low() in hyper mode)
			isDistinguished := false
			entryPosInt := int(entry.Position)
			if entryPosInt >= 0 && entryPosInt < len(distinguished) {
				isDistinguished = distinguished[entryPosInt]
			}

			// Compute pathRight unconditionally when !isDistinguished
			// (isDistinguished is low(), so both executions take the same branch)
			pathRight := make([]uint64, 0)
			if !isDistinguished {
				pathRight = client.DirectPathRight(search_tree, entry.Position, distinguished /*@, 1/8 @*/)
			}


			tVal := uint64(entry.Version)
			//@ invariant acc(pathRight)
			//@ invariant acc(trees)
			//@ invariant acc(rootHashes)
			//@ invariant acc(label, p)
			//@ invariant acc(search_tree.Inv(), 1/4)
			//@ invariant acc(distinguished)

			//Distinguished nodes are low as they are public (Otherwise it doesn't make sense to make them as checkpoints)
			
			//@ invariant low(len(distinguished))
			//@ invariant forall j int :: 0 <= j && j < len(distinguished) ==> low(distinguished[j])
			//@ invariant size <= uint64(len(trees))
			//@ invariant forall i int :: i >= 0 && i < len(trees) ==> acc(&trees[i])
			//@ invariant forall i int :: {&trees[i]} i >= 0 && i < len(trees) ==> acc(trees[i])
			//@ invariant forall i int :: i >= 0 && i < len(trees) ==> trees[i] != nil
			//@ invariant 0 <= pIdx && pIdx <= len(pathRight)
			//@ invariant !determined ==> resultErr == nil
			for pIdx := 0; pIdx < len(pathRight); pIdx++ {
				if !determined {
					pos := pathRight[pIdx]
					posIdx := int(pos)
					if posIdx < 0 || posIdx >= len(trees) {
						resultErr = errors.New("monitoring check failed: position out of bounds")
						determined = true
					} else {
						Prefix_tree := trees[posIdx]
						rootHash := rootHashes[posIdx]
						if Prefix_tree != nil {
							steps /*@, tStarIdx @*/ := client.FullBinaryLadderSteps_with_tstar(tVal)

							//@ ghost var labelSeq seq[byte] = getContent(label)
							//@ ghost var rootHashSeq seq[byte] = getContent(rootHash[:])

							cgRes, cgErr := client.CheckGreatest(Prefix_tree, steps, label, tVal, rootHash[:], size /*@, tStarIdx, labelSeq, rootHashSeq @*/)
							if cgErr != nil {
								resultErr = cgErr
								determined = true
							} else if cgRes == -1 {
								// Hole found: version not in log
								resultErr = errors.New("monitoring check failed: version not included")
								determined = true
							} else {
								// Success: advance position
								newPosition = pos
							}
						}
					}
				}
			}

			// Always append to keep new_map/versions in sync across executions
			newEntry := client.MonitoringMapEntry{
				Position: newPosition,
				Version:  entry.Version,
			}
			new_map = append( /*@ perm(1/2), @*/ new_map, newEntry)
			//@ ghost versions = versions ++ seq[uint32]{entry.Version}
		}
	}

	if determined {
		err = resultErr
	} else {
		err = nil
	}
	return new_map, err
}
