package monitor

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
// ============================= Monitor Types ======================================

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
// ============================= buildMonitorPrefixTrees ============================

// buildMonitorPrefixTrees constructs prefix trees from a MonitorResponse's
// prefix proofs. Analogous to client.buildPrefixTrees but for monitor responses.
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
func buildMonitorPrefixTrees(resp MonitorResponse, n int /*@, ghost p perm @*/) (trees []*prefixtree.PrefixTree, rootHashes []*[sha256.Size]byte, err error) {
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
// ============================= VerifyMonitor ======================================

// VerifyMonitor verifies that previously-searched label-version pairs remain in
// the log (Section 8.2 — Contact Monitoring). For each entry in monitor_map, it
// computes the direct path right from the entry's position to the first
// distinguished node, then calls CheckGreatest at each position along that path.
// Entries where a "hole" is found (version not included) cause a failure.
//
// The function updates the user's tree view, builds prefix trees, computes the
// distinguished set using the reasonable monitoring window, and produces an
// updated monitoring map with new positions.
//
// Preconditions: st.Inv() must hold, resp must satisfy Inv(), label must be
// non-nil and low, tree size must be low and > 0, all monitor_map entries'
// Version and Position must be low, config.ReasonableMonitoringWindow must be low.
//
// Postconditions (hyper-property): if err==nil, the output new_map has low length
// and all entries have low Version and Position — two executions with the same
// root hash agree on the monitoring map contents.
//
// Returns:
//   - new_map: updated monitoring map with new positions for each entry
//   - err: non-nil if any monitoring check fails
//
//TODO: I think the current spec is too weak and we need other implementations to make sure that the security property is implemented
// The issue here is that the current implementation shows the non-equivocation but not the consistency that the users will reach to a consensus that they'll see

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
// @ ensures err == nil ==> low(len(new_map))
// @ ensures err == nil ==> forall j int :: 0 <= j && j < len(new_map) ==> low(new_map[j].Version)
// @ ensures err == nil ==> forall j int :: 0 <= j && j < len(new_map) ==> low(new_map[j].Position)
func VerifyMonitor(st *client.UserState, label []byte, resp MonitorResponse, monitor_map []client.MonitoringMapEntry, config *client.Configuration /*@, ghost p perm @*/) (new_map []client.MonitoringMapEntry, err error) {
	//@ unfold acc(resp.Inv(), p)

	determined := false
	var resultErr error = nil

	// Capture size and n before folding so Gobra retains size <= n
	size := resp.Full_tree_head.Tree_head.Tree_size
	n := len(resp.Search.Prefix_proofs)

	// Copy timestamps while resp.Search.Inv() is still accessible
	//@ unfold acc(resp.Search.Inv(), p/2)
	timestamps := make([]uint64, len(resp.Search.Timestamps))
	copy(timestamps, resp.Search.Timestamps /*@, p/4 @*/)
	//@ fold acc(resp.Search.Inv(), p/2)

	// Phase 2: Build prefix trees
	//@ fold acc(resp.Inv(), p)

	var trees []*prefixtree.PrefixTree
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
		// Process entries
		//@ ghost var versions seq[uint32] = seq[uint32]{}
		//@ ghost var positions seq[uint64] = seq[uint64]{}

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
		//@ invariant low(positions)
		//@ invariant len(positions) == len(new_map)
		//@ invariant forall j int :: 0 <= j && j < len(new_map) ==> new_map[j].Position == positions[j]
		//@ invariant len(new_map) == mIdx
		//@ invariant low(len(new_map))
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
			//@ invariant low(pIdx)
			//@ invariant low(len(pathRight))
			//@ invariant forall j int :: 0 <= j && j < len(pathRight) ==> low(pathRight[j])
			//@ invariant low(newPosition)
			//@ invariant !determined ==> resultErr == nil
			for pIdx := 0; pIdx < len(pathRight); pIdx++ {
				pos := pathRight[pIdx]
				posIdx := int(pos)
				if !determined {
					if posIdx < 0 || posIdx >= len(trees) {
						resultErr = errors.New("monitoring check failed: position out of bounds")
						determined = true
					} else {
						Prefix_tree := trees[posIdx]
						rootHash := rootHashes[posIdx]
						if Prefix_tree != nil {
							cgRes, cgErr := client.CheckGreatest(Prefix_tree, label, tVal, rootHash[:], size)
							if cgErr != nil {
								resultErr = cgErr
								determined = true
							} else if cgRes == -1 {
								// Hole found: version not in log
								resultErr = errors.New("monitoring check failed: version not included")
								determined = true
							}
						}
					}
				}
				// Always advance position — both executions stay in sync
				newPosition = pos
			}

			// Always append to keep new_map/versions in sync across executions
			newEntry := client.MonitoringMapEntry{
				Position: newPosition,
				Version:  entry.Version,
			}
			new_map = append( /*@ perm(1/2), @*/ new_map, newEntry)
			//@ ghost versions = versions ++ seq[uint32]{entry.Version}
			//@ ghost positions = positions ++ seq[uint64]{newPosition}
		}
	}

	// UpdateView: only update state after full verification succeeds
	if !determined {
		//@ unfold acc(resp.Inv(), p)
		updateErr := st.UpdateView(resp.Full_tree_head, resp.Search /*@, p/2 @*/)
		//@ fold acc(resp.Inv(), p)
		if updateErr != nil {
			err = updateErr
		} else {
			err = nil
		}
	} else {
		err = resultErr
	}
	return new_map, err
}
