package client

import (
	"crypto/sha256"
	"errors"

	"github.com/felixlinker/keytrans-verification/pkg/prefixtree"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// Package client implements the client-side verification logic for key
// transparency. It provides functions to verify that a transparency log
// correctly reports the latest version of a user's key, using binary ladder
// proofs and prefix tree lookups.
//
// The core verification functions are:
//   - VerifyLatest: verifies a search response and checks that the returned
//     version is the latest, combining update verification with a greatest
//     version check.
//   - VerifyLatestKey: verifies a claimed greatest version against all frontier
//     nodes of the implicit binary search tree, ensuring no greater version
//     exists in the log.
//   - CheckGreatest: checks a single prefix tree against the binary ladder
//     steps to confirm consistency with the claimed greatest version.
//
// All exported verification functions carry Gobra specifications for formal
// verification of hyperproperties (information flow) in extended hyper mode.

// ##(--hyperMode extended --enableExperimentalHyperFeatures)

/*@
//Helper functions
//Compare the bytes of the arrays
ghost
requires acc(r1, _) && acc(r2, _)
decreases
pure func BytesEqual(r1, r2 []byte) bool {
	return len(r1) == len(r2) &&
		forall i int :: {r1[i], r2[i]} 0 <= i && i < len(r1) ==> r1[i] == r2[i]
}

// PrefixTreesInv encapsulates per-element permissions for prefix tree slices.
// Reduces quantifier count in the SIF product program.
pred PrefixTreesInv(trees []*prefixtree.PrefixTree) {
		forall i int :: {&trees[i]} i >= 0 && i < len(trees) ==> acc(&trees[i]) && trees[i].Inv() && trees[i] != nil
}

// RootHashesInv encapsulates per-element permissions for root hash slices.
pred RootHashesInv(hashes []*[sha256.Size]byte) {
	forall i int :: {&hashes[i]} i >= 0 && i < len(hashes) ==> acc(&hashes[i]) && acc(hashes[i])
}

ghost
decreases
pure func min(a, b uint64) uint64 {
  return a < b ? a : b
}

ghost
decreases
pure func max(a, b uint64) uint64 {
  return a > b ? a : b
}

// IsTStar captures: tStarVal == TStar(min(t1,t2), max(t1,t2))
// AND min(t1,t2) < tStarVal <= max(t1,t2) if t1 != t2
ghost
decreases
opaque
pure func IsTStar(tStarVal, t1, t2 uint64) bool {
  return (t1 < 0 || t2 < 0) ? true :  // Cannot happen for uint64, but needed as proof hint
    t1 == t2 ? true :
        tStarVal == TStarBetween(t1, t2)
}

ghost
requires min(t1,t2) >= 0 && max(t1,t2) > 0
ensures t1 != t2 ==> min(t1, t2) < res && res <= max(t1, t2)
decreases
pure func TStarBetween(t1, t2 uint64) (res uint64) {
  return t1 == t2 ? 0 :
    t1 < t2 ? proofs.TStar_pure(t1, t2) : proofs.TStar_pure(t2, t1)
}


ghost
requires acc(arr, _)
decreases
pure
func getContent(arr []byte) (res seq[byte]) {
  return getByteContent(arr, 0)
}

ghost
requires acc(arr, _)
requires 0 <= idx && idx <= len(arr)
decreases len(arr) - idx
opaque
pure
func getByteContent(arr []byte, idx int) (res seq[byte]) {
  return idx == len(arr) ? seq[byte]{} : seq[byte]{arr[idx]} ++ getByteContent(arr, idx + 1)
}

// Lemma: returns a low sequence equal to getByteContent(data, idx).
// Recurses matching getByteContent's structure. Workaround for Gobra issue #974:
// low() cannot directly wrap a recursive pure function, so we build the result
// imperatively (making low() provable) while ensuring equality with getByteContent.
ghost
requires p > noPerm
requires acc(data, p)
requires low(len(data))
requires 0 <= idx && idx <= len(data)
requires low(idx)
requires forall i int :: {data[i]} 0 <= i && i < len(data) ==> low(data[i])
ensures acc(data, p)
ensures low(len(data))
ensures forall i int :: {data[i]} 0 <= i && i < len(data) ==> low(data[i])
ensures low(result)
ensures result == getByteContent(data, idx)
decreases len(data) - idx
func getByteContentIsLow(data []byte, idx int, ghost p perm) (result seq[byte]) {
  if idx == len(data) {
    result = seq[byte]{}
  } else {
    tail := getByteContentIsLow(data, idx + 1, p)
    result = seq[byte]{data[idx]} ++ tail
  }
  // reveal after permissions are restored so the body is visible on the correct heap
  revealedContent := reveal getByteContent(data, idx)
}

// Build low ghost seq from a *[sha256.Size]byte array
ghost
requires acc(arr, 1/2)
requires forall k int :: {arr[k]} 0 <= k && k < sha256.Size ==> low(arr[k])
ensures acc(arr, 1/2)
ensures low(result)
decreases
func buildLowSeqFromHash(arr *[sha256.Size]byte) (result seq[byte]) {
  i := 0

  invariant acc(arr, 1/2)
  invariant 0 <= i && i <= sha256.Size
  invariant low(i)
  invariant low(result)
  invariant forall k int :: {arr[k]} 0 <= k && k < sha256.Size ==> low(arr[k])
  decreases sha256.Size - i
  for i < sha256.Size {
    result = result ++ seq[byte]{arr[i]}
    i = i + 1
  }
}


ghost
requires n >= 0
requires low(n)
requires forall i int :: {&hashes[i]} 0 <= i && i < n ==> acc(&hashes[i]) && acc(hashes[i])
requires forall i int :: {&hashes[i]} 0 <= i && i < n ==> forall k int :: {hashes[i][k]} 0 <= k && k < sha256.Size ==> low(hashes[i][k])
ensures low(result)
ensures len(result) == n
ensures forall i int :: {&hashes[i]} 0 <= i && i < n ==> acc(&hashes[i]) && acc(hashes[i])
decreases
func buildRootHashContents(hashes []*[sha256.Size]byte, n int) (result seq[seq[byte]]) {
  i := 0

  invariant 0 <= i && i <= n
  invariant low(i)
  invariant low(n)
  invariant low(result)
  invariant len(result) == i
  invariant forall j int :: {&hashes[j]} 0 <= j && j < n ==> acc(&hashes[j]) && acc(hashes[j])
  invariant forall j int :: {&hashes[j]} 0 <= j && j < n ==> forall k int :: {hashes[j][k]} 0 <= k && k < sha256.Size ==> low(hashes[j][k])
  decreases n - i
  for i < n {
    s := buildLowSeqFromHash(hashes[i])
    result = result ++ seq[seq[byte]]{s}
    i = i + 1
  }
}
@*/

type PT interface {
	// Returns non-nil if we can prove that the prefix tree contains a key for the
	// label and version pair provided. Returns nil if we can prove that the
	// prefix tree does not contain a key for the label and version pair provided.
	// Returns error in any other case.
	GetCommitment(Label []byte, Version uint64, RootHash []byte) (res []byte, err error)
}

type TreeHead struct {
	Tree_size uint64
	Signature []byte
}

/*@
pred (t TreeHead) Inv() {
	acc(t.Signature)
}
@*/

type FullTreeHead struct {
	Tree_head TreeHead
	RootHash  []byte // Added RootHash for the prefixtree comparison if needed, currently a stub implementation
	// TODO: AuditorTreeHead auditor_tree_head
}

/*@
pred (f FullTreeHead) Inv() {
	f.Tree_head.Inv() && acc(f.RootHash)
}

ghost
decreases
requires acc(f.Inv(), _)
pure func (f FullTreeHead) Size() uint64 {
	return unfolding acc(f.Inv(), _) in f.Tree_head.Tree_size
}
@*/

type SearchRequest struct {
	Last  *uint32
	Label []byte
	// TODO: optional<uint32> version
}

/*@
pred (s SearchRequest) Inv() {
	acc(s.Last) && acc(s.Label)
}
@*/

type SearchResponse struct {
	Full_tree_head FullTreeHead
	Version        *uint32
	Binary_ladder  []proofs.BinaryLadderStep
	Search         proofs.CombinedTreeProof
	Inclusion      proofs.InclusionProof
	Opening        []byte
	Value          proofs.UpdateValue // value associated with queried label
}

/*@
pred (s SearchResponse) Inv() {
	s.Full_tree_head.Inv() &&
	(s.Version != nil ==> acc(s.Version)) &&
	acc(s.Binary_ladder) &&
	s.Search.Inv() &&
	s.Inclusion.Inv() &&
	acc(s.Opening) &&
	s.Value.Inv()
}
@*/

// @ requires noPerm < p
// @ preserves st.Inv()
// @ requires acc(config, p)
// @ requires acc(query.Inv(), p)
// @ requires unfolding acc(query.Inv(), p) in query.Label != nil
// @ requires unfolding acc(query.Inv(), p) in low(len(query.Label)) && forall i int :: { query.Label[i] } 0 <= i && i < len(query.Label) ==> low(query.Label[i])
// @ requires acc(resp.Inv(), p)
// @ requires resp.Version != nil
// @ requires unfolding acc(resp.Inv(), p) in *resp.Version >= 0
// @ requires resp.Full_tree_head.RootHash != nil
// @ requires resp.Full_tree_head.Tree_head.Tree_size > 0
// @ requires resp.Full_tree_head.Tree_head.Tree_size <= uint64(len(resp.Search.Prefix_proofs))
// @ requires low(resp.Full_tree_head.Tree_head.Tree_size)
// @ requires low(len(resp.Search.Prefix_proofs))
// @ ensures err != nil ==> acc(resp.Inv(), p)
// @ ensures err == nil ==> acc(resp.Version, p) && low(*resp.Version)
func (st *UserState) VerifyLatest(query SearchRequest, resp SearchResponse, config *Configuration /*@, ghost p perm @*/) (res *proofs.UpdateValue, err error) {
	//@ unfold acc(resp.Inv(), p)
	determined := false

	// Phase 1: UpdateView
	updateErr := st.UpdateView(resp.Full_tree_head, resp.Search /*@, p/2 @*/)
	if updateErr != nil {
		err = updateErr
		determined = true
	}

	// Phase 2: Validation checks (resp.Inv() still unfolded)
	if !determined {
		if resp.Version == nil {
			err = errors.New("no version provided")
			determined = true
		}
	}
	if !determined {
		if *resp.Version < 0 {
			err = errors.New("Version is negative")
			determined = true
		}
	}
	if !determined {
		if len(resp.Search.Prefix_roots) != 0 {
			err = errors.New("prefix roots provided")
			determined = true
		}
	}
	if !determined {
		ladderIndices /*@, idx @*/ := proofs.FullBinaryLadderSteps(uint64(*resp.Version) /*@, 0 @*/)
		if len(resp.Binary_ladder) != len(ladderIndices) {
			err = errors.New("length of binary ladder does not match greatest version")
			determined = true
		}
	}

	// Phase 3: Build prefix trees
	n := len(resp.Search.Prefix_proofs)
	//@ fold acc(resp.Inv(), p)

	var trees []*prefixtree.PrefixTree
	var rootHashes []*[sha256.Size]byte
	//@ ghost var rhContents seq[seq[byte]] = seq[seq[byte]]{}
	if !determined {
		var buildErr error
		trees, rootHashes, buildErr = buildPrefixTrees(resp, n /*@, p @*/)
		if buildErr != nil {
			err = buildErr
			determined = true
		} else {
			//@ rhContents = buildRootHashContents(rootHashes, n)
			//@ fold acc(RootHashesInv(rootHashes), p)
		}
	}

	// Phase 4: VerifyLatestKey
	decision := false
	if !determined {
		//@ unfold acc(resp.Inv(), p)
		//@ unfold acc(resp.Full_tree_head.Inv(), p)
		//@ unfold acc(query.Inv(), p)
		size := resp.Full_tree_head.Tree_head.Tree_size
		monitoringMap := make([]MonitoringMapEntry, 0)
		decision, err = VerifyLatestKey(trees, rootHashes, size, query, resp, monitoringMap, config /*@, rhContents, p @*/)

		if !decision || err != nil {
			//@ fold acc(resp.Full_tree_head.Inv(), p)
			//@ fold acc(resp.Inv(), p)
			if err == nil {
				err = errors.New("Query response does not contain latest version")
			}
			determined = true
		}
	}

	// Phase 5: Single return
	if !determined && decision {
		// VerifyLatestKey ensures: err == nil && res ==> low(*resp.Version)
		// Don't fold resp.Inv() — keep acc(resp.Version, p) for postcondition
		//@ unfold acc(resp.Value.Inv(), p)
		res = &proofs.UpdateValue{Value: resp.Value.Value}
		//@ fold acc(resp.Value.Inv(), p)
		err = nil
	} else {
		res = nil
	}
	return res, err
}

// @ requires target >= 0
// @ ensures acc(r1)
// @ ensures forall j int :: {r1[j]} j >= 0 && j < len(r1) ==> r1[j] >= 0
// @ ensures 0 <= tStarIdx && tStarIdx < len(r1)
// @ ensures low(r1[tStarIdx])
// @ ensures IsTStar(r1[tStarIdx], rel(target, 0), rel(target, 1))
func FullBinaryLadderSteps_with_tstar(target uint64) (r1 []uint64 /*@, ghost tStarIdx int @*/) {
	assert false // TODO
	// r1 = proofs.FullBinaryLadderSteps_wrapper(target)
	// tStarIdx = findTStarIdx(r1, target)
	return
}

// CheckGreatest wraps FullBinaryLadderSteps_with_tstar and CheckCommitment
// into a single function to create a verification boundary. The SMT solver verifies
// this function once; at the call site in VerifyLatestKey, it only reasons about the
// postcondition, reducing the proof obligation in the main loop.
// @ requires p > noPerm
// @ requires label != nil
// @ requires acc(label, p)
// @ requires acc(RootHash, p)
// @ requires prefixTree != nil ==> acc(prefixTree.Inv(), p)
// @ requires low(labelSeq)
// @ requires low(RootHashSeq)
// @ requires t >= 0
// @ ensures prefixTree != nil ==> acc(prefixTree.Inv(), p)
// @ ensures acc(label, p)
// @ ensures acc(RootHash, p)
// @ ensures err == nil && res == 0 ==> low(t)
func CheckGreatest(prefixTree *prefixtree.PrefixTree, label []byte, t uint64, RootHash []byte, size uint64 /*@, ghost labelSeq seq[byte], ghost RootHashSeq seq[byte], ghost p perm@*/) (res int, err error) {
	steps /*@, tStarIdx @*/ := FullBinaryLadderSteps_with_tstar(t)
	return CheckCommitment(prefixTree, steps, label, t, RootHash, size /*@, tStarIdx, labelSeq, RootHashSeq, p@*/)
}

// CheckCommitment iterates over the binary ladder steps and queries the prefix
// tree at each step to check consistency with t being the greatest version.
// Returns:
//   -1: a version at or below t is absent (gap detected)
//    0: all steps are consistent (t is the greatest version)
//   +1: a version above t is present (greater version exists)
//

// @ requires p > noPerm
// @ requires label != nil
// @ requires acc(label, p)
// @ requires acc(RootHash, p)
// @ requires acc(steps,p)
// @ requires prefixTree != nil ==> acc(prefixTree.Inv(), p)
// @ requires low(labelSeq)
// @ requires low(RootHashSeq)
// @ requires t >= 0
// @ requires forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> steps[i] >= 0
// @ requires 0 <= tStarIdx && tStarIdx < len(steps)
// @ requires low(steps[tStarIdx])
// @ requires IsTStar(steps[tStarIdx], rel(t, 0), rel(t, 1))
// @ ensures prefixTree != nil ==> acc(prefixTree.Inv(), p)
// @ ensures acc(label, p)
// @ ensures acc(RootHash, p)
// @ ensures err == nil && res == 0 ==> low(t)
func CheckCommitment(prefixTree *prefixtree.PrefixTree, steps []uint64, label []byte, t uint64, RootHash []byte, size uint64 /*@, ghost tStarIdx int, ghost labelSeq seq[byte], ghost RootHashSeq seq[byte], ghost p perm@*/) (res int, err error) {
	resultRes := 0
	var resultErr error
	determined := false // this flag encodes early returns, which are not yet supported by Gobra's hypermode
	//@ ghost tStar := steps[tStarIdx]
	//@ ghost revealedIsTStar := reveal IsTStar(steps[tStarIdx], rel(t, 0), rel(t, 1))

	//@ non_incl_expected := prefixtree.GetCommitmentIsDeterministic(labelSeq, tStar, RootHashSeq) && tStar <= t
	//@ incl_expected := !prefixtree.GetCommitmentIsDeterministic(labelSeq, tStar, RootHashSeq) && t < tStar

	// after visiting `tStarIdx` and successfully passing all checks (i.e., `!determined`), one of the following two cases will hold.
	// as desired, this contradicts `IsTStar(tStar, rel(t, 0), rel(t, 1))` unless `low(t)` holds, which establishes the postcondition.

	//@ invariant prefixTree != nil ==> acc(prefixTree.Inv(), p)
	//@ invariant acc(RootHash, p)
	//@ invariant acc(label,p)
	//@ invariant acc(steps,p)
	//@ invariant forall i int :: {steps[i]} 0 <= i && i < len(steps) ==> steps[i] >= 0
	//@ invariant 0 <= idx && idx <= len(steps)
	//@ invariant tStar == steps[tStarIdx]
	//@ invariant IsTStar(steps[tStarIdx], rel(t, 0), rel(t, 1))
	//@ invariant determined ==> resultRes != 0
	//@ invariant !determined ==> resultRes == 0 && resultErr == nil
	//@ invariant tStarIdx < idx && !determined ==> non_incl_expected || incl_expected
	for idx := 0; idx < len(steps); idx++ {
		if !determined {
			step := steps[idx]
			commitment, err := prefixTree.GetCommitment(label, step, RootHash /*@, labelSeq, RootHashSeq, p@*/)
			if err != nil {
				if !determined {
					resultRes = 404
					resultErr = err
					determined = true
				}
			} else {
				incl := commitment != nil
				if !incl {
					if step <= t {
						resultRes = -1
						determined = true
					}
				} else {
					if t < step {
						resultRes = 1
						determined = true
					}
				}
				/*@
				ghost if idx == tStarIdx {
					assert !determined ==> (non_incl_expected || incl_expected)
				}
				@*/
			}
		}
	}
	return resultRes, resultErr

}

type MonitoringMapEntry struct {
	Position uint64
	Version  uint32
}

// @ requires noPerm < p
// @ requires acc(config, p)
// @ requires acc(monitor_map)
// @ requires acc(query.Label, p)
// @ requires query.Label != nil
// @ requires low(len(query.Label)) && forall i int :: {query.Label[i]} 0 <= i && i < len(query.Label) ==> low(query.Label[i])
// @ requires acc(resp.Version, p)
// @ requires acc(resp.Full_tree_head.RootHash, p)
// @ requires resp.Version != nil
// @ requires *resp.Version >= 0
// @ requires resp.Full_tree_head.RootHash != nil
// @ requires acc(PrefixTreesInv(prefixTrees), p)
// @ requires acc(RootHashesInv(prefixRootHash), p)
// @ requires size > 0 && size <= uint64(len(prefixTrees)) && size <= uint64(len(prefixRootHash))
// @ requires len(rootHashContents) == len(prefixRootHash)
// @ requires low(size)
// @ requires low(rootHashContents)
// @ ensures acc(config, p)
// @ ensures acc(query.Label, p)
// @ ensures acc(resp.Version, p)
// @ ensures resp.Full_tree_head.RootHash != nil ==> acc(resp.Full_tree_head.RootHash, p)
// @ ensures acc(prefixTrees, p)
// @ ensures acc(prefixRootHash, p)
// @ ensures err == nil && res ==> low(*resp.Version)
func VerifyLatestKey(prefixTrees []*prefixtree.PrefixTree, prefixRootHash []*[sha256.Size]byte, size uint64, query SearchRequest, resp SearchResponse, monitor_map []MonitoringMapEntry, config *Configuration /*@, ghost rootHashContents seq[seq[byte]], ghost p perm @*/) (res bool, err error) {
	t := resp.Version //Claimed greatest version
	tVal := uint64(*t)
	search_tree := MkImplicitBinarySearchTree(size)
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
	//@ ghost var labelSeq seq[byte] = getByteContentIsLow(query.Label, 0, p)

	//@ invariant acc(PrefixTreesInv(prefixTrees), p)
	//@ invariant acc(RootHashesInv(prefixRootHash), p)
	//@ invariant acc(frontiers)
	//@ invariant acc(resp.Version, p)
	//@ invariant acc(resp.Full_tree_head.RootHash, p)
	//@ invariant acc(query.Label, p)
	//@ invariant acc(config, p)
	//@ invariant tVal == uint64(*t)
	//@ invariant tVal >= 0
	//@ invariant 0 <= fIdx && fIdx <= len(frontiers) - 1
	//@ invariant len(frontiers) > 0
	//@ invariant len(rootHashContents) == len(prefixRootHash)
	//@ invariant forall i int :: {frontiers[i]} i >= 0 && i < len(frontiers) ==> frontiers[i]>=0 && frontiers[i] < uint64(len(prefixTrees))
	//@ invariant forall i int :: {frontiers[i]} i >= 0 && i < len(frontiers) ==> frontiers[i]>=0 && frontiers[i] < uint64(len(prefixRootHash))
	//@ invariant determined ==> !resultRes
	//@ invariant !determined ==> resultRes && resultErr == nil
	//@ invariant low(fIdx)
	//@ invariant low(size)
	//@ invariant low(labelSeq)
	//@ invariant low(rootHashContents)
	//@ invariant low(len(frontiers)) && forall j int :: {frontiers[j]} j>= 0 && j < len(frontiers) ==> low(frontiers[j])
	for fIdx := 0; fIdx < len(frontiers)-1; fIdx++ {
		frontier := frontiers[fIdx]
		if !determined {
			//@ assert frontier >= 0 && int(frontier) < len(prefixTrees)
			//@ unfold acc(PrefixTreesInv(prefixTrees), p)
			//@ unfold acc(RootHashesInv(prefixRootHash), p)
			Prefix_tree := prefixTrees[frontier]
			if prefixTrees[frontier] == nil {
				//@ fold acc(PrefixTreesInv(prefixTrees), p)
				//@ fold acc(RootHashesInv(prefixRootHash), p)
				resultRes = false
				resultErr = errors.New("prefix tree is nil")
				determined = true
			} else {
				rootHash := prefixRootHash[frontier]
				if frontier >= size {
					//@ fold acc(PrefixTreesInv(prefixTrees), p)
					//@ fold acc(RootHashesInv(prefixRootHash), p)
					resultRes = false
					resultErr = errors.New("version out of bounds")
					determined = true
				}
				if !determined {
					//@ ghost var rootHashSeq seq[byte] = rootHashContents[int(frontier)]
					LtGtOrEq, cgErr := CheckGreatest(Prefix_tree, query.Label, tVal, rootHash[:], size /*@, labelSeq, rootHashSeq, p@*/)
					//@ fold acc(PrefixTreesInv(prefixTrees), p)
					//@ fold acc(RootHashesInv(prefixRootHash), p)
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
	}

	// Process last frontier separately
	if !determined {
		//@ unfold acc(PrefixTreesInv(prefixTrees), p)
		//@ unfold acc(RootHashesInv(prefixRootHash), p)
		frontier := frontiers[len(frontiers)-1]
		Prefix_tree := prefixTrees[frontier]
		if prefixTrees[frontier] == nil {
			//@ fold acc(PrefixTreesInv(prefixTrees), p)
			//@ fold acc(RootHashesInv(prefixRootHash), p)
			resultRes = false
			resultErr = errors.New("prefix tree is nil")
			determined = true
		} else {
			rootHash := prefixRootHash[frontier]
			if frontier >= size {
				//@ fold acc(PrefixTreesInv(prefixTrees), p)
				//@ fold acc(RootHashesInv(prefixRootHash), p)
				resultRes = false
				resultErr = errors.New("version out of bounds")
				determined = true
			}
			if !determined {
				//@ ghost var rootHashSeq seq[byte] = rootHashContents[int(frontier)]
				LtGtOrEq, cgErr := CheckGreatest(Prefix_tree, query.Label, tVal, rootHash[:], size /*@, labelSeq, rootHashSeq, p@*/)
				//@ fold acc(PrefixTreesInv(prefixTrees), p)
				//@ fold acc(RootHashesInv(prefixRootHash), p)
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
	}

	if terminalLogEntry == -1 && resultErr == nil {
		resultRes = false
		resultErr = errors.New("Claimed Version is not found.")
	}
	if frontiers[0] < uint64(terminalLogEntry) && config.Mode == 1 {
		entry := MonitoringMapEntry{
			Position: uint64(len(frontiers) - 1),
			Version:  *t,
		}
		monitor_map = append( /*@ perm(1/2), @*/ monitor_map, entry)
	}

	//@ unfold acc(PrefixTreesInv(prefixTrees), p)
	//@ unfold acc(RootHashesInv(prefixRootHash), p)
	return resultRes, resultErr
}

// buildPrefixTrees constructs prefix trees from the response's prefix proofs.
// @ requires noPerm < p
// @ requires acc(resp.Inv(), p)
// @ ensures acc(resp.Inv(), p)
// @ ensures resp.Version != nil ==> (unfolding acc(resp.Inv(), p) in *resp.Version >= 0)
// @ ensures err == nil ==> len(trees) == n
// @ ensures err == nil ==> acc(PrefixTreesInv(trees), p)
// @ ensures err == nil ==> len(rootHashes) == n
// @ ensures err == nil ==> forall j int :: {&rootHashes[j]} 0 <= j && j < n ==> acc(&rootHashes[j]) && acc(rootHashes[j])
// @ ensures err == nil ==> forall j int :: {&rootHashes[j]} 0 <= j && j < n ==> forall k int :: {rootHashes[j][k]} 0 <= k && k < sha256.Size ==> low(rootHashes[j][k])
// @ trusted
func buildPrefixTrees(resp SearchResponse, n int /*@, ghost p perm @*/) (trees []*prefixtree.PrefixTree, rootHashes []*[sha256.Size]byte, err error) {
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
