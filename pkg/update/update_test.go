package update

import (
	"crypto/sha256"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/client"
	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/prefixtree"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ==================================================================================
// ================================== Helpers =======================================
// ==================================================================================

func buildSingleLeafTree(label []byte, version uint32) *prefixtree.PrefixTree {
	vrfInput := crypto.VrfInput{Label: label, Version: version}
	vrfHash := crypto.VRF_hash(nil, vrfInput)
	commitment := sha256.Sum256([]byte("test-commitment"))
	leaf := &proofs.PrefixLeaf{
		Vrf_output: vrfHash,
		Commitment: commitment,
	}
	tree := &prefixtree.PrefixTree{Leaf: leaf}
	tree.ComputeHash()
	return tree
}

func newUserState() *client.UserState {
	return &client.UserState{
		Size:                0,
		Full_subtrees:       []proofs.NodeValue{},
		Frontier_timestamps: []uint64{},
	}
}

func makeRootHash() []byte {
	h := sha256.Sum256([]byte("root"))
	return h[:]
}

func makeHashPtr() *[sha256.Size]byte {
	h := sha256.Sum256([]byte("root-hash"))
	return &h
}

// ==================================================================================
// ============================== VerifyUpdateKey Tests =============================
// ==================================================================================

func TestVerifyUpdateKey_VersionOutOfBounds(t *testing.T) {
	// new_version >= size → out of bounds
	label := []byte("alice")
	size := uint64(4)

	tree := buildSingleLeafTree(label, 0)
	trees := []*prefixtree.PrefixTree{tree, tree, tree, tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr(), makeHashPtr(), makeHashPtr(), makeHashPtr()}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	res, err := VerifyUpdateKey(trees, rootHashes, size, label, 5, 0, config)
	if err == nil {
		t.Fatal("VerifyUpdateKey should return error for version out of bounds")
	}
	if res {
		t.Error("VerifyUpdateKey should return false for version out of bounds")
	}
}

func TestVerifyUpdateKey_IsGreatest_SingleFrontier(t *testing.T) {
	// size=1, new_version=0, tree has (label, 0) included → success
	label := []byte("alice")
	size := uint64(1)

	tree := buildSingleLeafTree(label, 0)
	trees := []*prefixtree.PrefixTree{tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr()}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	res, err := VerifyUpdateKey(trees, rootHashes, size, label, 0, 0, config)
	if err != nil {
		t.Fatalf("VerifyUpdateKey returned unexpected error: %v", err)
	}
	if !res {
		t.Error("VerifyUpdateKey should return true when version is greatest")
	}
}

func TestVerifyUpdateKey_HoleDetected(t *testing.T) {
	// size=1, new_version=0 but tree has wrong version → hole
	label := []byte("alice")
	size := uint64(1)

	tree := buildSingleLeafTree(label, 99)
	trees := []*prefixtree.PrefixTree{tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr()}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	res, err := VerifyUpdateKey(trees, rootHashes, size, label, 0, 0, config)
	if err == nil {
		t.Fatal("VerifyUpdateKey should return error when hole is detected")
	}
	if res {
		t.Error("VerifyUpdateKey should return false when hole is detected")
	}
}

func TestVerifyUpdateKey_NilTree(t *testing.T) {
	// prefix tree is nil → error
	label := []byte("alice")
	size := uint64(1)

	trees := []*prefixtree.PrefixTree{nil}
	rootHashes := []*[sha256.Size]byte{makeHashPtr()}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	res, err := VerifyUpdateKey(trees, rootHashes, size, label, 0, 0, config)
	if err == nil {
		t.Fatal("VerifyUpdateKey should return error when prefix tree is nil")
	}
	if res {
		t.Error("VerifyUpdateKey should return false when prefix tree is nil")
	}
}

// ==================================================================================
// =============================== VerifyUpdate Tests ==============================
// ==================================================================================

func TestVerifyUpdate_NewVersionNotGreater(t *testing.T) {
	// new_version <= prev_greatest → error
	st := newUserState()
	label := []byte("alice")
	prevGreatest := uint32(5)
	resp := UpdateResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 4, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Prev_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 2, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		New_version:   3, // 3 <= 5 → error
		Prev_greatest: &prevGreatest,
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{{}, {}, {}, {}},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Prev_search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Values:   []proofs.UpdateValue{},
		Openings: [][]byte{},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	err := VerifyUpdate(st, label, resp, config)
	if err == nil {
		t.Fatal("VerifyUpdate should return error when new version <= prev greatest")
	}
}

func TestVerifyUpdate_InsertionPosNotGreater(t *testing.T) {
	// insertion_pos <= prev_insertion → error
	st := newUserState()
	label := []byte("alice")
	prevInsertion := uint64(10)
	resp := UpdateResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 4, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Prev_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 2, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		New_version:    6,
		Prev_greatest:  nil, // no previous greatest → skip that check
		Insertion_pos:  5,   // 5 <= 10 → error
		Prev_insertion: &prevInsertion,
		Binary_ladder:  []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{{}, {}, {}, {}},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Prev_search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Values:   []proofs.UpdateValue{},
		Openings: [][]byte{},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	err := VerifyUpdate(st, label, resp, config)
	if err == nil {
		t.Fatal("VerifyUpdate should return error when insertion pos <= prev insertion")
	}
}

// ==================================================================================
// ============================== VerifyHistory Tests ==============================
// ==================================================================================

func TestVerifyHistory_BuildPrefixTreesFails(t *testing.T) {
	// Invalid PrefixProof (Results without matching Binary_ladder) → build error.
	label := []byte("alice")
	resp := UpdateResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Prev_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		New_version:   0,
		Prev_greatest: nil,
		Binary_ladder: []proofs.BinaryLadderStep{}, // empty → ToTree fails for non-empty Results
		Search: proofs.CombinedTreeProof{
			Timestamps: []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{
				{Results: []proofs.PrefixSearchResult{{}}, Elements: []proofs.NodeValue{}},
			},
			Prefix_roots: []proofs.NodeValue{},
		},
		Prev_search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Values:   []proofs.UpdateValue{},
		Openings: [][]byte{},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	err := VerifyHistory(label, resp, config)
	if err == nil {
		t.Fatal("VerifyHistory should return error when prefix tree build fails")
	}
}

func TestVerifyHistory_VersionNotInLog(t *testing.T) {
	// Copath-node trees → CheckGreatest returns error → VerifyUpdateKey fails.
	label := []byte("alice")
	dummyElement := proofs.NodeValue{}
	for i := range dummyElement {
		dummyElement[i] = byte(i)
	}

	resp := UpdateResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Prev_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		New_version:   0,
		Prev_greatest: nil, // start from version 0
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps: []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{
				{Results: []proofs.PrefixSearchResult{}, Elements: []proofs.NodeValue{dummyElement}},
			},
			Prefix_roots: []proofs.NodeValue{},
		},
		Prev_search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Values:   []proofs.UpdateValue{},
		Openings: [][]byte{},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	err := VerifyHistory(label, resp, config)
	if err == nil {
		t.Fatal("VerifyHistory should return error when version cannot be verified in log")
	}
}

func TestVerifyHistory_EmptyRange(t *testing.T) {
	// Prev_greatest > New_version → loop doesn't execute → success.
	label := []byte("alice")
	prevGreatest := uint32(5)
	dummyElement := proofs.NodeValue{}
	for i := range dummyElement {
		dummyElement[i] = byte(i)
	}

	resp := UpdateResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Prev_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		New_version:   3, // start = 6 > 3 → empty range
		Prev_greatest: &prevGreatest,
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps: []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{
				{Results: []proofs.PrefixSearchResult{}, Elements: []proofs.NodeValue{dummyElement}},
			},
			Prefix_roots: []proofs.NodeValue{},
		},
		Prev_search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Values:   []proofs.UpdateValue{},
		Openings: [][]byte{},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	err := VerifyHistory(label, resp, config)
	if err != nil {
		t.Fatalf("VerifyHistory should succeed when version range is empty: %v", err)
	}
}

func TestVerifyHistory_WithPrevGreatest(t *testing.T) {
	// Prev_greatest=0, New_version=0 → start=1 > 0 → empty range → success.
	// This verifies that the start offset is computed correctly.
	label := []byte("alice")
	prevGreatest := uint32(0)
	dummyElement := proofs.NodeValue{}
	for i := range dummyElement {
		dummyElement[i] = byte(i)
	}

	resp := UpdateResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Prev_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		New_version:   0, // start = 1 > 0 → empty range
		Prev_greatest: &prevGreatest,
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps: []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{
				{Results: []proofs.PrefixSearchResult{}, Elements: []proofs.NodeValue{dummyElement}},
			},
			Prefix_roots: []proofs.NodeValue{},
		},
		Prev_search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Values:   []proofs.UpdateValue{},
		Openings: [][]byte{},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	err := VerifyHistory(label, resp, config)
	if err != nil {
		t.Fatalf("VerifyHistory should succeed when prev_greatest == new_version: %v", err)
	}
}

// ==================================================================================
// ============================= Happy-Path Helpers =================================
// ==================================================================================

// makeBinaryLadderStep creates a BinaryLadderStep whose Proof is VRF_hash(nil, {label, version}).
// Since VRF_proof_to_hash is the identity, the resulting PrefixLeaf will have
// Vrf_output == VRF_hash(nil, {label, version}), enabling GetCommitment to find it.
func makeBinaryLadderStep(label []byte, version uint32) proofs.BinaryLadderStep {
	vrfInput := crypto.VrfInput{Label: label, Version: version}
	vrfProof := crypto.VRF_hash(nil, vrfInput)
	commitment := sha256.Sum256(append([]byte("commit-"), byte(version)))
	return proofs.BinaryLadderStep{Proof: vrfProof, Commitment: commitment}
}

// ==================================================================================
// ========================== VerifyUpdate Happy-Path Tests =========================
// ==================================================================================

func TestVerifyUpdate_HappyPath_SingleVersion(t *testing.T) {
	// Simplest happy path: tree_size=1, New_version=0, no previous greatest.
	// FullBinaryLadderSteps_wrapper(0) = [0, 1] → 2 binary ladder steps.
	// PrefixProof with 1 Inclusion at depth 0 → leaf for version 0.
	// CheckGreatest: step 0 (inclusion, ≤t) ok; step 1 (non-inclusion, >t) ok → res=0.
	// Expected: VerifyUpdate returns nil error.
	label := []byte("alice")
	version := uint32(0)
	st := newUserState()

	ladderSteps := proofs.FullBinaryLadderSteps_wrapper(uint64(version))
	binaryLadder := make([]proofs.BinaryLadderStep, len(ladderSteps))
	for i := range ladderSteps {
		binaryLadder[i] = makeBinaryLadderStep(label, uint32(ladderSteps[i]))
	}

	prefixProof := proofs.PrefixProof{
		Results: []proofs.PrefixSearchResult{
			{Result_type: proofs.Inclusion, Depth: 0},
		},
		Elements: []proofs.NodeValue{},
	}

	resp := UpdateResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Prev_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		New_version:   version,
		Prev_greatest: nil, // first version
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{100},
			Prefix_proofs: []proofs.PrefixProof{prefixProof},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Prev_search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Values:   []proofs.UpdateValue{{Value: []byte("alice-key-v0")}},
		Openings: [][]byte{[]byte("opening-0")}, // expectedCount = 0+1 = 1
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	err := VerifyUpdate(st, label, resp, config)
	if err != nil {
		t.Fatalf("VerifyUpdate returned unexpected error: %v", err)
	}
}

// ==================================================================================
// ========================== VerifyHistory Happy-Path Tests ========================
// ==================================================================================

func TestVerifyHistory_HappyPath_SingleVersion(t *testing.T) {
	// tree_size=1, New_version=0, Prev_greatest=nil → start=0, end=0.
	// Loop iterates once for v=0. VerifyUpdateKey succeeds (version 0 is greatest).
	// Expected: VerifyHistory returns nil error.
	label := []byte("alice")
	version := uint32(0)

	ladderSteps := proofs.FullBinaryLadderSteps_wrapper(uint64(version))
	binaryLadder := make([]proofs.BinaryLadderStep, len(ladderSteps))
	for i := range ladderSteps {
		binaryLadder[i] = makeBinaryLadderStep(label, uint32(ladderSteps[i]))
	}

	prefixProof := proofs.PrefixProof{
		Results: []proofs.PrefixSearchResult{
			{Result_type: proofs.Inclusion, Depth: 0},
		},
		Elements: []proofs.NodeValue{},
	}

	resp := UpdateResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Prev_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		New_version:   version,
		Prev_greatest: nil,
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{100},
			Prefix_proofs: []proofs.PrefixProof{prefixProof},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Prev_search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Values:   []proofs.UpdateValue{},
		Openings: [][]byte{},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring}

	err := VerifyHistory(label, resp, config)
	if err != nil {
		t.Fatalf("VerifyHistory returned unexpected error: %v", err)
	}
}
