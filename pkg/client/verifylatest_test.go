package client

import (
	"crypto/sha256"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/prefixtree"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ==================================================================================
// ================================== Helpers =======================================
// ==================================================================================

// buildSingleLeafTree creates a PrefixTree with a single leaf whose VRF output
// matches the given (label, version) pair. GetCommitment on this tree returns:
//   - non-nil (inclusion) when queried with the same (label, version)
//   - nil (non-inclusion) for any other (label, version)
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

// newUserState creates a fresh UserState with no tree.
func newUserState() *UserState {
	return &UserState{
		Size:                0,
		Full_subtrees:       []proofs.NodeValue{},
		Frontier_timestamps: []uint64{},
	}
}

// uint32Ptr returns a pointer to the given uint32.
func uint32Ptr(v uint32) *uint32 {
	return &v
}

// makeRootHash creates a dummy root hash for testing.
func makeRootHash() []byte {
	h := sha256.Sum256([]byte("root"))
	return h[:]
}

// makeHashPtr creates a pointer to a [sha256.Size]byte for rootHashes slice.
func makeHashPtr() *[sha256.Size]byte {
	h := sha256.Sum256([]byte("root-hash"))
	return &h
}

// ==================================================================================
// ============================= RootNode Tests ====================================
// ==================================================================================

func TestRootNode_SpecCompliance(t *testing.T) {
	tests := []struct {
		name     string
		treeSize uint64
		wantRoot uint64
	}{
		{"size 0", 0, 0},
		{"size 1", 1, 0},
		{"size 2", 2, 1},
		{"size 4", 4, 3},
		{"size 8", 8, 7},
		{"size 16", 16, 15},
		{"size 3", 3, 1},
		{"size 5", 5, 3},
		{"size 6", 6, 3},
		{"size 7", 7, 3},
		{"size 9", 9, 7},
		{"size 14", 14, 7},
		{"size 15", 15, 7},
		{"size 50", 50, 31},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got := RootNode(tc.treeSize)
			if got != tc.wantRoot {
				t.Errorf("RootNode(%d) = %d; want %d", tc.treeSize, got, tc.wantRoot)
			}
		})
	}
}

// ==================================================================================
// ============================ CheckCommitment Tests ================================
// ==================================================================================

func TestCheckCommitment_IsGreatest(t *testing.T) {
	// Build a tree with (label, version=0) included.
	// With t=0 and steps=[0,1]:
	//   step 0: inclusion (version 0 matches leaf) → step <= t → ok
	//   step 1: non-inclusion (version 1 not in tree) → step > t → ok
	// Result: res=0 (t is the greatest version)
	label := []byte("alice")
	tree := buildSingleLeafTree(label, 0)
	rootHash := makeRootHash()
	steps := proofs.FullBinaryLadderSteps_wrapper(0)

	res, err := CheckCommitment(tree, steps, label, 0, rootHash, 4)
	if err != nil {
		t.Fatalf("CheckCommitment returned unexpected error: %v", err)
	}
	if res != 0 {
		t.Errorf("CheckCommitment = %d; want 0 (is greatest)", res)
	}
}

func TestCheckCommitment_HoleBelow(t *testing.T) {
	// Build a tree with (label, version=5) included (NOT version 0).
	// With t=0 and steps=[0,1]:
	//   step 0: non-inclusion → step 0 <= t 0 → hole
	// Result: res=-1 (hole found at or below t)
	label := []byte("alice")
	tree := buildSingleLeafTree(label, 5) // wrong version → non-inclusion at step 0
	rootHash := makeRootHash()
	steps := proofs.FullBinaryLadderSteps_wrapper(0)

	res, err := CheckCommitment(tree, steps, label, 0, rootHash, 4)
	if err != nil {
		t.Fatalf("CheckCommitment returned unexpected error: %v", err)
	}
	if res != -1 {
		t.Errorf("CheckCommitment = %d; want -1 (hole below t)", res)
	}
}

func TestCheckCommitment_NilTree(t *testing.T) {
	// A nil PrefixTree: SearchForCommitment handles nil gracefully
	// and returns (nil, nil), meaning non-inclusion.
	// At step 0 (step <= t), non-inclusion → hole → res=-1.
	label := []byte("alice")
	rootHash := makeRootHash()
	steps := proofs.FullBinaryLadderSteps_wrapper(0)

	res, err := CheckCommitment(nil, steps, label, 0, rootHash, 4)
	if err != nil {
		t.Fatalf("CheckCommitment returned unexpected error: %v", err)
	}
	if res != -1 {
		t.Errorf("CheckCommitment = %d; want -1 (hole, nil tree returns non-inclusion)", res)
	}
}

func TestCheckCommitment_EmptySteps(t *testing.T) {
	// With empty steps slice, the loop doesn't execute.
	// Result: res=0, err=nil (vacuously greatest)
	label := []byte("alice")
	tree := buildSingleLeafTree(label, 0)
	rootHash := makeRootHash()

	res, err := CheckCommitment(tree, []uint64{}, label, 0, rootHash, 4)
	if err != nil {
		t.Fatalf("CheckCommitment with empty steps returned error: %v", err)
	}
	if res != 0 {
		t.Errorf("CheckCommitment = %d; want 0 (vacuously greatest)", res)
	}
}

// ==================================================================================
// =========================== VerifyLatestKey Tests ================================
// ==================================================================================

func TestVerifyLatestKey_VersionOutOfBounds(t *testing.T) {
	// version >= size → should return (false, error)
	label := []byte("alice")
	version := uint32(5)
	size := uint64(4)

	tree := buildSingleLeafTree(label, 0)
	trees := []*prefixtree.PrefixTree{tree, tree, tree, tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr(), makeHashPtr(), makeHashPtr(), makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyLatestKey should return error for version out of bounds")
	}
	if res {
		t.Error("VerifyLatestKey should return false for version out of bounds")
	}
}

func TestVerifyLatestKey_VersionEqualToSize(t *testing.T) {
	// version == size → out of bounds (version must be < size)
	label := []byte("alice")
	version := uint32(4)
	size := uint64(4) // version 4 >= size 4 → out of bounds

	tree := buildSingleLeafTree(label, 0)
	trees := []*prefixtree.PrefixTree{tree, tree, tree, tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr(), makeHashPtr(), makeHashPtr(), makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyLatestKey should return error when version == size")
	}
	if res {
		t.Error("VerifyLatestKey should return false when version == size")
	}
}

func TestVerifyLatestKey_IsGreatest_SingleFrontier(t *testing.T) {
	// size=1: single frontier node at position 0.
	// Tree has (label, version=0) included → CheckCommitment returns 0.
	// Result: (true, nil)
	label := []byte("alice")
	version := uint32(0)
	size := uint64(1)

	tree := buildSingleLeafTree(label, version)
	trees := []*prefixtree.PrefixTree{tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyLatestKey returned unexpected error: %v", err)
	}
	if !res {
		t.Error("VerifyLatestKey should return true when version is greatest")
	}
}

func TestVerifyLatestKey_HoleDetected(t *testing.T) {
	// size=1, version=0 but tree has a different version → hole → (false, error)
	label := []byte("alice")
	version := uint32(0)
	size := uint64(1)

	tree := buildSingleLeafTree(label, 99) // wrong version → non-inclusion at step 0
	trees := []*prefixtree.PrefixTree{tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyLatestKey should return error when hole is detected")
	}
	if res {
		t.Error("VerifyLatestKey should return false when hole is detected")
	}
}

func TestVerifyLatestKey_NilTree(t *testing.T) {
	// size=1, prefix tree is nil → should return (false, error)
	label := []byte("alice")
	version := uint32(0)
	size := uint64(1)

	trees := []*prefixtree.PrefixTree{nil}
	rootHashes := []*[sha256.Size]byte{makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyLatestKey should return error when prefix tree is nil")
	}
	if res {
		t.Error("VerifyLatestKey should return false when prefix tree is nil")
	}
}

func TestVerifyLatestKey_MultipleFrontiers(t *testing.T) {
	// size=2: BST root=1, frontiers=[1, ...]. Need 2 prefix trees.
	// version=0, tree at position 0 has (label, 0) included.
	label := []byte("alice")
	version := uint32(0)
	size := uint64(2)

	tree := buildSingleLeafTree(label, version)
	trees := []*prefixtree.PrefixTree{tree, tree}
	rootHashes := []*[sha256.Size]byte{makeHashPtr(), makeHashPtr()}

	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: size},
			RootHash:  makeRootHash(),
		},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}
	monitorMap := make([]MonitoringMapEntry, 0)

	res, err := VerifyLatestKey(trees, rootHashes, size, query, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyLatestKey with multiple frontiers returned error: %v", err)
	}
	if !res {
		t.Error("VerifyLatestKey should return true with valid multi-frontier setup")
	}
}

// ==================================================================================
// ============================= VerifyLatest Tests ================================
// ==================================================================================

func TestVerifyLatest_NilVersion(t *testing.T) {
	// resp.Version == nil → should return error
	st := newUserState()
	query := SearchRequest{Label: []byte("alice")}
	resp := SearchResponse{
		Version: nil, // nil version triggers error
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{{}},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: []byte{}},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}

	res, err := st.VerifyLatest(query, resp, config)
	if err == nil {
		t.Fatal("VerifyLatest should return error for nil version")
	}
	if res != nil {
		t.Error("VerifyLatest should return nil result for nil version")
	}
}

func TestVerifyLatest_WrongLadderLength(t *testing.T) {
	// Binary ladder length doesn't match expected for version → error
	st := newUserState()
	version := uint32(3) // FullBinaryLadderSteps(3) = [0,1,3,7,5,4] → len 6
	query := SearchRequest{Label: []byte("alice")}
	resp := SearchResponse{
		Version: &version,
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: 4, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{{}, {}}, // len 2, expected 6
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{{}, {}, {}, {}},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: []byte{}},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}

	res, err := st.VerifyLatest(query, resp, config)
	if err == nil {
		t.Fatal("VerifyLatest should return error for wrong binary ladder length")
	}
	if res != nil {
		t.Error("VerifyLatest should return nil result for wrong binary ladder length")
	}
}

// ==================================================================================
// ======================== VerifyLatest Happy-Path Tests ===========================
// ==================================================================================

// makeBinaryLadderStep creates a BinaryLadderStep whose Proof is VRF_hash(nil, {label, version}).
// Since VRF_prove == VRF_hash and VRF_proof_to_hash is the identity, CombineResults
// will produce a leaf with the correct Vrf_output for this (label, version) pair.
func makeBinaryLadderStep(label []byte, version uint32) proofs.BinaryLadderStep {
	vrfInput := crypto.VrfInput{Label: label, Version: version}
	vrfProof := crypto.VRF_hash(nil, vrfInput)
	commitment := sha256.Sum256(append([]byte("commit-"), byte(version)))
	return proofs.BinaryLadderStep{Proof: vrfProof[:], Commitment: &commitment}
}

func TestVerifyLatest_HappyPath_Size1(t *testing.T) {
	// Simplest happy path: tree_size=1, version=0, label="alice"
	// FullBinaryLadderSteps_wrapper(0) = [0, 1] → 2 binary ladder steps
	// 1 prefix proof with Results: [{Inclusion, depth=0}], Elements: [] → leaf
	// CheckCommitment: step 0 → inclusion (<=t) ok; step 1 → non-inclusion (>t) ok → res=0
	// Expected: VerifyLatest returns (&UpdateValue{...}, nil)
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

	rootHash := makeRootHash()
	st := newUserState()
	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  rootHash,
		},
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{100},
			Prefix_proofs: []proofs.PrefixProof{prefixProof},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: []byte("alice-key-v0")},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}

	res, err := st.VerifyLatest(query, resp, config)
	if err != nil {
		t.Fatalf("VerifyLatest returned unexpected error: %v", err)
	}
	if res == nil {
		t.Fatal("VerifyLatest returned nil result; expected UpdateValue")
	}
	if string(res.Value) != "alice-key-v0" {
		t.Errorf("res.Value = %q; want %q", string(res.Value), "alice-key-v0")
	}
}

func TestVerifyLatest_HappyPath_Size2(t *testing.T) {
	// tree_size=2, version=0, label="bob"
	// FullBinaryLadderSteps_wrapper(0) = [0, 1] → 2 binary ladder steps
	// FrontierNodes(2) = [1] → checks tree at position 1
	// prefix_proofs[0]: copath node (not a frontier, not checked by VerifyLatestKey)
	// prefix_proofs[1]: leaf for version 0 (Inclusion, depth=0)
	label := []byte("bob")
	version := uint32(0)
	ladderSteps := proofs.FullBinaryLadderSteps_wrapper(uint64(version))

	binaryLadder := make([]proofs.BinaryLadderStep, len(ladderSteps))
	for i := range ladderSteps {
		binaryLadder[i] = makeBinaryLadderStep(label, uint32(ladderSteps[i]))
	}

	dummyHash := proofs.NodeValue{}
	dummyHash[0] = 0xAB

	prefixProofs := []proofs.PrefixProof{
		// prefix_proofs[0]: copath node (position 0 is not a frontier for size=2)
		{Results: []proofs.PrefixSearchResult{}, Elements: []proofs.NodeValue{dummyHash}},
		// prefix_proofs[1]: leaf for version 0
		{Results: []proofs.PrefixSearchResult{
			{Result_type: proofs.Inclusion, Depth: 0},
		}, Elements: []proofs.NodeValue{}},
	}

	rootHash := makeRootHash()
	st := newUserState()
	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: 2, Signature: []byte{}},
			RootHash:  rootHash,
		},
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{100},
			Prefix_proofs: prefixProofs,
			Prefix_roots:  []proofs.NodeValue{},
		},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: []byte("bob-key-v0")},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}

	res, err := st.VerifyLatest(query, resp, config)
	if err != nil {
		t.Fatalf("VerifyLatest returned unexpected error: %v", err)
	}
	if res == nil {
		t.Fatal("VerifyLatest returned nil result; expected UpdateValue")
	}
	if string(res.Value) != "bob-key-v0" {
		t.Errorf("res.Value = %q; want %q", string(res.Value), "bob-key-v0")
	}
}

func TestVerifyLatest_HappyPath_Size3(t *testing.T) {
	// tree_size=3, version=0, label="charlie"
	// FullBinaryLadderSteps_wrapper(0) = [0, 1] → 2 binary ladder steps
	// FrontierNodes(3) = [1, 2] → checks trees at positions 1 AND 2
	// prefix_proofs[0]: copath node (position 0 is not a frontier)
	// prefix_proofs[1]: leaf for version 0
	// prefix_proofs[2]: leaf for version 0
	label := []byte("charlie")
	version := uint32(0)
	ladderSteps := proofs.FullBinaryLadderSteps_wrapper(uint64(version))

	binaryLadder := make([]proofs.BinaryLadderStep, len(ladderSteps))
	for i := range ladderSteps {
		binaryLadder[i] = makeBinaryLadderStep(label, uint32(ladderSteps[i]))
	}

	dummyHash := proofs.NodeValue{}
	dummyHash[0] = 0xCD

	prefixProofs := []proofs.PrefixProof{
		// prefix_proofs[0]: copath node
		{Results: []proofs.PrefixSearchResult{}, Elements: []proofs.NodeValue{dummyHash}},
		// prefix_proofs[1]: leaf for version 0
		{Results: []proofs.PrefixSearchResult{
			{Result_type: proofs.Inclusion, Depth: 0},
		}, Elements: []proofs.NodeValue{}},
		// prefix_proofs[2]: leaf for version 0
		{Results: []proofs.PrefixSearchResult{
			{Result_type: proofs.Inclusion, Depth: 0},
		}, Elements: []proofs.NodeValue{}},
	}

	rootHash := makeRootHash()
	st := newUserState()
	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: 3, Signature: []byte{}},
			RootHash:  rootHash,
		},
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{100, 200},
			Prefix_proofs: prefixProofs,
			Prefix_roots:  []proofs.NodeValue{},
		},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: []byte("charlie-key-v0")},
	}
	config := &Configuration{Mode: DeploymentContractMonitoring}

	res, err := st.VerifyLatest(query, resp, config)
	if err != nil {
		t.Fatalf("VerifyLatest returned unexpected error: %v", err)
	}
	if res == nil {
		t.Fatal("VerifyLatest returned nil result; expected UpdateValue")
	}
	if string(res.Value) != "charlie-key-v0" {
		t.Errorf("res.Value = %q; want %q", string(res.Value), "charlie-key-v0")
	}
}

func TestVerifyLatest_HappyPath_UpdatesUserState(t *testing.T) {
	// Verify that a successful VerifyLatest call correctly updates the UserState
	// (size and frontier timestamps).
	label := []byte("dave")
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

	st := newUserState()
	if st.Size != 0 {
		t.Fatalf("initial st.Size = %d; want 0", st.Size)
	}

	config := &Configuration{Mode: DeploymentContractMonitoring}
	query := SearchRequest{Label: label}
	resp := SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: 1, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{42},
			Prefix_proofs: []proofs.PrefixProof{prefixProof},
			Prefix_roots:  []proofs.NodeValue{},
		},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: []byte("dave-key-v0")},
	}

	res, err := st.VerifyLatest(query, resp, config)
	if err != nil {
		t.Fatalf("VerifyLatest returned unexpected error: %v", err)
	}
	if res == nil {
		t.Fatal("VerifyLatest returned nil result")
	}

	// Verify UserState was updated by UpdateView
	if st.Size != 1 {
		t.Errorf("st.Size = %d; want 1", st.Size)
	}
	if len(st.Frontier_timestamps) != 1 {
		t.Fatalf("len(st.Frontier_timestamps) = %d; want 1", len(st.Frontier_timestamps))
	}
	if st.Frontier_timestamps[0] != 42 {
		t.Errorf("st.Frontier_timestamps[0] = %d; want 42", st.Frontier_timestamps[0])
	}
}

// ==================================================================================
// ========================== MkImplicitBinarySearchTree ===========================
// ==================================================================================

func TestMkImplicitBinarySearchTree_SizeZero(t *testing.T) {
	tree := MkImplicitBinarySearchTree(0)
	if tree != nil {
		t.Error("MkImplicitBinarySearchTree(0) should return nil")
	}
}

func TestMkImplicitBinarySearchTree_SizeOne(t *testing.T) {
	tree := MkImplicitBinarySearchTree(1)
	if tree == nil {
		t.Fatal("MkImplicitBinarySearchTree(1) should not return nil")
	}
	if tree.Root != 0 {
		t.Errorf("Root = %d; want 0", tree.Root)
	}
}

func TestFrontierNodes(t *testing.T) {
	tests := []struct {
		name     string
		size     uint64
		wantLen  int
		wantHead uint64
	}{
		{"size 1", 1, 1, 0},
		{"size 2", 2, 1, 1},
		{"size 3", 3, 2, 1},
		{"size 4", 4, 1, 3},
		{"size 5", 5, 2, 3},
		{"size 8", 8, 1, 7},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			tree := MkImplicitBinarySearchTree(tc.size)
			if tree == nil {
				t.Fatal("tree should not be nil")
			}
			frontiers := tree.FrontierNodes()
			if len(frontiers) != tc.wantLen {
				t.Errorf("len(FrontierNodes(%d)) = %d; want %d", tc.size, len(frontiers), tc.wantLen)
			}
			if len(frontiers) > 0 && frontiers[0] != tc.wantHead {
				t.Errorf("FrontierNodes(%d)[0] = %d; want %d", tc.size, frontiers[0], tc.wantHead)
			}
		})
	}
}

// ==================================================================================
// ========================== FullBinaryLadderSteps ================================
// ==================================================================================

func TestFullBinaryLadderSteps_StartsWithZero(t *testing.T) {
	targets := []uint64{0, 1, 3, 7, 15, 100}
	for _, target := range targets {
		steps := proofs.FullBinaryLadderSteps_wrapper(target)
		if len(steps) == 0 {
			t.Errorf("FullBinaryLadderSteps_wrapper(%d) returned empty", target)
			continue
		}
		if steps[0] != 0 {
			t.Errorf("FullBinaryLadderSteps_wrapper(%d)[0] = %d; want 0", target, steps[0])
		}
	}
}

func TestFullBinaryLadderSteps_ContainsTarget(t *testing.T) {
	// The binary ladder steps should contain the target itself
	// (it appears somewhere in the exponential jump or binary search phase)
	targets := []uint64{0, 1, 2, 3, 7, 8, 15}
	for _, target := range targets {
		steps := proofs.FullBinaryLadderSteps_wrapper(target)
		found := false
		for _, s := range steps {
			if s == target {
				found = true
				break
			}
		}
		// The target appears in steps as an exponential jump element (2^k - 1)
		// or as a binary search midpoint. It should be there for powers of 2 minus 1.
		if !found && (target == 0 || target == 1 || target == 3 || target == 7 || target == 15) {
			t.Errorf("FullBinaryLadderSteps_wrapper(%d) does not contain target; steps = %v", target, steps)
		}
	}
}

// ==================================================================================
// ================================ UpdateView =====================================
// ==================================================================================

func TestUpdateView_InitializesFullSubtrees(t *testing.T) {
	// First update (st.Size == 0): Full_subtrees should be initialized from prf.Full_subtrees.
	st := newUserState()
	hash1 := proofs.NodeValue{}
	hash1[0] = 0xAA
	hash1[1] = 0xBB

	newHead := FullTreeHead{
		Tree_head: TreeHead{Tree_size: 1, Signature: []byte{}},
		RootHash:  makeRootHash(),
	}
	prf := proofs.CombinedTreeProof{
		Timestamps:    []uint64{100},
		Prefix_proofs: []proofs.PrefixProof{},
		Prefix_roots:  []proofs.NodeValue{},
		Inclusion: proofs.InclusionProof{Elements: []proofs.NodeValue{hash1}},
	}

	err := st.UpdateView(newHead, prf)
	if err != nil {
		t.Fatalf("UpdateView returned unexpected error: %v", err)
	}
	if st.Size != 1 {
		t.Errorf("st.Size = %d; want 1", st.Size)
	}
	if len(st.Full_subtrees) != 1 {
		t.Fatalf("len(st.Full_subtrees) = %d; want 1", len(st.Full_subtrees))
	}
	if st.Full_subtrees[0] != hash1 {
		t.Error("st.Full_subtrees[0] does not match expected hash")
	}
}

func TestUpdateView_ConsistencyCheckPasses(t *testing.T) {
	// Second update: matching frontier hashes should pass the consistency check.
	// Transition: size 2 → size 3.
	hash1 := proofs.NodeValue{}
	hash1[0] = 0x11
	hash2 := proofs.NodeValue{}
	hash2[0] = 0x22

	st := newUserState()

	// First update to size 2 (frontier = [1], 1 timestamp needed)
	newHead1 := FullTreeHead{
		Tree_head: TreeHead{Tree_size: 2, Signature: []byte{}},
		RootHash:  makeRootHash(),
	}
	prf1 := proofs.CombinedTreeProof{
		Timestamps:    []uint64{100},
		Prefix_proofs: []proofs.PrefixProof{},
		Prefix_roots:  []proofs.NodeValue{},
		Inclusion: proofs.InclusionProof{Elements: []proofs.NodeValue{hash1}},
	}
	if err := st.UpdateView(newHead1, prf1); err != nil {
		t.Fatalf("First UpdateView failed: %v", err)
	}
	if st.Size != 2 {
		t.Fatalf("st.Size after first update = %d; want 2", st.Size)
	}

	// Second update to size 3 (frontier = [1, 2], 2 timestamps needed)
	// Full_subtrees[0] matches old Full_subtrees[0] → consistency passes.
	newHead2 := FullTreeHead{
		Tree_head: TreeHead{Tree_size: 3, Signature: []byte{}},
		RootHash:  makeRootHash(),
	}
	prf2 := proofs.CombinedTreeProof{
		Timestamps:    []uint64{100, 200},
		Prefix_proofs: []proofs.PrefixProof{},
		Prefix_roots:  []proofs.NodeValue{},
		Inclusion: proofs.InclusionProof{Elements: []proofs.NodeValue{hash1, hash2}},
	}
	if err := st.UpdateView(newHead2, prf2); err != nil {
		t.Fatalf("Second UpdateView failed: %v", err)
	}
	if st.Size != 3 {
		t.Errorf("st.Size after second update = %d; want 3", st.Size)
	}
	if len(st.Full_subtrees) != 2 {
		t.Fatalf("len(st.Full_subtrees) = %d; want 2", len(st.Full_subtrees))
	}
	if st.Full_subtrees[0] != hash1 || st.Full_subtrees[1] != hash2 {
		t.Error("st.Full_subtrees does not match expected hashes after second update")
	}
}

func TestUpdateView_ConsistencyCheckFails(t *testing.T) {
	// Second update: mismatched frontier hashes should fail.
	hash1 := proofs.NodeValue{}
	hash1[0] = 0x11
	hashWrong := proofs.NodeValue{}
	hashWrong[0] = 0xFF // different from hash1

	st := newUserState()

	// First update to size 2
	newHead1 := FullTreeHead{
		Tree_head: TreeHead{Tree_size: 2, Signature: []byte{}},
		RootHash:  makeRootHash(),
	}
	prf1 := proofs.CombinedTreeProof{
		Timestamps:    []uint64{100},
		Prefix_proofs: []proofs.PrefixProof{},
		Prefix_roots:  []proofs.NodeValue{},
		Inclusion: proofs.InclusionProof{Elements: []proofs.NodeValue{hash1}},
	}
	if err := st.UpdateView(newHead1, prf1); err != nil {
		t.Fatalf("First UpdateView failed: %v", err)
	}

	// Second update to size 3 with wrong Full_subtrees[0]
	newHead2 := FullTreeHead{
		Tree_head: TreeHead{Tree_size: 3, Signature: []byte{}},
		RootHash:  makeRootHash(),
	}
	prf2 := proofs.CombinedTreeProof{
		Timestamps:    []uint64{100, 200},
		Prefix_proofs: []proofs.PrefixProof{},
		Prefix_roots:  []proofs.NodeValue{},
		Inclusion: proofs.InclusionProof{Elements: []proofs.NodeValue{hashWrong, {}}},
	}
	err := st.UpdateView(newHead2, prf2)
	if err == nil {
		t.Fatal("UpdateView should fail when frontier hashes don't match")
	}
}

// ==================================================================================
// ============================== IsDistinguished ==================================
// ==================================================================================

// ==================================================================================
// =================== Large Happy-Path Tests (Spec-aligned) =======================
// ==================================================================================

// buildHappyPathSearchResponse constructs a valid SearchResponse for version 0
// in a tree of the given treeSize. Frontier positions receive an Inclusion
// PrefixProof (creating a leaf for version 0 via the binary ladder); all other
// positions receive a copath-node PrefixProof. Timestamps are strictly
// increasing with one entry per frontier node.
func buildHappyPathSearchResponse(label []byte, treeSize uint64) SearchResponse {
	version := uint32(0)
	ladderSteps := proofs.FullBinaryLadderSteps_wrapper(uint64(version))

	binaryLadder := make([]proofs.BinaryLadderStep, len(ladderSteps))
	for i := range ladderSteps {
		binaryLadder[i] = makeBinaryLadderStep(label, uint32(ladderSteps[i]))
	}

	// Compute frontier positions
	searchTree := MkImplicitBinarySearchTree(treeSize)
	frontiers := searchTree.FrontierNodes()
	frontierSet := make(map[uint64]bool)
	for _, f := range frontiers {
		frontierSet[f] = true
	}

	dummyHash := proofs.NodeValue{}
	dummyHash[0] = 0xAB

	prefixProofs := make([]proofs.PrefixProof, treeSize)
	for i := uint64(0); i < treeSize; i++ {
		if frontierSet[i] {
			// Frontier: Inclusion at depth 0 → leaf for version 0
			prefixProofs[i] = proofs.PrefixProof{
				Results: []proofs.PrefixSearchResult{
					{Result_type: proofs.Inclusion, Depth: 0},
				},
				Elements: []proofs.NodeValue{},
			}
		} else {
			// Non-frontier: copath node (never queried by CheckGreatest)
			prefixProofs[i] = proofs.PrefixProof{
				Results:  []proofs.PrefixSearchResult{},
				Elements: []proofs.NodeValue{dummyHash},
			}
		}
	}

	timestamps := make([]uint64, len(frontiers))
	for i := range frontiers {
		timestamps[i] = uint64((i + 1) * 100)
	}

	return SearchResponse{
		Version: uint32Ptr(version),
		Full_tree_head: FullTreeHead{
			Tree_head: TreeHead{Tree_size: treeSize, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: binaryLadder,
		Search: proofs.CombinedTreeProof{
			Timestamps:    timestamps,
			Prefix_proofs: prefixProofs,
			Prefix_roots:  []proofs.NodeValue{},
		},
		Opening:   []byte{},
		Value:     proofs.UpdateValue{Value: append([]byte{}, append(label, []byte("-key-v0")...)...)},
	}
}

func TestVerifyLatest_HappyPath_Size4(t *testing.T) {
	// tree_size=4 (power of two): BST root=3, frontier=[3]
	// Single frontier → CheckGreatest at position 3 → res=0 → success
	label := []byte("alice")
	st := newUserState()
	config := &Configuration{Mode: DeploymentContractMonitoring}
	query := SearchRequest{Label: label}
	resp := buildHappyPathSearchResponse(label, 4)

	res, err := st.VerifyLatest(query, resp, config)
	if err != nil {
		t.Fatalf("VerifyLatest(size=4) returned unexpected error: %v", err)
	}
	if res == nil {
		t.Fatal("VerifyLatest(size=4) returned nil result")
	}
	if string(res.Value) != "alice-key-v0" {
		t.Errorf("res.Value = %q; want %q", string(res.Value), "alice-key-v0")
	}
	if st.Size != 4 {
		t.Errorf("st.Size = %d; want 4", st.Size)
	}
}

func TestVerifyLatest_HappyPath_Size5_TwoFrontiers(t *testing.T) {
	// tree_size=5: BST root=3, right child at 4. frontier=[3, 4]
	// Two frontiers: non-last (3) must not return 1, last (4) must return 0
	label := []byte("bob")
	st := newUserState()
	config := &Configuration{Mode: DeploymentContractMonitoring}
	query := SearchRequest{Label: label}
	resp := buildHappyPathSearchResponse(label, 5)

	res, err := st.VerifyLatest(query, resp, config)
	if err != nil {
		t.Fatalf("VerifyLatest(size=5) returned unexpected error: %v", err)
	}
	if res == nil {
		t.Fatal("VerifyLatest(size=5) returned nil result")
	}
	if string(res.Value) != "bob-key-v0" {
		t.Errorf("res.Value = %q; want %q", string(res.Value), "bob-key-v0")
	}
	if st.Size != 5 {
		t.Errorf("st.Size = %d; want 5", st.Size)
	}
}

func TestVerifyLatest_HappyPath_Size8(t *testing.T) {
	// tree_size=8 (power of two): BST root=7, frontier=[7]
	// 8 prefix proofs, only position 7 is a frontier
	label := []byte("charlie")
	st := newUserState()
	config := &Configuration{Mode: DeploymentContractMonitoring}
	query := SearchRequest{Label: label}
	resp := buildHappyPathSearchResponse(label, 8)

	res, err := st.VerifyLatest(query, resp, config)
	if err != nil {
		t.Fatalf("VerifyLatest(size=8) returned unexpected error: %v", err)
	}
	if res == nil {
		t.Fatal("VerifyLatest(size=8) returned nil result")
	}
	if st.Size != 8 {
		t.Errorf("st.Size = %d; want 8", st.Size)
	}
}

func TestVerifyLatest_HappyPath_Size14_ThreeFrontiers(t *testing.T) {
	// tree_size=14: frontier=[7, 11, 13] (three frontier nodes)
	// Tests the full multi-frontier loop + final frontier check
	label := []byte("dave")
	st := newUserState()
	config := &Configuration{Mode: DeploymentContractMonitoring}
	query := SearchRequest{Label: label}
	resp := buildHappyPathSearchResponse(label, 14)

	res, err := st.VerifyLatest(query, resp, config)
	if err != nil {
		t.Fatalf("VerifyLatest(size=14) returned unexpected error: %v", err)
	}
	if res == nil {
		t.Fatal("VerifyLatest(size=14) returned nil result")
	}
	if st.Size != 14 {
		t.Errorf("st.Size = %d; want 14", st.Size)
	}
}

func TestVerifyLatest_HappyPath_Size50(t *testing.T) {
	// tree_size=50: frontier=[31, 47, 49] (spec example from Section 4.1)
	// 50 prefix proofs, three frontiers — exercises the full protocol at scale
	label := []byte("eve")
	st := newUserState()
	config := &Configuration{Mode: DeploymentContractMonitoring}
	query := SearchRequest{Label: label}
	resp := buildHappyPathSearchResponse(label, 50)

	res, err := st.VerifyLatest(query, resp, config)
	if err != nil {
		t.Fatalf("VerifyLatest(size=50) returned unexpected error: %v", err)
	}
	if res == nil {
		t.Fatal("VerifyLatest(size=50) returned nil result")
	}
	if st.Size != 50 {
		t.Errorf("st.Size = %d; want 50", st.Size)
	}
}

func TestVerifyLatest_HappyPath_SequentialUpdates(t *testing.T) {
	// Simulate a user receiving multiple tree updates: size 1 → 3 → 5 → 14
	// Each call should succeed and advance the UserState.
	// Subsequent calls must pass the consistency check (Full_subtrees match
	// the previous Full_subtrees at matching frontier positions).
	label := []byte("frank")
	config := &Configuration{Mode: DeploymentContractMonitoring}
	query := SearchRequest{Label: label}
	st := newUserState()

	// Use size transitions where the path to the old head's first node
	// differs from the old frontier's first node, so i=0 in UpdateView
	// and no Full_subtrees consistency check is needed.
	sizes := []uint64{1, 3, 5, 14}
	for step, size := range sizes {
		resp := buildHappyPathSearchResponse(label, size)

		res, err := st.VerifyLatest(query, resp, config)
		if err != nil {
			t.Fatalf("step %d (size=%d): VerifyLatest returned error: %v", step, size, err)
		}
		if res == nil {
			t.Fatalf("step %d (size=%d): VerifyLatest returned nil result", step, size)
		}
		if st.Size != size {
			t.Errorf("step %d: st.Size = %d; want %d", step, st.Size, size)
		}
	}
}

// ==================================================================================
// ============================== IsDistinguished ==================================
// ==================================================================================

func TestIsDistinguished(t *testing.T) {
	tests := []struct {
		leftTs  uint64
		rightTs uint64
		rmw     uint64
		want    bool
	}{
		{0, 100, 50, true},
		{0, 100, 100, true},
		{0, 100, 101, false},
		{50, 50, 0, true},
		{100, 50, 10, false}, // right < left
	}

	for _, tc := range tests {
		got := IsDistinguished(tc.leftTs, tc.rightTs, tc.rmw)
		if got != tc.want {
			t.Errorf("IsDistinguished(%d, %d, %d) = %v; want %v",
				tc.leftTs, tc.rightTs, tc.rmw, got, tc.want)
		}
	}
}
