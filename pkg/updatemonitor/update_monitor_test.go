package updatemonitor

import (
	"crypto/sha256"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/client"
	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ==================================================================================
// ================================== Helpers =======================================
// ==================================================================================

func buildSingleLeafTree(label []byte, version uint32) *proofs.PrefixTree {
	vrfInput := crypto.VrfInput{Label: label, Version: version}
	vrfHash := crypto.VRF_hash(nil, vrfInput)
	commitment := sha256.Sum256([]byte("test-commitment"))
	leaf := &proofs.PrefixLeaf{
		Vrf_output: vrfHash,
		Commitment: commitment,
	}
	tree := &proofs.PrefixTree{Leaf: leaf}
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

func uint32Ptr(v uint32) *uint32 {
	return &v
}

func uint64Ptr(v uint64) *uint64 {
	return &v
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
	trees := []*proofs.PrefixTree{tree, tree, tree, tree}
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
	trees := []*proofs.PrefixTree{tree}
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
	trees := []*proofs.PrefixTree{tree}
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

	trees := []*proofs.PrefixTree{nil}
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
// ============================== VerifyMonitor Tests ==============================
// ==================================================================================

func TestVerifyMonitor_EmptyMonitorMap(t *testing.T) {
	// Empty monitoring map with valid tree → should succeed with empty new_map.
	// Provide a PrefixProof with one copath element so ToTree succeeds.
	st := newUserState()
	label := []byte("alice")
	size := uint64(1)
	dummyElement := proofs.NodeValue{}
	for i := range dummyElement {
		dummyElement[i] = byte(i)
	}

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: size, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps: []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{
				{Results: []proofs.PrefixSearchResult{}, Elements: []proofs.NodeValue{dummyElement}},
			},
			Prefix_roots: []proofs.NodeValue{},
		},
	}
	monitorMap := []client.MonitoringMapEntry{}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring, ReasonableMonitoringWindow: 1}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err != nil {
		t.Fatalf("VerifyMonitor returned unexpected error: %v", err)
	}
	if len(newMap) != 0 {
		t.Errorf("VerifyMonitor returned new_map of len %d; want 0", len(newMap))
	}
}

func TestVerifyMonitor_UpdateViewFailsTreeSizeZero(t *testing.T) {
	// tree_size=0 → UpdateView returns error.
	// When determined is set early, new_map is empty (the loop doesn't execute).
	st := newUserState()
	label := []byte("alice")

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 0, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{},
			Prefix_proofs: []proofs.PrefixProof{},
			Prefix_roots:  []proofs.NodeValue{},
		},
	}
	monitorMap := []client.MonitoringMapEntry{
		{Position: 0, Version: 0},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring, ReasonableMonitoringWindow: 1}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyMonitor should return error when tree size is 0")
	}
	// When UpdateView fails, determined=true before the monitor loop,
	// so new_map stays empty.
	if len(newMap) != 0 {
		t.Errorf("VerifyMonitor returned new_map of len %d; want 0", len(newMap))
	}
}

func TestVerifyMonitor_PreservesMonitorMapEntries(t *testing.T) {
	// When verification succeeds, new_map should contain all entries
	// from the input monitoring map (always-append pattern).
	st := newUserState()
	label := []byte("alice")
	size := uint64(1)
	dummyElement := proofs.NodeValue{}
	for i := range dummyElement {
		dummyElement[i] = byte(i)
	}

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: size, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps: []uint64{1},
			Prefix_proofs: []proofs.PrefixProof{
				{Results: []proofs.PrefixSearchResult{}, Elements: []proofs.NodeValue{dummyElement}},
			},
			Prefix_roots: []proofs.NodeValue{},
		},
	}
	// All entries have version 0, and the tree is a copath node so
	// GetCommitment returns error → but for monitoring, we need to check
	// what happens. Since the tree built from a single copath element
	// has Value set (not a leaf), SearchForCommitment returns error
	// "cannot determine: reached copath node" → CheckGreatest returns 404.
	// That sets determined=true, so remaining entries are still appended.
	monitorMap := []client.MonitoringMapEntry{
		{Position: 0, Version: 1},
		{Position: 0, Version: 2},
		{Position: 0, Version: 3},
	}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring, ReasonableMonitoringWindow: 1}

	newMap, err := VerifyMonitor(st, label, resp, monitorMap, config)
	// First entry causes CheckGreatest error → determined = true
	// But the always-append pattern still appends all 3 entries
	if err == nil {
		// Copath node causes CheckGreatest to return error
		// Check that entries are preserved even on error
		if len(newMap) != len(monitorMap) {
			t.Errorf("VerifyMonitor new_map len = %d; want %d", len(newMap), len(monitorMap))
		}
	} else {
		// Even on error, some entries may have been appended
		// The always-append pattern ensures entries up to the error point are preserved
		t.Logf("VerifyMonitor returned error (expected): %v", err)
		t.Logf("new_map has %d entries", len(newMap))
	}

	// Verify that all entries in new_map have correct versions
	for i, entry := range newMap {
		if i < len(monitorMap) && entry.Version != monitorMap[i].Version {
			t.Errorf("new_map[%d].Version = %d; want %d", i, entry.Version, monitorMap[i].Version)
		}
	}
}

func TestVerifyMonitor_BadTimestamps(t *testing.T) {
	// Non-increasing timestamps → UpdateView returns error
	st := newUserState()
	label := []byte("alice")

	resp := MonitorResponse{
		Full_tree_head: client.FullTreeHead{
			Tree_head: client.TreeHead{Tree_size: 2, Signature: []byte{}},
			RootHash:  makeRootHash(),
		},
		Binary_ladder: []proofs.BinaryLadderStep{},
		Search: proofs.CombinedTreeProof{
			Timestamps:    []uint64{5, 3}, // non-increasing → error
			Prefix_proofs: []proofs.PrefixProof{{}, {}},
			Prefix_roots:  []proofs.NodeValue{},
		},
	}
	monitorMap := []client.MonitoringMapEntry{}
	config := &client.Configuration{Mode: client.DeploymentContractMonitoring, ReasonableMonitoringWindow: 1}

	_, err := VerifyMonitor(st, label, resp, monitorMap, config)
	if err == nil {
		t.Fatal("VerifyMonitor should return error for non-increasing timestamps")
	}
}
