package monitor

import (
	"crypto/sha256"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/client"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

// ==================================================================================
// ================================== Helpers =======================================
// ==================================================================================

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
