package trees

import (
	"crypto/sha256"
	"encoding/hex"
	"testing"

	"github.com/felixlinker/keytrans-verification/pkg/proofs"
)

type prefixDictVector struct {
	name              string
	label             string
	version           uint64
	publicKey         string
	ladderVersions    []uint64
	ladderProofs      []string
	ladderCommitments []string
	prefixResults     []prefixDictResultVector
	prefixElements    []string
	expectedRoot      string
}

type prefixDictResultVector struct {
	resultType     int
	depth          uint8
	leafVrfOutput  string
	leafCommitment string
}

var prefixDictVectors = []prefixDictVector{
	{
		name:      "user000@example.com-v0",
		label:     "user000@example.com",
		version:   0,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		ladderVersions: []uint64{
			0, 1,
		},
		ladderProofs: []string{
			"dde7bc4500529c2c837cb6d316c9af45c59c5a750ad24c39b0bff33bd88055f435115b1c364feb452c6ca9692500c339d44c95fa3c543cae87de3ecb97b314315c831c0eb54b86eeafd3a0c83c9a250c",
			"3081be8b1a45fecb0c280d12f08a4db47aeba960123475f559ec55a31e252cfab8db2425979966d0a58075c541d469a312069a9a3847a2f4d30014e35ac664ac7e3e469e5e67e36ae7a4e4fe0fab2009",
		},
		ladderCommitments: []string{
			"2626ec08fb1709477093732fc9d18df486f419838e10ebe8618f9275f7babda5",
			"0000000000000000000000000000000000000000000000000000000000000000",
		},
		prefixResults: []prefixDictResultVector{
			{resultType: proofs.Inclusion, depth: 12},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          8,
				leafVrfOutput:  "b9e10134e1c253851d8f01a61b0b9f10d38a204dc14c7b2b582529a1f95952cf",
				leafCommitment: "1d3cad4abf6fbbcd85e5904b6c00c7e579b6c96fd79be88063e05b9eb34d08b0",
			},
		},
		prefixElements: []string{
			"8b8d10566c4dc48d2729bb7e4efc5bc76754372b2ac9223672d6a32e573294c7",
			"b351fd62ed41f15be448c348f47c374d6d316be67edbf5d1aa02784f598723e6",
			"a1bd20ed32ab74c43a3ce21f16399b41e79275b6fb4ff5b24ca08403f905db5f",
			"103e6a4431e3e25624adc5e8aeb54d1a820ee4ce4ea07d43dc3dec4b2c9df77d",
			"91cc3328d6a115264367793bf741fe0c20191673d06df31eef62fb586aa9cab3",
			"cb4ba06b775cc7a9322d3de393bf39202f175632503a3e6e9f133edca0f60e29",
			"fe923da55000639e19f39280ef8e6647f91e47169152d3de6dc102239a7959c1",
			"7b6a739ba2ee3cc4dddb149742c3d9f3ff21389c06ee2f0536d6bc4b40541b4b",
			"2e976cd615c2e426d3d66b3ff6607e66889f4b0ffaffccbe99878c85a598a020",
			"c78d56242e23ddda0c0ef77dc0461fad7c5ccd94d505d2736a8a14c687b4082a",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"6d4accc3fbf722f166a2545cb1697409fee0af854811f2b01437a434a158ab32",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"1e44724e8be2bdab1219627fc80faac2485a49eb68cde218c5c02ca5d5c15621",
			"7ab4086b4d690bce096e0613d4fa1fbd289007829aa66e4747faecc23df5f60d",
		},
		expectedRoot: "a6761c0c6d2d40b96006282bad7c796eb597abff8c50b2be2ae101892708a15c",
	},
	{
		name:      "user002@example.com-v3",
		label:     "user002@example.com",
		version:   3,
		publicKey: "23bc54912c1e6e92c4a86825c867e27ffdc555bffbd4244f17a26abfffee965d",
		ladderVersions: []uint64{
			0, 1, 3, 7, 5, 4,
		},
		ladderProofs: []string{
			"f28a098fd2f88dcd67d34434aa4c54539d94efa71bb4e62952e5de12892c5a63cf1ef52e0ee22e5343450371884c9afe29c20c538fbdd76f6f5cb94892a8f54e1f7eb406237102c87d27aaefe7ad8f02",
			"17a25f78520dc766b8f7a3e7082513125a5151dd68284516518a45013d7556fe7905fe4d8a6691229cd97eb2b6ddb2220f2913c0f7612181f19ce72429d51ca65ece25dac9974509abc96f9b7c88430e",
			"3d838db0b118c0b12c64653728043ed57ae914e4476ce7772408a6ef4bbe2a42aa5f913cdde0864475340b2ae7c0f29ebda3320ffdceae08339cb497b86e983ee6e9cbd40e1eb9df447e314b37035500",
			"4cfb90b56d533cd5ce44e1e75f6f8aab762ee7e7854e6c31dbf3a05c192a8bf724e0a0416b8cc692d8afb752c3e8179bd1d54655ec49952a427244960ee49e294bab645b987e292659bfbdf3c27e7605",
			"05db54f9c4a74bf2447ab48104972352ab8840c977f32ae092cd41c7fec35071802802b0970a4cd17fbd2e02d15b387f927f41fe9dccc73491abd2c9fe5c68f8f5af86680b25883cdeb3d1ff17b6bc05",
			"3aa1b5d8aead56856ac6746f94f4c042b1c1e4f5238dc0e38f53c688214469db477ffcf56381b981b60f0bb898c08c3ce7432406b2c726ee0014d2f5c077414a33a1906c02a1a03f2f2451432ab7a60a",
		},
		ladderCommitments: []string{
			"0dd2e916909a8fd05bccb6c77e0eb9c3a6f8568596bd60ec16c7aea7b7857d55",
			"6f9304aaf95361d455a357fba378e26a7630620590321ba4c4f62dd6430fb6e2",
			"62388d47f2aa98481c187b85958d4c0c3aad4023619d5ca344d7219d37bd95e1",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
		},
		prefixResults: []prefixDictResultVector{
			{resultType: proofs.Inclusion, depth: 10},
			{resultType: proofs.Inclusion, depth: 10},
			{resultType: proofs.Inclusion, depth: 8},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          8,
				leafVrfOutput:  "0d27ee61e1071c19a29d4878768468a543972fe23bc403e1185e4951405ea449",
				leafCommitment: "5c48d2bbc2d5f5f4b177642c0f33158cfcbad17dd4fbcf19dcf474276c6f7c96",
			},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          10,
				leafVrfOutput:  "4750d039b49adc9b9845d7753737377b1c8f46191b13d45ade7e04da575e4962",
				leafCommitment: "31617fe06c9b3cd08d8df863cf8d7f10676f746b134ef656badde3343b6ee7b3",
			},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          8,
				leafVrfOutput:  "33dad0f922a7a64389019e5a78ac010bd37d35caa980488f2168ba49ed8c0783",
				leafCommitment: "7ed59722dc0112eee27856ff4de8e0c9f73f6120955fbbb22aead928bf76759e",
			},
		},
		prefixElements: []string{
			"bed9a0b890aacbbb04006bb30616ab3fd19211c1a3e262b5ade5f0938d8c053f",
			"aef7a09772b05ff106efb8666d940f63dcfd5406f3b4f80ffa2d7471b52f56b4",
			"c7b4d8e335e14dacef9e46fc1fd836a27256bc124379f3ade14bb0d5d8564df8",
			"59aa363f0514f72c0f9ebff839ffe62dd403a7af2549fb3cb11ef61a563a5129",
			"f0ef6df4934d0cd09fd6e21f47140a214e0d3c7c1dbfaca3c5252913c3747e1c",
			"560202d51fd84b313cc390b7d17c20c8581f726074e31b007c6a938d09b6e304",
			"56b7b9bed88a34cd6f7c60b36b4534d72044ce9bc738ed7a05365b49c5923f47",
			"2ec7d87e678f76714a8f50fa5cef6243260f7b6158168506e94c9b32525b1529",
			"2b7659a0dcfd715ad68eb962d6fcb3299baf92ce6b9c414a568ac22a7ddab5d5",
			"c783af06a385058e1a8f893408ec61b929547fc1d2554923aaa7ce4223e0cf18",
			"6d677d0ca601b5388fb4fe4f16142852ec81cef85215c50a9e0d779090c7766e",
			"e5a8be56e31199087e2b8a31264f9ec3161f4260964fd0717ae84b644157ee0b",
			"5c90011aba1174ba4cc95cc88a306b142687a6bb57b37712e8cebc299e4c3486",
			"05c424dbd9ba3aab616a9488a69cb3b3aa1a6ff928558a6927984ae9bff2aea6",
			"941ecc0529afd469e6528d4b089bdf7a6c050a3533f91cad2f1ccc7f1d8042b7",
			"4ca3af700c3cd55eb6e747c8fd138971ad62d51d52481d544fe80bd9b5aea737",
			"f6e2aa60e46a0ba873ba4351813bc533a9fa34a694959fbefd4e1aabe97c2ca2",
			"6bcf089be20a63c5400f9b2684b17da2a0c7bb9c82f97d5922042f4010d2e3be",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"2f5665d45df3c89e2a23ab8a3c3d097007b538ccacd1426484dae120b293dc4c",
			"3d39412419fe7b07551cf5743c66dd5f74ab0d3a79e5980b1159f759ec5119d8",
			"739fc53e9889950cc333889226c08c24e1679c6acd8ed8479adcd9c7dcd20068",
			"85377614ead13e72dee1706e7df6562d958422214e8d26e990fa8bd2589ef5ed",
			"22d27045d1dfa14f688148d7b64398c933a0f3e0b9cb92df9920df6fa305ffb6",
			"9d1515b7e6d54d13eba2f14f7cdbaec496a79c02d19d7b89e6af4bc2cfe32f1f",
			"3eb500de160e9f2faee68195b1dbe8cb3d37b695efc5a8842ae639b1c307acc4",
			"8af1023c8d2081ace35be7b2458bf236fc18d985f7325567e8ce7e9c6a310a98",
			"b5de1ee8b06368d7c09259cc8f304ed3158c2471a0902955b341f5720360486f",
			"1e0e19a45e3fe3efde362edc194685485e3c22b8841692a4bff9e5aa2bfb1354",
			"05b39750d5959dcdeae715340471e441dfab9ada05a36e0cf247ee447cde4166",
			"043665cdc758c86d5dc6b029980577cdb3d5cf51e9c6805578f7d397ef17bf0b",
			"ecf55fffaf95ab0e4ebea1d22a36b3775fd85feb1657012d4f7467bf30b9bbc4",
			"4aa998cef0edb274819fe5e3f737b9945060c5ec70e5c37404ba6677219114e6",
			"76237beba44ba8c1450631720a9a271352ca17c41285de0c2b3f94a00ea3fcda",
		},
		expectedRoot: "f4ef95dc21c36c0168d8e1c39115487a153b31fd45b89267e2f9b72d1b8f4446",
	},
}

func TestPrefixDictVectors(t *testing.T) {
	for _, vector := range prefixDictVectors {
		t.Run(vector.name, func(t *testing.T) {
			dict, err := Dict(
				[]byte(vector.label),
				vector.version,
				mustDecode(t, vector.publicKey),
				vectorPrefixProof(t, vector),
				vectorLadder(t, vector),
			)
			if err != nil {
				t.Fatal(err)
			} else if got, want := dict.GetRoot(), mustHexDigest(t, vector.expectedRoot); got != want {
				t.Fatalf("root = %x, want %x", got, want)
			}

			for i, version := range vector.ladderVersions {
				got, err := dict.GetCommitment([]byte(vector.label), version)
				if err != nil {
					t.Fatalf("GetCommitment(%d): %v", version, err)
				}
				want := mustHexDigest(t, vector.ladderCommitments[i])
				if want == ([sha256.Size]byte{}) {
					if got != nil {
						t.Fatalf("GetCommitment(%d) = %x, want nil", version, *got)
					}
				} else if got == nil || *got != want {
					t.Fatalf("GetCommitment(%d) = %x, want %x", version, got, want)
				}
			}
		})
	}
}

func vectorPrefixProof(t *testing.T, vector prefixDictVector) proofs.PrefixProof {
	t.Helper()

	results := make([]proofs.PrefixSearchResult, len(vector.prefixResults))
	for i, result := range vector.prefixResults {
		results[i] = proofs.PrefixSearchResult{
			Result_type: result.resultType,
			Depth:       result.depth,
		}
		if result.leafVrfOutput != "" {
			results[i].Leaf = &proofs.PrefixLeaf{
				Vrf_output: mustDecode(t, result.leafVrfOutput),
				Commitment: mustHexDigest(t, result.leafCommitment),
			}
		}
	}

	elements := make([]proofs.NodeValue, len(vector.prefixElements))
	for i, element := range vector.prefixElements {
		elements[i] = mustHexDigest(t, element)
	}

	return proofs.PrefixProof{
		Results:  results,
		Elements: elements,
	}
}

func vectorLadder(t *testing.T, vector prefixDictVector) []proofs.BinaryLadderStep {
	t.Helper()

	if len(vector.ladderProofs) != len(vector.ladderCommitments) {
		t.Fatalf("ladder proof and commitment counts differ")
	}
	ladder := make([]proofs.BinaryLadderStep, len(vector.ladderProofs))
	for i := range ladder {
		ladder[i] = proofs.BinaryLadderStep{
			Proof:      mustDecode(t, vector.ladderProofs[i]),
			Commitment: mustHexDigest(t, vector.ladderCommitments[i]),
		}
	}
	return ladder
}

func mustDecode(t *testing.T, s string) []byte {
	t.Helper()
	if out, err := hex.DecodeString(s); err != nil {
		t.Fatal(err)
		return nil
	} else {
		return out
	}
}

func mustHexDigest(t *testing.T, s string) [sha256.Size]byte {
	t.Helper()
	raw := mustDecode(t, s)
	if len(raw) != sha256.Size {
		t.Fatalf("digest has length %d, want %d", len(raw), sha256.Size)
	}
	var out [sha256.Size]byte
	copy(out[:], raw)
	return out
}
