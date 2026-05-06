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
			"dde7bc4500529c2c837cb6d316c9af45c59c5a750ad24c39b0bff33bd88055f43e872d58e270f40738502e9b5e69b3f64257c2900d193e16c8598416e57872e05988aea086dd75112e56275417a72502",
			"3081be8b1a45fecb0c280d12f08a4db47aeba960123475f559ec55a31e252cfae1788005f7cf25770c5ed18baab9529159f735e23c57ef994335796a3d14fafadaa1b189248495f908391406c982820e",
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
				leafVrfOutput:  "b9e10134e1c253851d8f01a61b0b9f10d38a204dc14c7b2b582529a1f95952cf24234a35e0302d97999d6af1dc86a6315f4c3dbd21a54d7ee0e9b64841ee2049",
				leafCommitment: "1d3cad4abf6fbbcd85e5904b6c00c7e579b6c96fd79be88063e05b9eb34d08b0",
			},
		},
		prefixElements: []string{
			"0af78065d37fb5a4da0b878c17461a17e9bec88a8ec3b5d5cf872b563cf65523",
			"205562dbccc61b4e57b902408c1bb8c3ae7e97d798eb85201122772eb9dbf2a4",
			"95dd1dda593d40c9d3089d1c17605b8f076c9d35dc01606fe6a8683a15907bac",
			"a3b52da37884290ca1aff3bb66b383887638f6df02d6a1616c905d3544d3325a",
			"7a3b98a1ae2fe1dcd02ceed423a2c74137901997a040229ff57a1d029317cdd6",
			"5db15b9bd4ea6edcc207d372232728b931d6ab3579970ac7a843ddae85b5279d",
			"2edac8fc29aa81773db2aa8ebd3dd8d1cff7791b1a1ad17cb2a8411271ce0f10",
			"bfe1b8439c216b6fdb9ddd07fb272bab549263b1cd17f82d2d8b20f210395b08",
			"b9697202de55b1f7111352235591f2ff8a73be896b5c6fb6b3548249d6ddacb2",
			"4b0741137b576e523ba6d1011eaeca9e71fbc42dccf63beb510e55e2c71f835c",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"1d37f5411d78b9d707426ad954c7f9fc58070519584820366ef3346eb74e41dd",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"b7d760763ed8fae26d69640dfa947d31e1181ef65f6a2b88cb17cee9189c7e0d",
			"8244e292e659d0848e65300aad0087711cc8487fa5f8b417ed7b0ad73c53e7ab",
		},
		expectedRoot: "0e8bac26e3ccb747b788f64075f0d3a6c311888f2d4a6d19f576e0ab5e2c710d",
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
			"f28a098fd2f88dcd67d34434aa4c54539d94efa71bb4e62952e5de12892c5a63191d27459c3489c88d95c8923f7f00acbfcff1be98a6290a0473ca86a179464bc97a35b17979d3e63fc04775d88c8c0d",
			"17a25f78520dc766b8f7a3e7082513125a5151dd68284516518a45013d7556fe69ba1408cb887930143d7e33697d88bbf2c462bf9b73d9232d3a702721ece859347b3fa7874a198f5daa7e173de0db0a",
			"3d838db0b118c0b12c64653728043ed57ae914e4476ce7772408a6ef4bbe2a428273dbe088ce874d207a4dfdaab84891c34118b3fbd6bfa4246c674736b52f3891025cc45ad33cf2bbd95b0ff602c602",
			"4cfb90b56d533cd5ce44e1e75f6f8aab762ee7e7854e6c31dbf3a05c192a8bf732e86c80e894f88161db9f37bbb12ca3e06cd6f03e9ac0ebbb16c5f8f05d86b1182ad8638ecb872d45c91b1ea5fd2f02",
			"05db54f9c4a74bf2447ab48104972352ab8840c977f32ae092cd41c7fec35071a8bd2251062425bb202bc0ed3bd5cca334329b295aedd16589a15563f37d4342f67339b96a132adf003d119ee7897d07",
			"3aa1b5d8aead56856ac6746f94f4c042b1c1e4f5238dc0e38f53c688214469db14c7d1abffd8e3fe726bbb014556ea7c2631e722b48f74e704d79db010df29b82b159e2ce04e3eefb07fcdc1985b5203",
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
				leafVrfOutput:  "0d27ee61e1071c19a29d4878768468a543972fe23bc403e1185e4951405ea4494d94b140562ffc6f9da365e178beaabf7c487da1ca2ceefb33525127927cb4b1",
				leafCommitment: "5c48d2bbc2d5f5f4b177642c0f33158cfcbad17dd4fbcf19dcf474276c6f7c96",
			},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          10,
				leafVrfOutput:  "4750d039b49adc9b9845d7753737377b1c8f46191b13d45ade7e04da575e4962c63f95f061788403934d923fbc9801b4be9743ace4eafee44eff5b947a061eba",
				leafCommitment: "31617fe06c9b3cd08d8df863cf8d7f10676f746b134ef656badde3343b6ee7b3",
			},
			{
				resultType:     proofs.NonInclusionLeaf,
				depth:          8,
				leafVrfOutput:  "33dad0f922a7a64389019e5a78ac010bd37d35caa980488f2168ba49ed8c0783afc49370e143cafeab8f45c46e3de4d2a5859224376e4327967ebfbb73dd1f5b",
				leafCommitment: "7ed59722dc0112eee27856ff4de8e0c9f73f6120955fbbb22aead928bf76759e",
			},
		},
		prefixElements: []string{
			"3d3078424edb3133a21054a822ab80274676f8623fe27772675bbdde262e4c63",
			"27ae58fa53d827972c1cc343053981fc64e275cc747387ca4f18cecca25b1050",
			"d5618f2df28655ae338ff367d9dedea32a713cc5b2e106d919852cc2835ed785",
			"a48c8e71de793bcb70abc0c0dfeffebf2d77101368b7dea9072af633c32d430f",
			"d806e69ebd842c2897b562636eb103f05f7e18726bbb18b2c0a5bcbcf1bf2385",
			"59928990ac18210c21c321bf442d7ae6c9dbc6b4dbafe6756ab7f568f49431c7",
			"ff18f993c0ce77d0eb591a3b9ac30735a16ab62630158c834604ef58cebf1e72",
			"f5e04e7d4bd6dd7de1183f23be84d85c3d605a62f1d33b6f87d8e34af4e9ec44",
			"176798e141c5041a4531b9b766befea699e55715c4ff21759ac752b3e390b983",
			"189fd91046ef14569d8fd3095bf0a7d079ce3c30e2889b258598237ff180a792",
			"4c3eb3459861d32dc5764d631d113a593de65fa9491e76ed02c304dfef28e074",
			"9e736e737843dd93feb803039aa29ea5a3289731b37f422dbfbf3b8fad8607a1",
			"03d65a00050e50aa8d1269834d99cba3a1747c3d5b7dd8aed7b91580184c5ec9",
			"0ce874dee35d09e140673f2adb14ee0ee081cec5bd00541bc1cddc0cd00e6d8e",
			"bbf09da0254942075b6a44afd359b704ea39b424e9d5875def090222cf93dadb",
			"7cd64d9417fd52f84e46335c613ac1f50c1a353795a129eaae0ed79f449282fc",
			"fc7091fdd36e9fead68f94b0e5a46662c3fa919143bb84a990f425a1510e1c0f",
			"09c8068611fff1d1224d80b790719808e83c46c0a36d6352583b334a2385224c",
			"0000000000000000000000000000000000000000000000000000000000000000",
			"62fa9ed994e2ac23af228b9c8e24bc12e76227081cfa807e693884e0525a7087",
			"8870239321faea5fc72ec40cac392d45c514a138e4c8c2033731811aeff3daa5",
			"343c6ddc59bc2ce637711b64640346d65fecf9bb485df41d7307cbe3b01b2e94",
			"eab4aa4955691df899ee39446cd9ffc996d48b1fb9b0033d5b9d338c1703bc43",
			"edb56bc67028adf53c8472202168f7ab846ac583980698ed40ef373137c23826",
			"09084dc8ac532160ce9c50aa43deafdbb90f4f5ca9595705bf089ebc012e4b09",
			"475863226ae01aed4b500397a55033ed1096b2640414cf008b1945f3801696b4",
			"012b41670dc26bf80ca45bf78535d19f9035719fcf01e8459ef57844a4b26765",
			"e7437649513680bc37f22161ef603b446e5f01bb9d1e8d944d0d694317142a83",
			"d977ac7763a547162159db85afece3ba793f0f2d44ca484a9de9f7868103c600",
			"81b2b1d7d630913e53d96d4ccedd9299fe87516eb6f9c11ace4fcbfe51183a12",
			"a542d63825b0cd1d7494dd4377e2db0e75133ca89517637ebf378121091b2374",
			"75885af4db3ba814f7b1985b9a854e24736dadf3a05faf9608877c883d72d7f7",
			"a9b99c80dc0dc8e4830a6c208dd5c8820be4c68dd46c22cf6574c9e93ff8849d",
			"b7138c56ea7f62347921e2c88973ae489897c3992d1d2893309ff0a308dd289a",
		},
		expectedRoot: "3a8ec5c4a66e79d6371e9b4f14c0a7964abac205f7f7b7542b23fc81d642eed3",
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
