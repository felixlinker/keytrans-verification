package client

import (
	"bytes"
	"encoding/hex"
	"testing"
)

const latestSearchSignaturePublicKeyHex = "03a107bff3ce10be1d70dd18e74bc09967e4d6309ba50d5f1ddc8664125531b8"
const latestSearchVrfPublicKeyHex = "29acbae141bccaf0b22e1a94d34d0bc7361e526d0bfe12c89794bc9322966dd7"
const latestSearchReasonableMonitoringWindow uint64 = 86400000

type latestSearchTestVector struct {
	name          string
	label         string
	treeSize      uint64
	latestVersion uint64
	value         string
	responseHex   string
}

var latestSearchVectors = []latestSearchTestVector{
	{
		name:          "single-user-single-key",
		label:         "alice@example.com",
		treeSize:      1,
		latestVersion: 0,
		value:         "alice-key-0",
		responseHex:   "0200000000000000010040b0c899d052126beedd7d17ed43c06642cebf579acd059a2620eca817e249f89c9ca0ba7d26a923845872f671c8e8940a2af086b983253042b7b2129d612fa9070000000034513106b38198632ac64727e4ee76df0000000b616c6963652d6b65792d3002c3b4b11599552e52008967055e04150ed27ef833f3a8b19a1352b33e4f62248ee7a64ce2e92f5b18d6560375f98fcb3e92e24fde620059118ed466dd32647033a5d5429135abc4dd9820a2dcd86817000068dae966c38d7f1160e31ce5a7e3b15b321f9603a389ceaf14ef4b36e6fa6b0087e6b2c1b357dd0e93571cbc36aadc9ea51c933cd2759730ebbf1015b8bbb88d6dc11f290415e2b0b3b68f9b9c7e8d0b00010000019fb32063c0010201000238af11e3933e8783de55f4baeb3cadd3579be715b4ed7e5c2917b19cbbde562e7226d23ac37b3be87d3f51dd5e33ec57059d98e6a3b02f39d830cb4314a52121000000000000",
	},
	{
		name:          "interleaved-users-and-updates",
		label:         "bob@example.com",
		treeSize:      5,
		latestVersion: 2,
		value:         "bob-key-2",
		responseHex:   "020000000000000005004057ad50e58a1bc185a4218a6d634ec0d170e86516958250a047ee40cf23a5a807af600bd3eba7b2205319b6e20af60841e4d98efbd72935bca784c10738fbe707000000023e18bec95c689ac2022e6a73933b390300000009626f622d6b65792d3204c0d0aa2eb560ee5575ce78e96d3642be0893b52f0dbffcec92ff3aa101fc8da19c73b1325239fe06e00dcb77547459c8da687390f2cd4575d8b12a140037125d2bf0696a53763df9ac757a552eda180c0117334276ad55c9c020ad47d439a0dff8b526f2c4e9fa8a4f8889ab553bc76ee45da55f817e850d18148e5eff8ecc8a1ed27712e39f04e4d50eb2584baac174b90e0ee879a0e2829e9d73aa752864f053cf84bbf0cdac0e2d0991a644ff32f0a9615938f0c9eefe4a3969685430ea5d0001bcf383e753f5cf5b80c39e05a75ca3edab036365d11d11139e4b813a8d24117b66b217d2fc0c0f68020b387607d10d837cbd54b32c9465432535aaa80c5847a4f904d6d3a5e21a719eae33f78320e844355c42bc2f7028b3c648712cdeec7e56574c28495a609ce525b748b7ff098f0400d2149defb9a156402ab0ad753c5dec9990a8cd04424b834ee713bce01ddf2702143093a42dc77362093e2b28c52957bf88012ac17bff573de133cdff48dc65e34a066737dd94f7aac381ca630f72d00f00020000019fb32063c30000019fb32063c4020401030109030203040008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f731bb0e8a8f0005c95557a3a5b8fee277d67cb060490e616862ca93905875c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b80af459c7e3459e9d73ece203fd4ecafbc492c5eaebac9a8e1fb30823cf9c4b020302010400030000000000000000000000000000000000000000000000000000000000000000a8e20c10d9ed2421533a7cddda4bdb33f494cc476f9beaf4aee08078aa79db5f3de126e2b7f105763ea8b06ac1d91870f3a3d32bdb5da91d5355f135c707665f000002a29102088e8e1fbc017dd1b028d0a74d2a9e2b0e10cbddb4e1f883ed207a158d4bb5f9f6212bc6d26465dec933640732d265f844d96588b0ba80a042e6eb3822",
	},
	{
		name:          "deep-log-with-long-version-history",
		label:         "zoe@example.com",
		treeSize:      16,
		latestVersion: 6,
		value:         "zoe-key-6",
		responseHex:   "02000000000000001000409aebdc8caf181b0c933a3d0a1ac8b5e7b92aec6dedbab31ab26b5b865ab7925f8c432173747e449f3f149a21cb42d1817e50a4bbf1797ef5336ad3dbd87fca010000000614e2e0737ce57fdf897e4a3eaf9fca38000000097a6f652d6b65792d3606286cfa3b36c4378e5629739828c03fb35592051c1b79a42ddd7611d149ce157e5f02320ad43e5646813597bc7823a3e221c85e19fc0de7edfc0b250191eb6ae15e9fd9bc6ce88eb0ed27a8bb53f42606013fd18e0144cb7f6a0fc57eaa7d57a300833ab51050cb013843bf143c73a110482faca3c312e37ec1795017a59660053229e626bee21fc716e2ab7d3baa8f072a92cf562b630d0aded9196a8832eb0e00f52694b01335e1b3b18c4d22a539a8d5c703117bf5887cf9eb0302a8d060ca0401f1c8d5479309b3128df32cf2e077ac0cceaf83a3038ebb156f5d4f2e9cba0b2299aefb51759f3421a152640118a1729660e177b143b01640873b388e0462e192947d75e7fb54d9a89b2e0d3a8e0bb3137abf27027390404a405b1a79f335c802f7096019a1d9f6ec33fad56e8384b00201dc10d15658bf48870655071332283ff8fea77917d64eda7e0a5e9517c08fbb8b799b3eb3ee83b3b193abf6b5e291c63c15d5a8768f55074773ee71d9a0336a8009926b423a8254e3e98a765e8e113924912120658ccdc6b535e247a7a2a02096ac0bb5181991fd48181cc0c97cd5d70c003acd970550c0aa4f17a6a72f260e3ca503186ba29d596f01ec1eec59d9f3e4e1a4aa2faea6ba0747dbce44e3521d4ba3ba019d4bb0b2e4cf1f8bf5d0788d7a18a4bc7ac70b337467a3733b76b37d4e0d01a904c2242f9c2569554627604bc00c65c092782bda5f89e554dddaa7f8d927931c70577971a21125bee46d22454826f71a9a5315315ccadebb928e50aeca49a71d68f876578e2b430081dac087ac65d316a5e4ce853f4b5c11bfde6b532056ef4a7c789e8e5bc4974c190fa399bb2a0500010000019fb32063ca010601040108010602776e5a1d30df15f157e56b70db325619d161455c0c1f70fbde422a202e0d04803fd18e0144cb7f6a0fc57eaa7d57a300833ab51050cb013843bf143c73a1104804010601090012a5c2847414836af92da4ad191d99e2dd3c20aa35d9e4b28c594f2fa190dd186ad77387fff1f3fd8342b95a9081ae78f622d1ffcab11a558eda1c7b3f7ba820076099b59b3934de9f213c22fb8b606f278078d5f97b971cd58b228aeac401c6cf0000000000000000000000000000000000000000000000000000000000000000263d2e463614a8c14ce10ed9c0ada7c69bb39e33d1e3aa8b72d92dc29a0187980000000000000000000000000000000000000000000000000000000000000000bc1e667bf491c5b3f032a619cc5471265d7aacc9b109c69a1d2debd291fb741b489517403b36936f0e4ea79fea4bd3221bd6e1f3920abf727cc0505cccc798804120fa9f8cc3dfb318bc62daf24e9d7108161bc65c122a5eaae12d77e43cf5de00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d426e59c64ccfccaebfe628ca2ecc3c37a38f346fdf3c99aafabfa9dee6379b500000000000000000000000000000000000000000000000000000000000000000bcc3840b67ad3874a0b68f4b427e92f5902bd0fae8610ca2281ded2220b2dd03a33ad0582ac535d16ad1defc4e7ab8f6df76a210a9260f1fd14505acb4033a6321532d4c94e19d8e3c03be1feab9e08d0d857b5400b634ae74059cd0891905a6af6119e308d6f8ce316569792b767255390457f7694becadc918ad55882be52830ebf44ac4a703e4291b8cdd9d3a72b50096e613c92f50956d25371c046fe780000042322228f8591dc26f9a4f3937ef3f06aef31717563deb599c1557114c0a64e1990d36ec95274e7d374ad28f103c8773d6756257dd311616602ffc09757fe80d17010d9246a49be9d37b3729d01b6559ffc228c221e8db86e5a844c7b48840b2697696b644d3cbadddbc57361cd838853e972fe59b10ff6d3e260b0b555d5adae",
	},
}

// @ trusted
func _TestVerifyLatest(t *testing.T) {
	signaturePublicKey, err := hex.DecodeString(latestSearchSignaturePublicKeyHex)
	if err != nil {
		t.Fatalf("decode signature public key: %v", err)
	}
	vrfPublicKey, err := hex.DecodeString(latestSearchVrfPublicKeyHex)
	if err != nil {
		t.Fatalf("decode VRF public key: %v", err)
	}

	for _, vector := range latestSearchVectors {
		t.Run(vector.name, func(t *testing.T) {
			responseBytes, err := hex.DecodeString(vector.responseHex)
			if err != nil {
				t.Fatalf("decode response: %v", err)
			}

			responseBuffer := bytes.NewBuffer(responseBytes)
			var response SearchResponse
			if err := response.Unmarshal(responseBuffer, nil); err != nil {
				t.Fatalf("unmarshal response: %v", err)
			}
			if responseBuffer.Len() != 0 {
				t.Fatalf("%d trailing response bytes", responseBuffer.Len())
			}
			if response.Version == nil {
				t.Fatal("response version is nil")
			}
			if got := *response.Version; got != vector.latestVersion {
				t.Fatalf("response version = %d, want %d", got, vector.latestVersion)
			}
			if response.Value == nil {
				t.Fatal("response value is nil")
			}
			if got := string(response.Value.Value); got != vector.value {
				t.Fatalf("response value = %q, want %q", got, vector.value)
			}
			if response.Full_tree_head == nil || response.Full_tree_head.Tree_head == nil {
				t.Fatal("response tree head is nil")
			}
			if got := response.Full_tree_head.Tree_head.Tree_size; got != vector.treeSize {
				t.Fatalf("response tree size = %d, want %d", got, vector.treeSize)
			}

			config := &Configuration{
				Mode:                       DeploymentContractMonitoring,
				ReasonableMonitoringWindow: latestSearchReasonableMonitoringWindow,
				SignaturePublicKey:         signaturePublicKey,
				VrfPublicKey:               vrfPublicKey,
			}
			state := &UserState{Config: config}
			request := &SearchRequest{Label: []byte(vector.label)}

			value, err := state.VerifyLatest(request, &response)
			if err != nil {
				t.Fatalf("VerifyLatest: %v", err)
			}
			if value == nil {
				t.Fatal("VerifyLatest returned a nil value")
			}
			if got := string(value.Value); got != vector.value {
				t.Errorf("value = %q, want %q", got, vector.value)
			}
			if got := state.Tree.GetSize(); got != vector.treeSize {
				t.Errorf("tree size = %d, want %d", got, vector.treeSize)
			}
		})
	}
}
