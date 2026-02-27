package client

type DeploymentMode uint8

const (
	DeploymentModeReserved         DeploymentMode = 0
	DeploymentContractMonitoring   DeploymentMode = 1
	DeploymentThirdPartyManagement DeploymentMode = 2
	DeploymentThirdPartyAuditing   DeploymentMode = 3
)

type Configuration struct {
	Mode                       DeploymentMode
	ReasonableMonitoringWindow uint64
	/*
		Ciphersuite                uint16
		SignaturePublicKey         []byte
		VrfPublicKey               []byte
		LeafPublickey              []byte //Only for Contact monitoring or ThirdParty
		MaxAuditorLag              uint64 //Only for ThirdParty
		AuditorStartPos            uint64 //Only for ThirdParty
		AuditorPublickey           []byte //Only for ThirdParty
		MaxAhead                   uint64
		MaxBehind                  uint64
		MaximumLifetime            *uint64 //Optional
		Nc                         int	   //Size of Commitment opening
		Kc                         []byte  //Fixed string for commitment computation
	*/
}

//
