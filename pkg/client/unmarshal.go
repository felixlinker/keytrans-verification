package client

import (
	"bytes"

	"github.com/felixlinker/keytrans-verification/pkg/crypto"
	"github.com/felixlinker/keytrans-verification/pkg/proofs"
	"github.com/felixlinker/keytrans-verification/pkg/utils"
)

// @ requires acc(th)
// @ ensures err == nil ==> acc(th.Inv())
func (th *TreeHead) Unmarshal(buf *bytes.Buffer) (err error) {
	if size, e := utils.ReadUint64(buf); e != nil {
		err = e
	} else if sig, e := utils.ReadBytes(buf, 2); e != nil {
		err = e
	} else {
		th.Tree_size = size
		th.Signature = sig
		// @ fold acc(th.Inv())
	}
	return
}

// @ requires acc(fth)
// @ ensures err == nil ==> acc(fth.Inv())
func (fth *FullTreeHead) Unmarshal(buf *bytes.Buffer) (err error) {
	if typ, e := buf.ReadByte(); e != nil {
		err = e
	} else {
		fth.headType = typ
		fth.Tree_head = nil
		if typ == FullTreeHeadUpdated {
			th /*@@@*/ := TreeHead{}
			if e := th.Unmarshal(buf); e != nil {
				err = e
			} else {
				fth.Tree_head = &th
			}
		}
		// @ fold acc(fth.Inv())
	}
	return
}

// @ requires acc(resp)
// @ requires version != nil ==> acc(version)
// @ ensures err == nil ==> acc(resp.Inv())
func (resp *SearchResponse) Unmarshal(buf *bytes.Buffer, version *uint64) (err error) {
	fth /*@@@*/ := FullTreeHead{}
	search /*@@@*/ := proofs.CombinedTreeProof{}
	// Nc is 16 for all ciphersuites currently
	opening /*@@@*/ := make([]byte, 16)
	value /*@@@*/ := crypto.UpdateValue{}
	if e := fth.Unmarshal(buf); e != nil {
		err = e
	} else {
		resp.Version = nil
		if version == nil {
			if ver /*@@@*/, e := utils.ReadUint32(buf); e != nil {
				err = e
			} else {
				tmp /*@@@*/ := uint64(ver)
				resp.Version = &tmp
				// @ assert acc(resp.Version)
				version = &tmp
			}
		}

		if err == nil {
			// @ assert version != nil
			if ladder, e := proofs.UnmarshalBinaryLadderSteps(buf, *version); e != nil {
				err = e
			} else if e := search.Unmarshal(buf); e != nil {
				err = e
			} else if n, e := buf.Read(opening); n != len(opening) || e != nil {
				err = utils.BufferError(e)
			} else if e := value.Unmarshal(buf); e != nil {
				err = e
			} else {
				resp.Full_tree_head = &fth
				resp.Binary_ladder = ladder
				resp.Search = &search
				resp.Opening = opening
				resp.Value = &value
				// @ fold utils.BytesMem(resp.Opening)
				// @ fold resp.Inv()
			}
		}
	}
	return
}
