module Hacl.VRF.ProofToHash

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntSeq

open Spec.Lib.IntTypes
open Spec.Lib.IntBuf
open Spec.Lib.IntBuf.Lemmas

open Hacl.VRF.HashToCurveFinal
open Hacl.VRF.HashPoints

open Hacl.VRF.Lib

val partialDecodeProof: gamma: point -> 
	proof: lbuffer uint8 80 -> 
	Stack bool 
		(requires  (fun h0 -> live h0 proof /\ live h0 gamma))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 gamma h0 h1))

let partialDecodeProof gamma proof = 
	let gamma' = sub proof (size 0) (size 32) in 
	let valid = decompress gamma gamma' in 
	if not valid then false else true

val proofToHash:
	beta: lbuffer uint8 32 ->
	proof: lbuffer uint8 80 -> 	
	Stack bool
		(requires  (fun h0 -> live h0 proof /\ live h0 beta))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 beta h0 h1))
			
let proofToHash beta proof = 
	alloc #(uint64) #(bool) #(20) (size 20) (u64(0)) 
		[BufItem proof]
		[BufItem beta]
		(fun h0 _ h1 -> True)
		(fun pointBuffer -> 
			let r = partialDecodeProof pointBuffer proof in 
			if not r then false else begin
			pointMult8 pointBuffer pointBuffer;
			let sizeHash = size 32 in 
			alloc #(uint8) #(bool) #(v sizeHash) sizeHash (u8(0))
				[BufItem pointBuffer]
				[BufItem beta]
				(fun h0 _ h1 -> True)
				(fun bufferForPreHash->
					let bT = sub  bufferForPreHash (size 0) (size 32) in 
					compress bT pointBuffer;
					hash beta (size 32) bufferForPreHash;
					true
				)
			end
		)	

