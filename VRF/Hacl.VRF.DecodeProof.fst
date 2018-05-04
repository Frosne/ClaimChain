module Hacl.VRF.DecodeProof

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

#reset-options " --z3rlimit 100"

val decodeProof: gamma: point -> 
	c: lbuffer uint8 16 -> s: lbuffer uint8 32 -> 
	proof: lbuffer uint8 80 -> 
	Stack bool 
		(requires  (fun h0 -> live h0 proof /\ live h0 c /\ live h0 s /\ live h0 gamma))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies3 gamma c s h0 h1))

let decodeProof gamma c s proof = 
	let gamma' = sub proof (size 0) (size 32) in 
	let c' = sub proof (size 32) (size 16) in 
	let s' = sub proof (size 48) (size 32) in 
	let valid = decompress gamma gamma' in 
	if not valid then false else 
	begin
		copy (size 16) c' c;
		copy (size 32) s' s;
		true
	end
	