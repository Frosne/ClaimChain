module Hacl.VRF.HashPoints

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib

open Spec.Lib.IntTypes
open Spec.Lib.IntBuf

open Spec.Lib.IntBuf.Lemmas

open Hacl.VRF.Lib

assume val compress: 
	out: lbuffer uint8 32 -> 
	input: lbuffer uint64 20 -> 
	Stack unit 
		(requires (fun h -> live h out /\ live h input))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))


assume val hash: 
	hashBuffer: lbuffer uint8 32 ->
	inputLength: size_t -> 
	input: lbuffer uint8 (v inputLength) -> 
	Stack unit
	(requires (fun h -> live h hashBuffer /\ live h input /\ disjoint hashBuffer input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 hashBuffer h0 h1))


val _ECVRF_hashPoints: hashBuffer: lbuffer uint8 32 ->
	points: lbuffer uint64 120 ->
	Stack unit 
		(requires (fun h -> live h hashBuffer /\ live h points /\ disjoint hashBuffer points))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 hashBuffer h0 h1))

let _ECVRF_hashPoints hashBuffer points = 
	let size_hash = size 192 in 
	alloc #_ #_ #(v size_hash) (size_hash) (u8(0)) 
		[BufItem points] [BufItem hashBuffer] 
		(fun h0 _ h1 -> True) (
			fun tmp -> 

		let pointA = sub #(uint64) #(120) #(20) points (size 0) (size 20) in 
		let pointB = sub #(uint64) #(120) #(20) points (size 20) (size 20) in 	
		let pointC = sub #(uint64) #(120) #(20) points (size 40) (size 20) in 
		let pointD = sub #(uint64) #(120) #(20) points (size 60) (size 20) in 
		let pointE = sub #(uint64) #(120) #(20) points (size 80) (size 20) in 
		let pointF = sub #(uint64) #(120) #(20) points (size 100) (size 20) in

		compress (sub tmp (size 0) (size 32)) pointA;
		compress (sub tmp (size 32) (size 32)) pointB;
		compress (sub tmp (size 64) (size 32)) pointC;
		compress (sub tmp (size 96) (size 32)) pointC;
		compress (sub tmp (size 128) (size 32)) pointE;
		compress (sub tmp (size 160) (size 32)) pointF;
		
		hash hashBuffer size_hash tmp 
	)
