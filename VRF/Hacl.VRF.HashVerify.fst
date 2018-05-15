module Hacl.VRF.HashVerify

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
open Hacl.VRF.DecodeProof

open Hacl.VRF.Lib

#reset-options " --z3rlimit 100"


val point_sum : pointTo0: point -> pointTo1: point -> pointTo2: point -> 
	pointFrom0: point -> scalarFrom0: word ->   
	pointFrom1: point -> scalarFrom1: word -> 
	Stack unit 
		(requires (fun h0 -> live h0 pointTo0 /\ live h0 pointTo1 /\ live h0 pointTo2 /\
			live h0 pointFrom0 /\ live h0 pointFrom1 /\ live h0 scalarFrom0 /\ live h0 scalarFrom1
			/\ disjoint pointTo0 pointFrom0 /\ disjoint pointTo1 pointFrom1/\ 
			disjoint pointTo2 pointTo0 /\ disjoint pointTo2 pointTo1
		))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies3 pointTo0 pointTo1 pointTo2 h0 h1 ))


let point_sum pointTo0 pointTo1 pointTo2 pointFrom0 scalarFrom0 pointFrom1 scalarFrom1 = 
	point_mult pointTo0 pointFrom0 scalarFrom0;
	point_mult pointTo1 pointFrom1 scalarFrom1;
	point_add pointTo2 pointTo0 pointTo1

val _ECVRF_verify: 
	#len : size_nat -> 
	proof: lbuffer uint8 80 -> 
	inputLength: size_t{v inputLength == len /\ len < maxint SIZE - 96} -> 
	input: lbuffer uint8 len -> 
	pk: point -> 
	Stack bool 
		(requires (fun h0 -> live h0 proof /\ live h0 input /\ live h0 pk))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1))

let _ECVRF_verify #len proof inputLength input pk = 
	alloc #_ #(bool) #(200) (size 200) (u64(0)) 
		[BufItem proof; BufItem input; BufItem pk] 
		[]
		(fun h0 _ h1 -> True)
		(fun pointBuffer -> 
			let pubKey = sub pointBuffer (size 40) (size 20) in 
			copy (size 20) pk pubKey;
			let r_ = alloc #_ #(bool) #(64) (size 64) (u8 (0)) 
			[BufItem proof; BufItem input; BufItem pointBuffer]
			[BufItem pointBuffer]
			(fun h0 _ h1 -> True)
			(fun cs -> 

				let generator = sub #_ #(200) #(20) pointBuffer (size 0) (size 20) in 
				let h = sub #_ #(200) #(20) pointBuffer (size 20) (size 20) in 
				let pk = sub #_ #(200) #(20) pointBuffer (size 40) (size 20) in 
				let gamma = sub #_ #(200) #(20) pointBuffer (size 60) (size 20) in 
				let u = sub #_ #(200) #(20) pointBuffer (size 80) (size 20) in
				let v = sub #_ #(200) #(20) pointBuffer (size 100) (size 20) in 
				let bufferToHash = sub #_ #(200) #(120) pointBuffer  (size 0) (size 120) in 

				let yc = sub #_ #(200) #(20) pointBuffer (size 120) (size 20) in 
				let gs = sub #_ #(200) #(20) pointBuffer (size 140) (size 20) in 
				let gammac = sub #_ #(200) #(20) pointBuffer (size 160) (size 20) in 
				let hs = sub #_ #(200) #(20) pointBuffer (size 180) (size 20) in 

				let gamma' = sub proof (size 0) (size 32) in 
				let c = sub #_ #(80) #(16) proof (size 32) (size 16) in 
				let s = sub proof (size 48) (size 32) in 
				let r = decompress gamma gamma' in 

				if not r then false else begin

				let cExtended = sub	cs (size 0) (size 32) in 
				let cToCheck = sub cs (size 32) (size 32) in 
				let partOfExtended = sub cs (size 0) (size 16) in 

				copy (size 16) c partOfExtended; 
				make_g generator;
				point_sum yc gs u pk cExtended generator s;

				let r = _ECVRF_hash_to_curve h pk inputLength input in
				if not r then false
				else begin	
				point_sum gammac hs v gamma cExtended h s;
				_ECVRF_hashPoints cToCheck bufferToHash;
				let cToCheckLow = sub cToCheck (size 16) (size 16) in 
				let r = equalBuffer cToCheckLow c in 
				r 
				end
				end	
 	
			)
		in r_
	)
