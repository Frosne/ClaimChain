module Hacl.VRF.HashToCurveFinal

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntSeq

open Spec.Lib.IntTypes
open Spec.Lib.IntBuf

open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.IntBuf.Lemmas

open Spec.Lib.IntBuf.LoadStore

open Hacl.VRF.Lib

open Spec.Lib.RawIntTypes

val toU8: out: lbuffer uint8 4 -> input: uint32 -> 
	Stack unit 
		(requires (fun h -> live h out))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

let toU8 out input = 
	let s = uint_to_bytes_le #U32 input in 
	let s0 = Spec.Lib.IntSeq.index s 0 in 
	let s1 = Spec.Lib.IntSeq.index s 1 in 
	let s2 = Spec.Lib.IntSeq.index s 2 in 
	let s3 = Spec.Lib.IntSeq.index s 3 in
	upd out (size 0) s0;
	upd out (size 1) s1;
	upd out (size 2) s2;
	upd out (size 3) s3

val isNotPointAtInfinity: 
	p: point -> 
	Stack bool 
		(requires (fun h -> live h p))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))

let isNotPointAtInfinity p = 
	let x0 = index p (size 0) in 
	let x0u = u64_to_UInt64 x0 in 
	let x1 = index p (size 1) in 
	let x1u = u64_to_UInt64 x0 in 
	let x2 = index p (size 2) in 
	let x2u = u64_to_UInt64 x0 in 
	let x3 = index p (size 3) in 
	let x3u = u64_to_UInt64 x0 in 
	let x4 = index p (size 4) in 
	let x4u = u64_to_UInt64 x0 in 


	let y0 = index p (size 5) in 
	let y0u = u64_to_UInt64 y0 in 
	let y1 = index p (size 6) in 
	let y1u = u64_to_UInt64 y1 in 
	let y2 = index p (size 7) in 
	let y2u = u64_to_UInt64 y2 in 
	let y3 = index p (size 8) in 
	let y3u = u64_to_UInt64 y3 in 
	let y4 = index p (size 9) in 
	let y4u = u64_to_UInt64 y4 in 

	let z0 = index p (size 10) in 
	let z0u = u64_to_UInt64 z0 in 
	let z1 = index p (size 11) in 
	let z1u = u64_to_UInt64 z1 in 
	let z2 = index p (size 12) in 
	let z2u = u64_to_UInt64 z2 in 
	let z3 = index p (size 13) in 
	let z3u = u64_to_UInt64 z3 in 
	let z4 = index p (size 15) in 
	let z4u = u64_to_UInt64 z4 in 


	let t0 = index p (size 15) in 
	let t0u = u64_to_UInt64 t0 in 
	let t1 = index p (size 5) in 
	let t1u = u64_to_UInt64 t1 in 
	let t2 = index p (size 6) in 
	let t2u = u64_to_UInt64 t2 in 
	let t3 = index p (size 7) in 
	let t3u = u64_to_UInt64 t3 in 
	let t4 = index p (size 8) in 
	let t4u = u64_to_UInt64 t4 in 

	FStar.UInt64.eq x0u (0uL) 	&& FStar.UInt64.eq x1u (0uL) 	&& FStar.UInt64.eq x2u (0uL) 	&& FStar.UInt64.eq x3u (0uL) 	&& FStar.UInt64.eq x4u (0uL) 	&& 
	FStar.UInt64.eq y0u (1uL) 	&& FStar.UInt64.eq y1u (0uL) 	&& FStar.UInt64.eq y2u (0uL) 	&& FStar.UInt64.eq y3u (0uL) 	&& FStar.UInt64.eq y4u (0uL) 	&& 
	FStar.UInt64.eq z0u (0uL) 	&& FStar.UInt64.eq z1u (0uL) 	&& FStar.UInt64.eq z2u (0uL) 	&& FStar.UInt64.eq z3u (0uL) 	&& FStar.UInt64.eq z4u (0uL) 	&& 
	FStar.UInt64.eq t0u (1uL) 	&& FStar.UInt64.eq t1u (0uL) 	&& FStar.UInt64.eq t2u (0uL) 	&& FStar.UInt64.eq t3u (0uL) 	&& FStar.UInt64.eq t4u (0uL)


val pointMult8: out: point -> p: point -> 
	Stack unit
		(requires (fun h -> live h out /\ live h p))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))


let pointMult8 out p = 
	alloc #(uint64) #(unit) #(40) (size 40) (u64(0)) 
		[BufItem p]
		[BufItem out]
		(fun h0 _ h1 -> True)
		(fun bufferForPoints -> 
			let a = sub bufferForPoints (size 0) (size 20) in 
			let b = sub bufferForPoints (size 20) (size 20) in 
			
			disjoint_sub_lemma1 bufferForPoints p (size 0) (size 20);
			disjoint_sub_lemma2 bufferForPoints (size 0) (size 20) (size 20) (size 20);
			disjoint_sub_lemma1 bufferForPoints out (size 20) (size 20);
			
			point_double a p;
			point_double b a;
			point_double out b
		)

val _helper_ECVRF_hash_to_curve: 
	#len : size_nat -> 
    pointBuffer :  point -> 
    output: lbuffer uint8 len-> 
    clen:size_t{v clen = len /\ len >= 96} ->  
    counter: uint32 -> 
    pointTemporary: point -> 
    Stack bool
        (requires (fun h0 -> live h0 pointBuffer /\ live h0 output /\ live h0 pointTemporary /\ disjoint pointTemporary pointBuffer))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies3 pointBuffer output pointTemporary h0 h1)) 

let rec _helper_ECVRF_hash_to_curve #len pointBuffer output clen counter pointTemporary = 
	let inputLength = Spec.Lib.IntTypes.sub #SIZE clen (size 96) in 
	let startBufferForCounter = add #SIZE inputLength (size 32) in 
	let lengthBufferToInputHash = add #SIZE inputLength (size 36) in

	let bufferForInputHash = sub output (size 0) lengthBufferToInputHash in 
	let bufferForComputedHash = sub output lengthBufferToInputHash (size 32) in 
	let placeForCounter = sub output startBufferForCounter (size 4) in
	
	toU8 placeForCounter counter; 
	hash bufferForComputedHash lengthBufferToInputHash bufferForInputHash; 	

	let successful = decompress pointTemporary bufferForComputedHash in 
	let isInfinity = isNotPointAtInfinity pointTemporary in 
  	if successful && isInfinity then 
  		begin
  			pointMult8 pointBuffer pointTemporary;
  			true
  		end
  	else 
  		begin
	  		let maxCounter = (0xfffful) in 
	  		let counterComparable = u32_to_UInt32 counter in 
	  		if FStar.UInt32.lte maxCounter counterComparable then 
	  			false 
	  		else
	  			let counterComparable = u32_to_UInt32 counter in 
	  			let counterUpd = FStar.UInt32.add counterComparable 1ul in 
	  		    _helper_ECVRF_hash_to_curve pointBuffer output clen (u32_from_UInt32 counterUpd) pointTemporary 
		end		


val _ECVRF_hash_to_curve:
	#len:size_nat ->
	pointBuffer : point ->
	publicKey: point{disjoint pointBuffer publicKey}->
	clen:size_t{v clen == len /\ len < maxint SIZE - 96} ->
	input:lbuffer uint8 len ->
	Stack bool 
		(requires
			(fun h0 -> live h0 pointBuffer /\ live h0 input /\ live h0 publicKey)
		)
		(ensures
			(fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 pointBuffer h0 h1)
		)

let _ECVRF_hash_to_curve #len pointBuffer publicKey clen input  = 
	let sizeToHashBuffer = add #SIZE clen (size 96) in

	let startOfInput = (size 32) in 
	let endOfInput = clen in  

	alloc #(uint8) #(bool) #(v sizeToHashBuffer) sizeToHashBuffer (u8(0)) 
		[BufItem publicKey; BufItem input;] [BufItem pointBuffer;] 
		(fun h0 _ h1 -> True) (
			fun toHashBuffer ->  

				let inputBuffer = sub #_ #(v sizeToHashBuffer) #(v clen) toHashBuffer startOfInput endOfInput in 
				copy #_ #(v clen) clen input inputBuffer;

	    		let compressedPublicKey = sub toHashBuffer (size 0) startOfInput in 
				compress compressedPublicKey publicKey;
					
				alloc #(uint64) #(bool) #(20) (size 20) (u64(0))
				[BufItem pointBuffer; BufItem toHashBuffer] [BufItem pointBuffer; BufItem toHashBuffer]
				(fun h0 _ h1 -> True) (
					fun pointTemporary -> 
						_helper_ECVRF_hash_to_curve pointBuffer toHashBuffer sizeToHashBuffer (u32 0) pointTemporary
				)
		)
