module Hacl.VRF.HashToCurve

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntSeq

open Spec.Lib.IntTypes
open Spec.Lib.IntBuf

open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.IntBuf.Lemmas
open Hacl.VRF.Lib

open Spec.Lib.RawIntTypes

#set-options " --z3rlimit 200 "

assume val hash: 
	hashBuffer: lbuffer uint8 32 ->
	inputLength: size_t -> 
	input: lbuffer uint8 (v inputLength) -> 
	Stack unit
	(requires (fun h -> live h hashBuffer /\ live h input /\ disjoint hashBuffer input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 hashBuffer h0 h1))

assume val toU8: out: lbuffer uint8 16 -> input: uint128 -> 
	Stack unit 
		(requires (fun h -> live h out))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

assume val compress: 
	out: lbuffer uint8 32 -> 
	input: point -> 
	Stack unit 
		(requires (fun h -> live h out /\ live h input))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

assume val decompress: 
	out: point -> 
	input: lbuffer uint8 32 -> 
	Stack bool 
		(requires (fun h -> live h out /\ live h input))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

noeq type bignumCounter = 
	|C: high: uint_t U128 -> low: uint_t U128 -> bignumCounter

val bignumCounterInc: b: bignumCounter{let h = uint_v b.high in let l = uint_v b.low in (pow2 128 * h + l) < pow2 256 -1} -> r: bignumCounter{
	let h = uint_v r.high in let l = uint_v r.low in 
	let h_ = uint_v b.high in let l_ = uint_v b.low in 
	(pow2 128 * h_ + l_ ) + 1 = (pow2 128 * h + l)}

let bignumCounterInc b = 
	let m = u128(0xffffffffffffffffffffffffffffffff) in 
	let m_ = u128_to_UInt128 m in 
	let one = u128_to_UInt128 (u128 1) in 
	let zero = u128_to_UInt128 (u128 0) in 
	let h = u128_to_UInt128 b.high in 
	let l = u128_to_UInt128 b.low in 
		if FStar.UInt128.eq l m_ then begin
				assert_norm((pow2 128 -1) * pow2 128 = pow2 256 - pow2 128);
			let h = FStar.UInt128.add h one in 
			let l = zero in 
			C (u128_from_UInt128 h) (u128_from_UInt128 l) 
		end	
		else
			begin
			let l = FStar.UInt128.add l one in 
			C (u128_from_UInt128 h) (u128_from_UInt128 l) 
			end

(* TODO: *)

assume val bignumCounterLess: b: bignumCounter -> c: bignumCounter -> Tot (r : bool {r == true ==> 
	(let h = uint_v b.high in let l = uint_v b.low in 
	let h_ = uint_v c.high in let l_ = uint_v c.low in 
	(pow2 128 * h + l) < (pow2 128 * h_ + l_))})

(* TODO: *)
val pointCompare: a: point -> b: point -> Stack bool 
	(requires (fun h0 -> live h0 a /\ live h0 b))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1))

let pointCompare a b = 
	let a0_i = (index a (size 0)) in 
	let a0 = u128_to_UInt128 a0_i in 
	let b0_i = (index b (size 0)) in 
	let b0 = u128_to_UInt128 b0_i in  
	let eq = FStar.UInt128.eq in 
	eq a0 b0

val _helper_ECVRF_hash_to_curve: 
	#len : size_nat -> 
    pointBuffer : point -> 
    output: lbuffer uint8 len-> 
    clen:size_t{v clen = len /\ len >= 96} ->  
    counter: bignumCounter -> 
    curveOrder: word -> 
    curveOrderCounter: bignumCounter{bignumCounterLess counter curveOrderCounter == true /\ (
    	let h = uint_v curveOrderCounter.high in let l = uint_v curveOrderCounter.low in 
		(pow2 128 * h + l) < pow2 256 - 1)} -> 
    cofactor_check_buffer: lbuffer uint128 40 -> 
    Stack bool
        (requires (fun h0 -> live h0 pointBuffer /\ live h0 output /\ live h0 cofactor_check_buffer /\ live h0 curveOrder /\ disjoint cofactor_check_buffer pointBuffer))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1)) 

let rec _helper_ECVRF_hash_to_curve #len pointBuffer output clen counter curveOrder curveOrderCounter cofactor_check_buffer = 
	let inputLength = Spec.Lib.IntTypes.sub #SIZE clen (size 96) in 
	let startBufferForCounter = add #SIZE inputLength (size 32) in 
	let lengthBufferToInputHash = add #SIZE inputLength (size 64) in

	let bufferForInputHash = sub output (size 0) lengthBufferToInputHash in 
	let bufferForComputedHash = sub output lengthBufferToInputHash (size 32) in 
	let placeForCounterHigh = sub output startBufferForCounter (size 16)   in
	let placeForCounterLow = sub output (add #SIZE startBufferForCounter (size 16)) (size 16) in  

	toU8 placeForCounterHigh counter.high;
	toU8 placeForCounterLow counter.low;

	hash bufferForComputedHash lengthBufferToInputHash bufferForInputHash; 

  	let successful = decompress pointBuffer bufferForComputedHash in 
  	if successful then 
  		let buffer_point = sub cofactor_check_buffer (size 20) (size 20) in 
  		disjoint_sub_lemma1 cofactor_check_buffer pointBuffer (size 20) (size 20);
  		point_mult buffer_point pointBuffer curveOrder;
  		let buffer_point_infinity = sub cofactor_check_buffer (size 0) (size 20) in 
  		let r = pointCompare buffer_point buffer_point_infinity in 
  		if r then 
  			true
  		else 
  			begin
  	  		let counterUpd = bignumCounterInc counter in 
  			let rc = bignumCounterLess counterUpd curveOrderCounter in 
  			if rc = false then false else 
  				_helper_ECVRF_hash_to_curve #len pointBuffer output clen counterUpd curveOrder curveOrderCounter cofactor_check_buffer 
  			end	
  	else 
  		begin
  	  	let counterUpd = bignumCounterInc counter in 
  		let rc = bignumCounterLess counterUpd curveOrderCounter in 
  		if rc = false then false else 
  			_helper_ECVRF_hash_to_curve #len pointBuffer output clen counterUpd curveOrder curveOrderCounter cofactor_check_buffer
  	end

(*TODO: add the function checking whether curveOrder as word is the same as CurveOrderCounteryyy *)

val _ECVRF_hash_to_curve:
	#len:size_nat ->
	pointBuffer : point ->
	publicKey: point{disjoint pointBuffer publicKey}->
	clen:size_t{v clen == len /\ len < maxint SIZE - 96} ->
	input:lbuffer uint8 len ->
	curveOrder: word -> 
    curveOrderCounter: bignumCounter{let h = uint_v curveOrderCounter.high in let l = uint_v curveOrderCounter.low in (
    	(pow2 128 * h + l) < pow2 256 - 1 && (pow2 128 * h + l > 0))} -> 
    cofactor_check_buffer: lbuffer uint128 40 ->
	Stack bool 
		(requires
			(fun h0 -> live h0 pointBuffer /\ live h0 input /\ live h0 publicKey /\ live h0 cofactor_check_buffer /\ live h0 curveOrder /\ disjoint cofactor_check_buffer pointBuffer)
		)
		(ensures
			(fun h0 _ h1 -> preserves_live h0 h1)
		)

let _ECVRF_hash_to_curve #len pointBuffer publicKey clen input curveOrder curveOrderCounter cofactor_check_buffer  = 
	let sizeToHashBuffer = add #SIZE clen (size 96) in 
	let sizeInput = add #SIZE clen (size 32) in 
	alloc #(uint8) #(bool) #(v sizeToHashBuffer) sizeToHashBuffer (u8(0)) 
		[BufItem publicKey; BufItem input; BufItem curveOrder;] [BufItem pointBuffer; BufItem cofactor_check_buffer] 
		(fun h0 _ h1 -> True) (
			fun toHashBuffer ->  	
				let inputBuffer = sub toHashBuffer (size 0) clen in 
				copy #_ #(v clen) clen input inputBuffer;
	    		let compressedPublicKey = sub #_ #(v sizeToHashBuffer) #(32) toHashBuffer clen (size 32) in 
				compress compressedPublicKey publicKey;
				let counterStart = C (u128 0) (u128 0) in 
					assume (disjoint cofactor_check_buffer pointBuffer);	
					assume (bignumCounterLess counterStart curveOrderCounter = true);
				let r =  _helper_ECVRF_hash_to_curve pointBuffer toHashBuffer sizeToHashBuffer counterStart curveOrder curveOrderCounter cofactor_check_buffer in
				admit(); 
				r
		)
