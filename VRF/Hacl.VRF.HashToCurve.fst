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

noeq type uint256 = 
	|C: high: uint_t U128 -> low: uint_t U128 -> uint256

val v_counter: c: uint256 -> GTot nat 
let v_counter c = 
	let high = uint_v c.high in 
	let low = uint_v c.low in 
	pow2 128 * high + low

assume val inc_: c: uint256{v_counter c < pow2 256 - 1} -> Tot (r: uint256{v_counter r = v_counter c + 1 })

assume val less: a: uint256 -> b: uint256 -> Tot bool

val _helper_ECVRF_hash_to_curve: 
	#len : size_nat -> 
    pointBuffer : point -> 
    output: lbuffer uint8 len-> (* length output = v inputLength + 96 *)
    clen:size_t{v clen = len /\ len >= 96} ->  
    highCounter: uint128 -> 
    lowCounter: uint128 -> 
    Stack bool
        (requires (fun h0 -> live h0 pointBuffer /\live h0 output))
   		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 output pointBuffer h0 h1 ))

assume val greater: highCounter: uint128 -> lowCounter: uint128 -> highValue: uint128 -> lowValue: uint128 -> Tot bool

(*let greater hc lc hv lv = 
	if (highCounter > highValue) then true 
	else if (highCounter < highValue) then false 
	else
		begin
			if (lowCounter > lowValue) then true else false 
		end	
*)
assume val inc: highCounter : uint128 -> lowCounter: uint128 -> Tot (tuple2 uint128 uint128)	 	

let rec _helper_ECVRF_hash_to_curve #len pointBuffer output clen highCounter lowCounter  =
	let inputLength = Spec.Lib.IntTypes.sub #SIZE clen (size 96) in 

	let startBufferForCounter = add #SIZE inputLength (size 32) in 
	let lengthBufferToInputHash = add #SIZE inputLength (size 64) in 

	let bufferForInputHash = sub output (size 0) lengthBufferToInputHash in 
	let bufferForComputedHash = sub output lengthBufferToInputHash (size 32) in 
		
	let placeForCounterHigh = sub output startBufferForCounter (size 16)   in
	let placeForCounterLow = sub output (add #SIZE startBufferForCounter (size 16)) (size 16) in  

	toU8 placeForCounterHigh highCounter;
	toU8 placeForCounterLow lowCounter;

	hash bufferForComputedHash lengthBufferToInputHash bufferForInputHash;  

  	let successful = decompress pointBuffer bufferForComputedHash in 
  	if successful then true
  	else
  	( 
  		(*Example *)
  		let curveOrderHigh = u128 10 in 
  		let curveOrderLow = u128 10 in 
  		(*/Example *)

  		if greater highCounter lowCounter curveOrderHigh curveOrderLow then false else
  		let counterIncH, counterIncL = inc highCounter lowCounter in 
  			_helper_ECVRF_hash_to_curve #len pointBuffer output clen highCounter lowCounter
  )

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
	assert(uint_v sizeToHashBuffer >= 96);
	let sizeInput = add #SIZE clen (size 32) in 
	alloc #(uint8) #(bool) #(v sizeToHashBuffer) sizeToHashBuffer (u8(0)) 
		[BufItem publicKey; BufItem input] [BufItem pointBuffer] 
		(fun h0 _ h1 -> True) (
			fun toHashBuffer ->  	
					let inputBuffer = sub toHashBuffer (size 0) clen in 
				copy #_ #(v clen) clen input inputBuffer;

	    		let compressedPublicKey = sub #_ #(v sizeToHashBuffer) #(32) toHashBuffer clen (size 32) in 
				compress compressedPublicKey publicKey;
				 _helper_ECVRF_hash_to_curve pointBuffer toHashBuffer sizeToHashBuffer (u128 0) (u128 0)
 	)
