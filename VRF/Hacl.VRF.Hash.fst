module Hacl.VRF.Hash

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntSeq

open Spec.Lib.IntTypes
open Spec.Lib.IntBuf

open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.IntBuf.Lemmas

open Hacl.VRF.HashToCurve
open Hacl.VRF.HashPoints
open Hacl.VRF.Bignum

open Hacl.VRF.Lib

(*
let g_x : elem = 15112221349535400772501151409588531511454012693041857206046113283949847762202
let g_y : elem = 46316835694926478169428394003475163141307993866256225615783033603165251855960
*)

(*
corresponds to edd25519 method make_g
*)


(* Secret buffer consists of private key of the user and the random value *)
(* Input - the array to be hashed *)
(* pk - public key of the user *)

val _ECVRF_prove: 
	#len : size_nat -> 
	proof: lbuffer uint8 80 -> 
	inputLength: size_t{v inputLength == len } -> 
	input: lbuffer uint8 len -> 
	secret: doubleWord ->
	pk: point  -> 
	Stack bool 
		(requires 
			(fun h0 -> live h0 proof /\ live h0 input /\ live h0 secret /\ live h0 pk 
			)
		)
		(ensures 
			(
				fun h0 _ h1 -> preserves_live h0 h1
			) 
		)

let _ECVRF_prove #len proof inputLength input secret pk = 
	let r = alloc #_ #(bool) (size 120) (u128(0)) 
		[BufItem input; BufItem secret; BufItem pk] [BufItem proof] 
		(fun h0 _ h1 -> True) 
		(fun pointBuffer ->

			let c = sub proof (size 32) (size 32) in 

			let privateKey = sub #_ #(64) #(32) secret (size 0) (size 32) in 
			let random = sub #_ #(64) #(32) secret (size 32) (size 32) in 

			let generator = sub pointBuffer (size 0) (size 20) in 
				generatorLoad generator;
			let h = sub #_ #(120) #(20) pointBuffer (size 20) (size 20) in
				let r = _ECVRF_hash_to_curve h pk inputLength input in 
				if not r then false else 
			(let publicKey =  sub #_ #(120) #(20) pointBuffer (size 40) (size 20) in
				copy (size 20) publicKey pk;
			let gammaPoint = sub #_ #(120) #(20) pointBuffer (size 60) (size 20) in
				point_mult gammaPoint h privateKey;
			let gk = sub #_ #(120) #(20) pointBuffer (size 80) (size 20) in
				point_mult gk generator random;
			let hk = sub #_ #(120) #(20) pointBuffer (size 100) (size 20) in
				point_mult hk h random;
			 _ECVRF_hashPoints c pointBuffer;
			true)

		) 
	in 
		(
			if  not r then false else  
				(
					alloc #_ #(bool) #(30) (size 30) (u64(0))
					[BufItem secret; BufItem proof] [BufItem proof]
					(fun h0 _ h1 -> True)
					(fun bigNums -> 

					let cf = sub #_ #(30) #(5) bigNums (size 0) (size 5) in 
					let xf = sub #_ #(30) #(5) bigNums (size 5) (size 5) in 
					let cxf = sub #_ #(30) #(5) bigNums (size 10) (size 5) in 
					let kf = sub #_ #(30) #(5) bigNums (size 15) (size 5) in 
					(*let k_cxf = sub #_ #(30) #(5) bigNums (size 20) (size 5) in 
					let resultf = sub #_ #(30) #(5) bigNums (size 25) (size 5) in *)

					let c = sub #_ #(80) #(32) proof (size 32) (size 32) in 
					let s = sub #_ #(80) #(32) proof (size 48) (size 32) in 

					let privateKey = sub #_ #(64) #(32) secret (size 0) (size 32) in 
					let random = sub #_ #(64) #(32) secret (size 32) (size 32) in 

					fexpand cf c; 
					fexpand xf privateKey;
					fexpand kf random; (* kf = random *)

					fmul cxf cf xf; (*cxf = c * x *)
					fdifference_reduced kf cxf; (* kf = kf - cxf *)

					let clow = sub #_ #(80) #(16) proof (size 48) (size 16) in 
					let chigh = sub #_ #(80) #(16) proof (size 32) (size 16) in 
					copy (size 16) clow chigh;

					fcontract s kf;
 
					true
					)
				)
			)

(*)
val decodeProof: gamma: point -> 
			c: scalar -> s: scalar -> 
			proof: lbuffer uint8 (v(size 80)) -> 
			Stack bool 
		(requires  (fun h0 -> live h0 proof))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1))

let decodeProof gamma c s proof = 
	let gamma' = sub proof (size 0) (size 32) in 
	let c' = sub proof (size 32) (size 32) in 
	let s' = sub proof (size 48) (size 32) in 
	let valid = decompress gamma gamma' in 
	if not valid then false else
	toBn c c';
	toBn s s'; 
	true

val proofToHash:
			beta: lbuffer uint8 (v size_hash) ->
			gamma: point -> 
			c: scalar -> s: scalar -> 
			proof: lbuffer uint8 (v(size 80)) -> 	
			Stacl bool
		(requires  (fun h0 -> live h0 proof /\ live h0 gamma /\ live h0 beta))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1))
			
let proofToHash gamma proof = 
	let r = decodeProof gamma c s proof in 
	if not r then false else
	let gamma' = sub proof (size 0) (size 32) in 
	hash beta (size 32) gamma';
	true


val _ECVRF_verify:
		points: lbuffer uint128 (v(size 160)) -> 
		proof: lbuffer uint8 (v(size 80)) -> 
		inputLength: size_t{v inputLength == len /\ uint_v inputLength < maxint SIZE - 97} -> 
		input: lbuffer uint8 len -> 
		Stack bool
			(requires  (fun h0 -> live h0 proof /\ live h0 gamma /\ live h0 beta))
			(ensures (fun h0 _ h1 -> preserves_live h0 h1))
		
let _ECVRF_verify pk proof inputLength input = 
	let r = alloc #_ #(bool) (size 128) (u8(0)) 
		[BufItem pk; BufItem proof; BufItem input] [] 
		(fun h0 _ h1 -> True) 
		(fun scalars ->
	let pk = sub points (size 0) (size 20) in 
	let yc = sub points (size 20) (size 20) in 
	let g = sub points (size 40) (size 20) in 
	let gs = sub points (size 60) (size 20) in 
	let u = sub points (size 80) (size 20) in 
	let gammac = sub points (size 100) (size 20) in 
	let hs = sub points (size 120) (size 20) in 
	let gamma = sub points (size 140) (size 20) in 		

	let c = sub scalars (size 0) (size 32) in
	let s = sub scalars (size 32) (size 32) in 
	let h = sub scalars (size 64) (size 32) in 
	let c_new = sub scalars(size 96) (size 32) in 
	let c_small = sub c (size 0) (size 16) in 
	let d = decodeProof gamma c_small s proof in 
	if not d then false else
	point_mult yc y c;
	make_g g;
	point_mult gs g s;
	point_add u yc gs;
	let r = _ECVRF_hash_to_curve h pk input in 
	if not r then false else 
	point_mult gammac gamma c;
	point_mult hs h s;
	point_add v gammac hs;
	_ECVRF_hashPoints c_new h pk gamma u v;
	c==c_new


















