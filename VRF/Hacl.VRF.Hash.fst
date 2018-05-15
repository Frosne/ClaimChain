module Hacl.VRF.Hash

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


(* Secret buffer consists of private key of the user and the random value *)
(* Input - the array to be hashed *)
(* pk - public key of the user *)

val _ECVRF_prove_2: proof: lbuffer uint8 80 -> secret: doubleWord -> Stack bool
	(requires(fun h0 -> live h0 proof /\ live h0 secret /\ disjoint proof secret))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 proof h0 h1))

let _ECVRF_prove_2 proof secret = 
	alloc #_ #(bool) #(30) (size 30) (u64(0))
		[BufItem secret; BufItem proof] [BufItem proof]
		(fun h0 _ h1 -> True)
		(fun bigNums -> 
			let cf = sub #_ #(30) #(5) bigNums (size 0) (size 5) in 
			let xf = sub #_ #(30) #(5) bigNums (size 5) (size 5) in 
			let cxf = sub #_ #(30) #(5) bigNums (size 10) (size 5) in 
			let kf = sub #_ #(30) #(5) bigNums (size 15) (size 5) in 

			let c = sub #_ #(80) #(32) proof (size 32) (size 32) in 
			let s = sub #_ #(80) #(32) proof (size 48) (size 32) in 

			let clow = sub #_ #(80) #(16) proof (size 48) (size 16) in 
			let chigh = sub #_ #(80) #(16) proof (size 32) (size 16) in 

			let privateKey = sub #_ #(64) #(32) secret (size 0) (size 32) in 
			let random = sub #_ #(64) #(32) secret (size 32) (size 32) in 
				
			fexpand cf c;
				disjoint_sub_lemma2 bigNums (size 0) (size 5) (size 5) (size 5);
				disjoint_sub_lemma2 bigNums (size 0) (size 5) (size 15) (size 5);
				disjoint_sub_lemma2 bigNums (size 5) (size 5) (size 15) (size 5);
				disjoint_sub_lemma2 bigNums (size 10) (size 5) (size 15) (size 5);
			fexpand xf privateKey;
			fexpand kf random; 
				let h0 = ST.get() in 
				lemma_red_513_is_red_53 (as_lseq cf h0);
				lemma_red_513_is_red_5413 (as_lseq xf h0);
			fmul cxf cf xf; 
				let h3 = ST.get() in 
				disjoint_sub_lemma2 bigNums (size 15) (size 5) (size 10) (size 5);
			fdifference_reduced kf cxf; 
			copy (size 16) clow chigh;	
			fcontract s kf;
			true
		)


val _ECVRF_prove: 
	#len : size_nat -> 
	proof: lbuffer uint8 80 -> 
	inputLength: size_t{v inputLength == len /\ len < maxint SIZE - 96} -> 
	input: lbuffer uint8 len -> 
	secret: doubleWord ->
	pk: point  -> 
	Stack bool 
		(requires (fun h0 -> live h0 proof /\ live h0 input /\ live h0 secret /\ live h0 pk /\ disjoint proof secret))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 proof h0 h1))

let _ECVRF_prove #len proof inputLength input secret pk = 
	let r = alloc #_ #(bool) (size 120) (u64(0)) 
		[BufItem input; BufItem secret; BufItem pk] [BufItem proof] 
		(fun h0 _ h1 -> True) 
		(fun pointBuffer ->
			let c = sub proof (size 32) (size 32) in 

			let privateKey = sub #_ #(64) #(32) secret (size 0) (size 32) in 
			let random = sub #_ #(64) #(32) secret (size 32) (size 32) in 

			let generator = sub pointBuffer (size 0) (size 20) in 
			make_g generator;
			let h = sub #_ #(120) #(20) pointBuffer (size 20) (size 20) in
				disjoint_sub_lemma1 pointBuffer pk (size 20) (size 20);
			let r = _ECVRF_hash_to_curve h pk inputLength input in 
			if not r then begin
				false
			end
			else begin

				let publicKey =  sub #_ #(120) #(20) pointBuffer (size 40) (size 20) in
				copy (size 20) pk publicKey;
				let gammaPoint = sub #_ #(120) #(20) pointBuffer (size 60) (size 20) in
					point_mult gammaPoint h privateKey;
				let gk = sub #_ #(120) #(20) pointBuffer (size 80) (size 20) in
					point_mult gk generator random;
				let hk = sub #_ #(120) #(20) pointBuffer (size 100) (size 20) in
					point_mult hk h random;

				disjoint_sub_lemma1 proof pointBuffer (size 32) (size 32);	

				 _ECVRF_hashPoints c pointBuffer;
				true
			end
		) 
	in 
		if  not r then false else  
			_ECVRF_prove_2 proof secret











