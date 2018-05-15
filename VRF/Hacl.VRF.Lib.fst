module Hacl.VRF.Lib

open FStar.Mul

open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib
open Spec.Lib.IntSeq

open Spec.Lib.IntTypes
open Spec.Lib.IntBuf

open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.IntBuf.Lemmas

type limb = uint64
type word = lbuffer uint8 (32)
type doubleWord = lbuffer uint8 (64)
type scalar = lbuffer uint8 (8)
type felem = lbuffer limb 5
type point = lbuffer limb 20

assume val point_mult: out: point ->p: point ->  
	scalar: word -> 
	Stack unit 
		(requires (fun h0 -> live h0 out /\ live h0 p /\ live h0 scalar /\ disjoint out p))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1 ))

assume val point_add: out: point ->p: point ->  
	q: point -> 
	Stack unit 
		(requires (fun h0 -> live h0 out /\ live h0 p /\ live h0 q /\ 
			disjoint out p /\ disjoint out q))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1 ))


assume val point_double: out: point -> p: point ->  
	Stack unit 
		(requires (fun h0 -> live h0 out /\ live h0 p /\ disjoint out p))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1 ))

assume val hash: 
	hashBuffer: lbuffer uint8 32 ->
	inputLength: size_t -> 
	input: lbuffer uint8 (v inputLength) -> 
	Stack unit
	(requires (fun h -> live h hashBuffer /\ live h input /\ disjoint hashBuffer input))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 hashBuffer h0 h1))

assume val compress: 
	out: lbuffer uint8 32 -> 
	input: lbuffer limb 20 -> 
	Stack unit 
		(requires (fun h -> live h out /\ live h input))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))

assume val decompress: 
	out: point -> 
	input: lbuffer uint8 32 -> 
	Stack bool 
		(requires (fun h -> live h out /\ live h input))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 out h0 h1))


let seqelem = lseq limb 5

let getx (p:point) : Tot felem = sub p (size 0) (size 5)
let gety (p:point) : Tot felem = sub p (size 5) (size 5)
let getz (p:point) : Tot felem = sub p (size 10) (size 5)
let gett (p:point) : Tot felem = sub p (size 15) (size 5)

assume val red_513: seqelem -> GTot Type0
assume val red_53: seqelem -> GTot Type0
assume val red_5413: seqelem -> GTot Type0

let point_inv h (p:point) : GTot Type0 =
  	live h p /\ 
  		(let x = getx p in let y = gety p in let z = getz p in let t = gett p in
  			red_513 (as_lseq x h) /\ 
  			red_513 (as_lseq y h) /\ 
  			red_513 (as_lseq z h) /\ 
  			red_513 (as_lseq t h))


assume val make_g:
  g:point ->
  Stack unit
    (requires (fun h -> live h g))
    (ensures (fun h0 _ h1 -> live h1 g /\ modifies1 g h0 h1 /\ point_inv h1 g /\ preserves_live h0 h1)) 


assume val fexpand: output:felem -> input:lbuffer uint8 32 -> Stack unit
  (requires (fun h -> live h output /\ live h input))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1 /\ red_513 (as_lseq output h1)))

assume val lemma_red_513_is_red_53: s:seqelem -> Lemma (requires (red_513 s)) (ensures (red_53 s))
assume val lemma_red_513_is_red_5413: s:seqelem -> Lemma (requires (red_513 s)) (ensures (red_5413 s))

assume val fdifference_reduced:
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun h ->  live h a /\ live h b /\ red_513 (as_lseq a h) /\ red_513 (as_lseq b h)))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 a h0 h1 /\ red_513 (as_lseq a h1)))

assume val fcontract: output: lbuffer uint8 32 -> input:felem -> Stack unit
  (requires (fun h -> live h output /\ live h input /\ red_513 (as_lseq input h)))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 output input h0 h1))

assume val fmul:
  out:felem ->
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ live h b /\ red_53 (as_lseq a h) /\ red_5413 (as_lseq b h)))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ red_513 (as_lseq out h1) /\ modifies1 out h0 h1)) 

assume val modifies_2_modifies_2 : #a1: Type0 -> #a2: Type0 -> #len1: size_nat -> #len2: size_nat -> 
	b1 : lbuffer a1 len1 -> b2: lbuffer a2 len2 -> 
	h0 : mem -> h1: mem -> 	Lemma
	(requires (modifies2 b1 b2 h0 h1))
	(ensures (modifies2 b2 b1 h0 h1))		  	  
	[SMTPat (modifies2 b1 b2 h0 h1);
	SMTPat (live h0 b1);
	SMTPat (live h0 b2)
	]

assume val modifies2_sub_lemma: #a:Type0 ->  #a2:Type0 -> #len:size_nat ->  #len2:size_nat ->  b:lbuffer a len ->b2:lbuffer a2 len2 ->  start:size_t -> n:size_t{v start+v n <= len} ->
		 start2:size_t -> n2:size_t{v start2+v n2 <= len2} ->
 			h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b /\live h0 b2 /\ modifies2 (sub #a #len #(v n) b start n)  (sub #a2 #len2 #(v n2) b2 start2 n2) h0 h1))
			 (ensures  (modifies2 b b2 h0 h1 /\ modifies2 b2 b h0 h1))
			 [SMTPat (live h0 b);
			  SMTPat (live h0 b2);
			  SMTPat (modifies2 (sub #a #len #(v n) b start n) (sub #a2 #len2 #(v n2) b2 start2 n2)   h0 h1)]			  

assume val modifies3_sub_lemma: #a:Type0 ->
	#len:size_nat -> 
	b:lbuffer a len ->
	start:size_t -> n:size_t{v start+v n <= len} ->
	start2:size_t -> n2:size_t{v start2+v n2 <= len} ->
	start3:size_t -> n3:size_t{v start3+v n3 <= len} ->
 	h0:mem -> h1:mem -> Lemma
	(requires (live h0 b/\ 
	modifies3 (sub #a #len #(v n) b start n)  
		(sub #a #len #(v n2) b start2 n2)
		(sub #a #len #(v n3) b start3 n3) h0 h1
	))
	(ensures  (modifies1 b h0 h1))
	[SMTPat (live h0 b);
	SMTPat (modifies3 
		(sub #a #len #(v n) b start n) 
		(sub #a #len #(v n2) b start2 n2)  
		(sub #a #len #(v n3) b start3 n3)   h0 h1)]			  






assume val modifies_0_modifies_3: #a1:Type0 -> #a2:Type0  -> #a3:Type0 -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> 
	b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ modifies0 h0 h1 /\ live h0 b3))
			 (ensures (modifies3 b1 b2 b3 h0 h1 /\ modifies3 b3 b2 b1 h0 h1 /\ modifies3 b1 b3 b2 h0 h1 /\ modifies3 b2 b1 b3 h0 h1 /\ modifies3 b2 b3 b1 h0 h1 /\
			 		modifies3 b3 b1 b2 h0 h1))
			 [SMTPat (modifies0 h0 h1);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2);
			  SMTPat (live h0 b3)
			  ]

assume val modifies_3_modifies_3: #a1:Type0 -> #a2:Type0  -> #a3:Type0 -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> 
	b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ modifies3 b1 b2 b3 h0 h1 /\ live h0 b3))
			 (ensures (modifies3 b3 b1 b2 h0 h1))
			 [SMTPat (modifies3 b1 b2 b3 h0 h1);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2);
			  SMTPat (live h0 b3)
			  ]		

assume val equalBuffer: #a: Type0 -> #len:size_nat ->
	b1: lbuffer a len -> b2: lbuffer a len -> Stack bool
	(requires (fun h0  -> live h0 b1 /\ live h0 b2))
	(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))