module Spec.VRF

open FStar.UInt32
open FStar.UInt8
open FStar.Seq
open FStar.Option

open FStar.Mul
open FStar.Seq
open FStar.UInt

open FStar.Endianness
open Spec.Curve25519
open Spec.Ed25519

open Spec.SHA2_256


#reset-options "--max_fuel 0 --z3rlimit 100"

let bytes =  seq FStar.UInt8.t
let key = lbytes 32
let field = prime

let n = 16


let d : elem = 37095705934669439343138083508754565189542113879843219016388785533085940283555
type twisted_edward_point = ext_point

let g_x : elem = 15112221349535400772501151409588531511454012693041857206046113283949847762202
let g_y : elem = 46316835694926478169428394003475163141307993866256225615783033603165251855960


let cardinality = 57896044618658097711785492504343953926856930875039260848015607506283634007912

let generator: twisted_edward_point = (g_x, g_y, 1, g_x `fmul` g_y)

val pointMultiplication : point : twisted_edward_point -> k: bytes -> Tot twisted_edward_point
let pointMultiplication point k = 
	Spec.Ed25519.point_mul k point

val scalarAddition : p : twisted_edward_point -> q: twisted_edward_point -> Tot twisted_edward_point
let scalarAddition p q = 
	Spec.Ed25519.point_add p q 

val isPointOnCurve: point : option twisted_edward_point -> Tot bool
let isPointOnCurve point =
	if isNone point then false else
	let point = get point in 
	let px, py, pz, pt = point in 
	let x2 = fmul px px in 
	let y2 = fmul py py in 
	let left = fsub x2 y2 in 
	let z2 = fmul pz pz in 
	let t2 = fmul pt pt in 
	let dt2 = fmul d t2 in 
	let right = fadd z2 dt2 in 
	(left = right)

val _ECP2OS : gamma: twisted_edward_point -> Tot(r: bytes {Seq.length r = 32})
let _ECP2OS gamma = point_compress gamma

val _OS2ECP : point: bytes{Seq.length point = 32} -> Tot(option twisted_edward_point)
let _OS2ECP point = point_decompress point

val nat_to_uint8: x: int {x < 256} -> Tot(FStar.UInt8.t)
let nat_to_uint8 x = FStar.UInt8.uint_to_t (to_uint_t 8 x)

val uint8_to_int : x: FStar.UInt8.t -> Tot(int)
let uint8_to_int x = FStar.UInt8.v x

val _helper_I2OSP: value: nat -> s: bytes -> counter : nat {counter < Seq.length s} -> 
		Tot (r: bytes {Seq.length r = Seq.length s})
		(decreases (counter))
let rec _helper_I2OSP value s counter  = 
	let mask = 256 in 
	let r = value % mask in 
	let r = nat_to_uint8 r in 
	let s = upd s counter r in 
	let number = value / mask  in 
		if (counter -1 >=0 ) then 
			_helper_I2OSP number s (counter -1 )
	else s

val _I2OSP: value: nat -> n: int{n > 0} -> Tot(r: bytes{Seq.length r = n})
let _I2OSP value n = 
	if (pow2 (n * 8)  <= value) then Seq.create n 0uy (* changed*)
	else 
		let s = Seq.create n 0uy in 
	(_helper_I2OSP value s (n -1))

val _helper_OS2IP: s: bytes  -> counter: nat {counter < Seq.length s} -> number: nat -> Tot (nat)(decreases (Seq.length s - counter))

let rec _helper_OS2IP s counter number = 
	let temp = Seq.index s counter in 
	let temp = uint8_to_int temp in 
	let counter_mult = pow2 (8 * (Seq.length s - counter -1 )) in 
	let number = number + (op_Multiply counter_mult temp) in 
	if (counter +1 < Seq.length s) then  
		_helper_OS2IP s (counter +1 ) number
	else 
		number	

val _OS2IP: s: bytes{Seq.length s > 0} -> nat
let _OS2IP s = 
	_helper_OS2IP s 0 0

val seqConcat : s1: seq 'a -> s2: seq 'a -> 
			Tot(r:seq 'a{Seq.length	r = Seq.length s1 + Seq.length s2})

let seqConcat s1 s2 = 
	FStar.Seq.append s1 s2 	

val hash: input: bytes{Seq.length input < Spec.SHA2_256.max_input_len_8} -> 
		Tot(r: bytes{Seq.length r = Spec.SHA2_256.size_hash})	
let hash input = 
	Spec.SHA2_256.hash input




val _ECVRF_decode_proof: 
		pi: bytes {Seq.length pi = op_Multiply 5 n} -> 
		Tot(
				tuple3 (option twisted_edward_point)
		 		(c:bytes{Seq.length c = n})
		 		(s:bytes {Seq.length s = (op_Multiply 2 n)})
			)

let _ECVRF_decode_proof pi = 
	let gamma, cs = Seq.split pi (op_Multiply 2 n) in 
		assert(Seq.length cs =(op_Multiply 3 n));
	let c, s = Seq.split cs n in 
		assert(Seq.length s = (op_Multiply 2 n));
	let point = _OS2ECP gamma in 
	(point, c, s)


val _helper_ECVRF_hash_to_curve : 
	ctr : nat{ctr < field} ->counter_length:nat{counter_length > 0} ->  
	pk: bytes{Seq.length pk = 32} ->
	input: bytes{Seq.length input < Spec.SHA2_256.max_input_len_8 - 32 - counter_length } ->
	Tot(r: option twisted_edward_point) 
	(decreases(field - ctr)) 

let rec _helper_ECVRF_hash_to_curve ctr counter_length pk input = 
	let _CTR = _I2OSP ctr counter_length in 
	let toHash = seqConcat input pk in 
	let toHash = seqConcat toHash _CTR in 
	let hash = hash toHash in
	let possible_point = point_decompress hash in 
	if isNone possible_point then 
		(
			if (ctr + 1) < field then 
					(_helper_ECVRF_hash_to_curve (ctr+1) counter_length pk input) else
			None
		)
		else 
			possible_point				

val _ECVRF_hash_to_curve: input: bytes{Seq.length input < Spec.SHA2_256.max_input_len_8 - 36 } -> 
			public_key: (twisted_edward_point) -> Tot(option twisted_edward_point)			

let _ECVRF_hash_to_curve input public_key = 
	let ctr = 0 in 
	let pk = _ECP2OS public_key in 
	let point = _helper_ECVRF_hash_to_curve ctr 4 pk input in point

val _ECVRF_hash_points : generator: twisted_edward_point -> h:  twisted_edward_point -> 
			public_key: twisted_edward_point -> gamma : twisted_edward_point -> 
			gk : twisted_edward_point -> hk : twisted_edward_point -> 
			Tot(nat)

let _ECVRF_hash_points generator h public_key gamma gk hk = 
	let p = _ECP2OS generator in (*32 *)
	let p = seqConcat p (_ECP2OS h) in (* 64  *)
	let p = seqConcat p (_ECP2OS public_key) (* 32*3 *) in 
	let p = seqConcat p (_ECP2OS gamma)  (* still less than 2pow 61 *)in 
	let p = seqConcat p (_ECP2OS gk) in 
	let p = seqConcat p (_ECP2OS hk) in 
	let h' = hash p in 
	let h = fst (FStar.Seq.split h' n) in 
	_OS2IP h

val little_endian_ins:	a: bytes -> 
			counter: nat {counter < Seq.length a} -> 
			b: bytes{Seq.length a = Seq.length b}-> 
			Tot (r: bytes{Seq.length a = Seq.length r})
			(decreases(Seq.length a - counter))

let rec little_endian_ins a counter b = 
	let element = Seq.index a counter in 
	let newSeq = Seq.upd b (Seq.length a -1 - counter) element in 
	if (counter+1 < Seq.length a) then 
		little_endian_ins a (counter+1) newSeq
	else 
		newSeq	

val little_endian_: a: bytes{Seq.length a > 0} -> Tot (r: bytes {Seq.length a = Seq.length r})
let little_endian_ a = 
	let s = Seq.create (Seq.length a) 0uy in 
	little_endian_ins a 0 s

val _ECVRF_prove: input: bytes {Seq.length input < Spec.SHA2_256.max_input_len_8 - 36 } ->  
			public_key: twisted_edward_point -> 
			private_key : bytes{Seq.length private_key > 0} ->
			Tot(proof: option bytes {Some?proof ==> Seq.length (Some?.v proof) = op_Multiply 5 n})

let _ECVRF_prove input public_key private_key = 
	let h = _ECVRF_hash_to_curve input public_key in 
		if isNone h then None (* trying to convert the hash to point, if it was not possible returns None *)
		else 
			let h = get h in 		
		let private_keyLE = little_endian_ private_key in 		
	let gamma = pointMultiplication h private_keyLE in 
	let k_ = random cardinality in 
	let k =  _I2OSP k_ 32 in 
	let kLE = little_endian_ k in 
		let gk = pointMultiplication generator kLE in  
		let hk = pointMultiplication h kLE in 
	let c = _ECVRF_hash_points generator h public_key gamma gk hk in 
			let cPrivateKey = op_Multiply c (_OS2IP private_key) in  
			let cPrivateKeyModQ = cPrivateKey % cardinality in 
	let k_  = k_ + cardinality in 
	let s = k_ - cPrivateKeyModQ in 
	let s = s % cardinality in 
			let fst = _ECP2OS gamma in 
			let snd = _I2OSP c n in (* Seq length snd = n*)
			let thd = _I2OSP s (op_Multiply 2 n) (* Seq.length thr = 2n *) in 
	let pi = seqConcat fst (seqConcat snd thd) in Some pi

val _ECVRF_proof2hash: pi: bytes{Seq.length pi = op_Multiply 5 n } -> Tot(hash: bytes{Seq.length hash = n})

let _ECVRF_proof2hash pi = 
	let right_part = snd( Seq.split pi (op_Multiply 2 n)) in 
	fst (Seq.split right_part n)

val _ECVRF_verify :
		public_key : twisted_edward_point ->
		proof: bytes {Seq.length proof = op_Multiply 5 n } -> 
		input : bytes{Seq.length input < Spec.SHA2_256.max_input_len_8 - 36 } -> 
		Tot(bool)

let _ECVRF_verify public_key proof input = 
	let gamma, c, s = _ECVRF_decode_proof proof in 
	if isNone gamma then false
		else let gamma = get gamma in 
	let cLE = little_endian_ c in 
	let sLE = little_endian_ s in 	
	let yc = pointMultiplication public_key cLE in 
	let gs = pointMultiplication generator sLE in 
	let u  = scalarAddition yc gs in 
	let h = _ECVRF_hash_to_curve input public_key in 
		if isNone h then false
	else 
	let h = get h in 
	let gammac = pointMultiplication gamma cLE in 
	let hs = pointMultiplication h sLE in 
	let v = scalarAddition gammac hs in 
	let c_prime = _ECVRF_hash_points generator h public_key gamma u v in 
	(_OS2IP c) = c_prime
