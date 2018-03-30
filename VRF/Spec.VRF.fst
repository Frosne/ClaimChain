module Spec.VRF

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

open Spec.Curve25519
open Spec.Ed25519
open Spec.SHA2
open FStar.Option

#reset-options "--max_fuel 0 --z3rlimit 100"

let n = 16

let _OS2ECP (s:lbytes 32) : Tot (option ext_point) =
	point_decompress s

let _ECP2OS (p:ext_point) : Tot (lbytes 32) = 
	point_compress p

let _I2OSP (value: nat{value < pow2 256}) : Tot (lbytes 32) = 
	nat_to_bytes_le 32 value	

let _OS2IP (s: lbytes 32) : Tot (elem) = 
	let n = nat_from_bytes_le #32 s in 
	n % prime

let _OS2IP_16 (s: lbytes 16) : Tot (elem) = 
	let n = nat_from_bytes_le #16 s in 
	n % prime

let maxHash = (maxint(U64) + 1)/8

let hash (len:size_nat{len < maxHash}) (input:lbytes len)  = 
	hash256	len input

let curveOrder : elem = 7237005577332262213973186563042994240857116359379907606001950938285454250989	

val _ECVRF_hash_to_curve: ctr: nat {ctr <= curveOrder} -> pub: lbytes 32 -> len : size_nat{len < maxint U32 - 64} -> 
	input: (lbytes len) -> Tot (option ext_point)
	(decreases (curveOrder - ctr))

let rec  _ECVRF_hash_to_curve ctr pub len input = 
	let tmp =  create (len + 64) (u8 0) in 
	let tmp = update_sub #_ #_ tmp 0 len input in 
	let tmp = update_sub #_ #_ tmp len 32 pub in 
	let tmp = update_sub #_ #_ tmp (len + 32) 32 (_I2OSP ctr) in 
	let hashed = hash (len + 64) tmp in 
	let possiblePoint = _OS2ECP hashed in 
	match possiblePoint with 
		| Some p -> Some p
		| None -> if ctr < curveOrder then 
				_ECVRF_hash_to_curve (ctr + 1) pub len input
			else
				None	
	
val _ECVRF_decode_proof: pi: lbytes (op_Multiply n 5) -> Tot 
	(tuple3 (option ext_point) (lbytes n) (lbytes (op_Multiply 2 n)))

let _ECVRF_decode_proof pi = 
	let gamma = slice pi 0 (op_Multiply n 2) in 
	let c = slice pi (op_Multiply n 2) (op_Multiply n 3) in 
	let s = slice pi (op_Multiply n 3) (op_Multiply n 5) in 
	(_OS2ECP gamma, c, s)

val _ECVRF_hash_points: g: ext_point -> h: ext_point -> pub: ext_point -> gamma: ext_point -> 
	gk: ext_point -> hk: ext_point -> Tot elem

let _ECVRF_hash_points g h pub gamma gk hk = 
	let tmp = create 192 (u8 0) in 
	let tmp = update_sub #_ #_ tmp 0 32 (_ECP2OS g) in 
	let tmp = update_sub #_ #_ tmp 32 32 (_ECP2OS h) in 
	let tmp = update_sub #_ #_ tmp 64 32 (_ECP2OS pub) in 
	let tmp = update_sub #_ #_ tmp 96 32 (_ECP2OS gamma) in 
	let tmp = update_sub #_ #_ tmp 128 32 (_ECP2OS gk) in 
	let tmp = update_sub #_ #_ tmp 160 32 (_ECP2OS hk) in 
	_OS2IP (hash 192 tmp)

val _ECVRF_prove: len : size_nat{len < maxint U32 - 64} -> input: (lbytes len) -> pub: lbytes 32 -> priv: lbytes 32 -> k: elem ->
	Tot (option (lbytes (op_Multiply n 5)))

let _ECVRF_prove len input pub priv k = 
	let ap = point_decompress pub in 
		if isNone ap then None else
	let ap = get ap in 
	let h = _ECVRF_hash_to_curve 0 pub len input in 
		if isNone h then None else 
	let h = get h in 	
	let gamma = point_mul 32 priv h in 
	let kPrime = _I2OSP k in 
	let gk = point_mul 32 kPrime g in 
	let hk = point_mul 32 kPrime h in 
	let c = _ECVRF_hash_points g h ap gamma gk hk in 
	let cPrime = fmul c (_OS2IP priv) in 
	let s = fsub k cPrime in 
	let tmp = create 80 (u8 0) in 
	let tmp = update_sub #_ #_ tmp 0 32 (_ECP2OS gamma)	in 
	let halfC = slice (_I2OSP c) 0 16 in 
	let tmp = update_sub #_ #_ tmp 32 16 halfC in 
	let tmp = update_sub #_ #_ tmp 48 32 (_I2OSP s) in 
	Some tmp

val _ECVRF_proof_to_hash: pi: lbytes (op_Multiply n 5 ) -> Tot (option (lbytes (op_Multiply 2 n)))

let _ECVRF_proof_to_hash pi = 
	let (gamma, c, s ) = _ECVRF_decode_proof pi in 
	if isNone gamma then None else
	let gamma = get gamma in 
	let gammaPrime = _ECP2OS gamma in 
	let hashed = hash 32 gammaPrime in 
	Some hashed

val _ECVRF_verify:  len : size_nat{len < maxint U32 - 64} -> input: (lbytes len) -> pub: lbytes 32 ->
	pi: lbytes (op_Multiply n 5 ) ->Tot bool
	
let _ECVRF_verify len input pub pi = 
	let ap = point_decompress pub in 
		if isNone ap then false else
	let ap = get ap in 
	let (gamma, c, s ) = _ECVRF_decode_proof pi in 
		if isNone gamma then false else
	let gamma = get gamma in 
	let yc = point_mul 16 c ap in 
	let gs = point_mul 32 s g in 
	let u = point_add yc gs in 
	let h = _ECVRF_hash_to_curve 0 pub len input in 
		if isNone h then false else 
	let h = get h in 
	let gammac = point_mul 16 c gamma in 
	let hs = point_mul 32 s h in 
	let v = point_add gammac hs in 
	let c_prime = _ECVRF_hash_points g h ap gamma u v in 
	c_prime % pow2 128 = _OS2IP_16 c

