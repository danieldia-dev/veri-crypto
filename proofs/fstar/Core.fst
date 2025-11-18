module Core

(* This is an example F* module that would be extracted from the Rust code.
   In a full hax extraction, this would be automatically generated.
   This demonstrates the structure of the formal verification. *)

open FStar.Mul

(* Type representing the Keccak state: 25 64-bit words *)
type keccak_state = lseq FStar.UInt64.t 25

(* Round constants from the Keccak specification *)
let rc : lseq FStar.UInt64.t 24 = [
  0x0000000000000001uL; 0x0000000000008082uL; 0x800000000000808AuL;
  0x8000000080008000uL; 0x000000000000808BuL; 0x0000000080000001uL;
  0x8000000080008081uL; 0x8000000000008009uL; 0x000000000000008AuL;
  0x0000000000000088uL; 0x0000000080008009uL; 0x000000008000000AuL;
  0x000000008000808BuL; 0x800000000000008BuL; 0x8000000000008089uL;
  0x8000000000008003uL; 0x8000000000008002uL; 0x0000000000000080uL;
  0x000000000000800AuL; 0x800000008000000AuL; 0x8000000080008081uL;
  0x8000000000008080uL; 0x0000000080000001uL; 0x8000000080008008uL
]

(* Rotation offsets from the Keccak specification *)
let r : lseq nat 25 = [
  0; 1; 62; 28; 27; 36; 44; 6; 55; 20; 3; 10; 43; 25; 39;
  41; 45; 15; 21; 8; 18; 2; 61; 56; 14
]

(* Helper function to compute array index from (x, y) coordinates *)
let idx (x: nat{x < 5}) (y: nat{y < 5}) : nat{idx x y < 25} =
  (x % 5) + 5 * (y % 5)

(* Mathematical specification of a single Keccak round *)
val keccak_round_spec (state: keccak_state) (round_index: nat{round_index < 24})
  : keccak_state

(* Mathematical specification of the full Keccak-f[1600] permutation *)
val keccak_f1600_spec (state: keccak_state) : keccak_state

(* Implementation of keccak_f1600 (extracted from Rust) *)
val keccak_f1600 (state: keccak_state) : keccak_state

(* Main correctness theorem: The implementation matches the specification *)
val keccak_f1600_correctness_theorem:
  state: keccak_state ->
  Lemma (ensures keccak_f1600 state == keccak_f1600_spec state)

(* Theorem: Keccak-f[1600] is a permutation (bijective) *)
val keccak_f1600_is_permutation:
  state1: keccak_state ->
  state2: keccak_state ->
  Lemma (requires keccak_f1600 state1 == keccak_f1600 state2)
        (ensures state1 == state2)

(* Theorem: Keccak rounds are composable *)
val keccak_round_composition:
  state: keccak_state ->
  r1: nat{r1 < 24} ->
  r2: nat{r2 < 24} ->
  Lemma (ensures
    keccak_round_spec (keccak_round_spec state r1) r2 ==
    keccak_round_spec state r2)
