module Utils

(* This module contains formal verification of byte conversion utilities.
   These functions are marked as opaque after verification to simplify
   higher-level proofs. *)

open FStar.Mul
open Core

(* Convert bytes to state with XOR operation *)
val bytes_to_state_xor (state: keccak_state) (input: bytes) (rate_in_bytes: nat)
  : keccak_state

(* Convert state to bytes *)
val state_to_bytes (state: keccak_state) (rate_in_bytes: nat)
  : bytes

(* Specification: Mathematical definition of bytes_to_state_xor *)
val bytes_to_state_xor_spec (state: keccak_state) (input: bytes) (rate_in_bytes: nat)
  : keccak_state

(* Specification: Mathematical definition of state_to_bytes *)
val state_to_bytes_spec (state: keccak_state) (rate_in_bytes: nat)
  : bytes

(* Theorem: bytes_to_state_xor matches its specification *)
val bytes_to_state_xor_correctness:
  state: keccak_state ->
  input: bytes ->
  rate_in_bytes: nat{length input <= rate_in_bytes} ->
  Lemma (ensures
    bytes_to_state_xor state input rate_in_bytes ==
    bytes_to_state_xor_spec state input rate_in_bytes)

(* Theorem: state_to_bytes matches its specification *)
val state_to_bytes_correctness:
  state: keccak_state ->
  rate_in_bytes: nat{rate_in_bytes <= 200} ->
  Lemma (ensures
    state_to_bytes state rate_in_bytes ==
    state_to_bytes_spec state rate_in_bytes)

(* Theorem: byte conversions preserve lengths *)
val byte_conversion_length_preservation:
  state: keccak_state ->
  rate_in_bytes: nat{rate_in_bytes <= 200} ->
  Lemma (ensures length (state_to_bytes state rate_in_bytes) == rate_in_bytes)

(* Theorem: Little-endian encoding/decoding is correct *)
val little_endian_correctness:
  state: keccak_state ->
  rate_in_bytes: nat{rate_in_bytes <= 200} ->
  Lemma (ensures
    (let bytes = state_to_bytes state rate_in_bytes in
     (* Property: each byte corresponds to the correct position in the state *)
     forall (i: nat{i < rate_in_bytes}).
       let word_idx = i / 8 in
       let byte_idx = i % 8 in
       Seq.index bytes i ==
       FStar.UInt64.uint_to_t ((FStar.UInt64.v (Seq.index state word_idx)) / (pow2 (byte_idx * 8))) % 256))

(* Theorem: XOR operation is commutative at byte level *)
val xor_commutativity:
  state: keccak_state ->
  input1: bytes ->
  input2: bytes ->
  rate_in_bytes: nat{length input1 <= rate_in_bytes && length input2 <= rate_in_bytes} ->
  Lemma (ensures
    bytes_to_state_xor (bytes_to_state_xor state input1 rate_in_bytes) input2 rate_in_bytes ==
    bytes_to_state_xor (bytes_to_state_xor state input2 rate_in_bytes) input1 rate_in_bytes)

(* Mark these functions as opaque for higher-level proofs *)
let bytes_to_state_xor_opaque = bytes_to_state_xor
let state_to_bytes_opaque = state_to_bytes
