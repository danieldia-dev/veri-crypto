use crate::core::KeccakState;
use hax_lib as hax;

/// Converts a 136-byte (1088-bit) block into the Keccak state.
///
/// This function is full of byte-level manipulations
/// (endianness, bit-fiddling) which are annoying to verify.
///
/// STRATEGY: We will verify this function *once* and then
/// make it `#[hax::opaque]` (from `macro-system-complete.md`).
/// This hides its internal complexity from the `sponge` module,
/// making the sponge's proof *much* simpler.
//
// #[hax::opaque]
// #[hax::ensures(|result|
//    result == mathematical_spec::bytes_to_state(input)
// )]
pub fn bytes_to_state_xor(state: &mut KeccakState, input: &[u8], rate_in_bytes: usize) {
    // --- Implementation Skeleton ---
    // 1. Iterate over the `rate_in_bytes`.
    // 2. XOR `input` bytes into the `state` words
    //    (handling little-endian conversion).
    // --- End Implementation ---
    unimplemented!();
}

/// Converts the Keccak state back into a 136-byte block.
/// (Inverse of `bytes_to_state_xor`).
//
// #[hax::opaque]
// #[hax::ensures(/* ... */)]
pub fn state_to_bytes(state: &KeccakState, output: &mut [u8], rate_in_bytes: usize) {
    // --- Implementation Skeleton ---
    // 1. Iterate over `rate_in_bytes`.
    // 2. Copy bytes from `state` words to `output`
    //    (handling little-endian conversion).
    // --- End Implementation ---
    unimplemented!();
}
