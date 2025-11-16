use crate::core::KeccakState;
// use hax_lib as hax; // Uncomment when using hax for verification

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
    // XOR input bytes into the state words
    // The state is organized as 25 u64 words, with the rate portion
    // being the first rate_in_bytes/8 words (plus partial word if needed)

    let len = input.len().min(rate_in_bytes);

    for i in 0..len {
        let word_idx = i / 8;
        let byte_idx = i % 8;

        // XOR the byte into the appropriate position in the word
        // using little-endian byte order
        let byte_val = input[i] as u64;
        state[word_idx] ^= byte_val << (byte_idx * 8);
    }
}

/// Converts the Keccak state back into a 136-byte block.
/// (Inverse of `bytes_to_state_xor`).
//
// #[hax::opaque]
// #[hax::ensures(/* ... */)]
pub fn state_to_bytes(state: &KeccakState, output: &mut [u8], rate_in_bytes: usize) {
    // Copy bytes from state words to output
    // using little-endian byte order

    let len = output.len().min(rate_in_bytes);

    for i in 0..len {
        let word_idx = i / 8;
        let byte_idx = i % 8;

        // Extract the byte from the appropriate position in the word
        // using little-endian byte order
        output[i] = (state[word_idx] >> (byte_idx * 8)) as u8;
    }
}
