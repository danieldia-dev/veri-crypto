use crate::core::{KeccakState, keccak_f1600};
use crate::utils;
// use hax_lib as hax; // Uncomment when using hax for verification

const RATE_IN_BYTES: usize = 136;

/// Represents the stateful Keccak sponge construction.
/// This is the second verification target: a state machine.
/// We will prove its invariants.
pub struct Sponge {
    // The 1600-bit (200-byte) internal state.
    state: KeccakState,
    // The number of bytes in the "rate" (non-capacity)
    // part of the state that have been filled.
    rate_in_bytes: usize,
    // The index into the rate for squeezing.
    squeezing_idx: usize,
    // Position in the current block being absorbed
    absorbed_bytes: usize,
}

impl Sponge {
    /// Creates a new sponge for SHA3-256 (rate = 1088 bits = 136 bytes).
    pub fn new_sha3_256() -> Self {
        Sponge {
            state: [0u64; 25],
            rate_in_bytes: RATE_IN_BYTES, // 1088 / 8
            squeezing_idx: 0,
            absorbed_bytes: 0,
        }
    }

    /// Absorbs input data into the sponge state.
    /// This function runs in a loop, processing blocks of data.
    /// We will use `#[loop_invariant]`
    /// to prove this state machine is correct.
    pub fn absorb(&mut self, input: &[u8]) {
        let mut offset = 0;

        while offset < input.len() {
            // Determine how many bytes to process in this iteration
            let remaining_in_block = self.rate_in_bytes - self.absorbed_bytes;
            let bytes_to_absorb = (input.len() - offset).min(remaining_in_block);

            // XOR the input directly into the state at the correct position
            for i in 0..bytes_to_absorb {
                let pos = self.absorbed_bytes + i;
                let word_idx = pos / 8;
                let byte_idx = pos % 8;
                let byte_val = input[offset + i] as u64;
                self.state[word_idx] ^= byte_val << (byte_idx * 8);
            }

            self.absorbed_bytes += bytes_to_absorb;
            offset += bytes_to_absorb;

            // If we've filled a complete block, apply the permutation
            if self.absorbed_bytes == self.rate_in_bytes {
                self.state = keccak_f1600(self.state);
                self.absorbed_bytes = 0;
            }
        }
    }

    /// Squeezes output data from the sponge state.
    /// This is also a loop that provides bytes to the caller.
    //
    // #[hax::loop_invariant(
    //   // "The state is valid and `squeezing_idx` is in bounds"
    //   self.squeezing_idx < self.rate_in_bytes
    // )]
    pub fn squeeze(&mut self, output: &mut [u8]) {
        let mut output_idx = 0;

        while output_idx < output.len() {
            // If we've squeezed all available bytes from current state, permute
            if self.squeezing_idx == self.rate_in_bytes {
                self.state = keccak_f1600(self.state);
                self.squeezing_idx = 0;
            }

            // Calculate how many bytes we can squeeze from current state
            let bytes_to_squeeze =
                (output.len() - output_idx).min(self.rate_in_bytes - self.squeezing_idx);

            // Create a temporary buffer to hold the state bytes
            let mut temp_buffer = vec![0u8; self.rate_in_bytes];
            utils::state_to_bytes(&self.state, &mut temp_buffer, self.rate_in_bytes);

            // Copy the squeezed bytes to the output
            output[output_idx..output_idx + bytes_to_squeeze].copy_from_slice(
                &temp_buffer[self.squeezing_idx..self.squeezing_idx + bytes_to_squeeze],
            );

            self.squeezing_idx += bytes_to_squeeze;
            output_idx += bytes_to_squeeze;
        }
    }

    /// Finalizes the padding and absorbs the last block.
    pub fn finalize(&mut self) {
        // SHA3 padding: append 0x06, pad with zeros, then append 0x80
        // The 0x06 is the SHA3 domain separator

        // Get the current position in the block
        let pos = self.absorbed_bytes;

        // Apply the first padding byte (0x06 for SHA3)
        let word_idx = pos / 8;
        let byte_idx = pos % 8;
        self.state[word_idx] ^= 0x06u64 << (byte_idx * 8);

        // Apply the final padding byte (0x80) at the last position of the rate
        let last_pos = self.rate_in_bytes - 1;
        let last_word_idx = last_pos / 8;
        let last_byte_idx = last_pos % 8;
        self.state[last_word_idx] ^= 0x80u64 << (last_byte_idx * 8);

        // Apply the final permutation
        self.state = keccak_f1600(self.state);

        // Reset for squeezing
        self.absorbed_bytes = 0;
        self.squeezing_idx = 0;
    }
}
