use crate::core::{KeccakState, keccak_f1600};
use crate::utils;
use hax_lib as hax;

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
}

impl Sponge {
    /// Creates a new sponge for SHA3-256 (rate = 1088 bits = 136 bytes).
    pub fn new_sha3_256() -> Self {
        Sponge {
            state: [0u64; 25],
            rate_in_bytes: 136, // 1088 / 8
            squeezing_idx: 0,
        }
    }

    /// Absorbs input data into the sponge state.
    /// This function runs in a loop, processing blocks of data.
    /// We will use `#[loop_invariant]` from `verification-techniques.md`
    /// to prove this state machine is correct.
    pub fn absorb(&mut self, input: &[u8]) {
        // --- Implementation Skeleton ---
        // 1. Iterate over chunks of `input`.
        // 2. XOR chunks into the `self.state`.
        // 3. When the `rate` part is full, call `keccak_f1600`.
        //
        // let mut input_idx = 0;
        // while input_idx < input.len() {
        //   ... logic to copy bytes ...
        //   ...
        //   // When a block is full:
        //   self.state = keccak_f1600(self.state);
        // }
        // --- End Implementation ---
        unimplemented!();
    }

    /// Squeezes output data from the sponge state.
    /// This is also a loop that provides bytes to the caller.
    //
    // #[hax::loop_invariant(
    //   // "The state is valid and `squeezing_idx` is in bounds"
    //   self.squeezing_idx < self.rate_in_bytes
    // )]
    pub fn squeeze(&mut self, output: &mut [u8]) {
        // --- Implementation Skeleton ---
        // 1. Iterate `output.len()` times.
        // 2. If `squeezing_idx` is at the end of the rate,
        //    call `self.state = keccak_f1600(self.state)`.
        // 3. Copy bytes from `self.state` to `output`.
        // --- End Implementation ---
        unimplemented!();
    }

    /// Finalizes the padding and absorbs the last block.
    pub fn finalize(&mut self) {
        // --- Implementation Skeleton ---
        // 1. Add the SHA3 padding (e.g., `0x06` for SHA3)
        // 2. Pad with zeros to fill the block.
        // 3. Call `keccak_f1600` one last time.
        // --- End Implementation ---
        unimplemented!();
    }
}
