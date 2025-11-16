use crate::sponge::Sponge;

/// Computes the SHA3-256 hash of the given input.
///
/// This is the high-level, public-facing API.
/// Its correctness relies *entirely* on the verified `Sponge` module.
/// We do not need to re-verify the logic here, only prove
/// that the components are composed correctly.
pub fn sha3_256(input: &[u8]) -> [u8; 32] {
    let mut sponge = Sponge::new_sha3_256();

    // 1. Absorb all input
    sponge.absorb(input);

    // 2. Finalize the state with padding
    sponge.finalize();

    // 3. Squeeze 32 bytes (256 bits) of output
    let mut output = [0u8; 32];
    sponge.squeeze(&mut output);

    output
}