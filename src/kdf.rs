use crate::sponge::Sponge;

/// A simple Key Derivation Function (KDF) built from the sponge.
/// This demonstrates the "versatile" part of the sponge and
/// provides the "secure messaging" application.
///
/// This function's security relies on the verified `Sponge`.
///
/// Note: This is a simplified KDF. A production-ready KDF
/// like HKDF is more complex, but this serves the project goal.
//
// We can add contracts from `hax-lib-api.md`.
// #[hax::ensures(|result| result.len() == output_len)]
pub fn sponge_kdf(key: &[u8], info: &[u8], output_len: usize) -> Vec<u8> {
    let mut sponge = Sponge::new_sha3_256();

    // 1. Absorb the key material
    sponge.absorb(key);

    // 2. Absorb the context/info string
    sponge.absorb(info);

    // 3. Finalize
    sponge.finalize();

    // 4. Squeeze the desired number of output bytes
    let mut output = vec![0u8; output_len];
    sponge.squeeze(&mut output);

    output
}
