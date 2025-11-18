/// Veri-Rust-Crypto: A modular, formally verified cryptographic crate.
///
/// This crate provides cryptographic primitives built on a verified
/// Keccak-f[1600] permutation.
///
/// The verification strategy is:
/// 1. `core`: Prove functional correctness of the permutation.
/// 2. `sponge`: Prove correctness of the stateful sponge construction.
/// 3. `hash`/`kdf`: Compose the verified sponge into high-level APIs.
// The core permutation, the primary verification target.
pub mod core;

// The stateful sponge construction built on the core.
pub mod sponge;

// High-level "application" modules that use the sponge.
pub mod hash;
pub mod kdf;

// Internal utilities for byte/word conversions.
mod utils;

// Re-export the main, public-facing functions.
pub use hash::sha3_256;
pub use kdf::sponge_kdf;

// Test module
#[cfg(test)]
mod tests;