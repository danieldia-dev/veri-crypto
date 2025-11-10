use hax_lib as hax;

// This module is the "mathematical heart" of the crate.
// It should be pure, stateless, and operate on fixed-size arrays,
// which is ideal for verification.

// The type for the Keccak state. 25x 64-bit words.
pub type KeccakState = [u64; 25];

/// Performs one full Keccak-f[1600] permutation on the given state.
///
/// This is the primary verification target. We will prove that this
/// Rust implementation is functionally equivalent to a mathematical
/// specification of Keccak-f[1600].
///
/// We will use `hax-lib-api.md`'s `#[requires]` and `#[ensures]`
/// to define its contract.
//
// #[hax::requires(/* true */)] // No precondition on the state
// #[hax::ensures(|result_state|
//    // Prove equivalence to a spec function.
//    // This is "Idea 1" from our plan.
//    result_state == mathematical_spec::keccak_f1600(state)
// )]
pub fn keccak_f1600(state: KeccakState) -> KeccakState {
    let mut a = state;

    // --- Implementation Skeleton ---
    // The 24 rounds of Keccak go here.
    // for round in 0..24 {
    //   a = keccak_round(a, round);
    // }
    // --- End Implementation ---

    // We will not write the 1,000 lines of Keccak logic here.
    // We'll use a `todo!()` or `unimplemented!()` as a placeholder
    // while we set up the verification pipeline.
    unimplemented!("Keccak-f[1600] logic goes here");

    // The final state.
    // The `#[ensures]` contract will be proven against this.
    // a
}

/// A single round of the Keccak permutation.
/// This will be a private, helper function.
/// We can verify this function first, then make it `#[opaque]`
/// (from `macro-system-complete.md`) to simplify the main proof.
//
// #[hax::opaque]
// #[hax::ensures(|result| result == mathematical_spec::keccak_round(state, round_index))]
fn keccak_round(state: KeccakState, round_index: usize) -> KeccakState {
    // --- Implementation Skeleton ---
    // 1. Theta step
    // 2. Rho and Pi steps
    // 3. Chi step
    // 4. Iota step
    // --- End Implementation ---
    unimplemented!();
}

/// This module would contain the pure, mathematical specification
/// of Keccak, written in Rust but marked for `hax` to use as a spec.
#[cfg(hax)]
mod mathematical_spec {
    use super::KeccakState;

    /// The "specification" function. This is a "ghost" function
    /// that is only used for proof.
    // #[hax::lemma]
    // #[hax::ensures(/* ... */)] // This *is* the spec
    pub fn keccak_f1600(state: KeccakState) -> KeccakState {
        // ... a simple, unoptimized, but "obviously correct"
        // implementation of Keccak to prove against.
        unimplemented!();
    }
}
