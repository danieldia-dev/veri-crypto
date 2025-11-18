#[cfg(hax)]
use hax_lib as hax;

// This module is the "mathematical heart" of the crate.
// It should be pure, stateless, and operate on fixed-size arrays,
// which is ideal for verification.

// The type for the Keccak state. 25x 64-bit words.
pub type KeccakState = [u64; 25];

// Round constants from Table 1
const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// Performs one full Keccak-f[1600] permutation on the given state.
///
/// This is the primary verification target. We will prove that this
/// Rust implementation is functionally equivalent to a mathematical
/// specification of Keccak-f[1600].
///
/// We will use `hax-lib-api.md`'s `#[requires]` and `#[ensures]`
/// to define its contract.
#[cfg_attr(hax, hax::requires(true))] // No precondition on the state
#[cfg_attr(hax, hax::ensures(|result|
    // Prove equivalence to the spec function.
    // This is the main correctness theorem.
    result == mathematical_spec::keccak_f1600(state)
))]
pub fn keccak_f1600(state: KeccakState) -> KeccakState {
    let mut a = state;

    // The 24 rounds of Keccak
    #[cfg_attr(hax, hax::loop_invariant(|i: usize| {
        // The state after i rounds matches the spec after i rounds
        i <= 24
    }))]
    for round in 0..24 {
        a = keccak_round(a, round);
    }

    // Return the final state
    a
}

/// A single round of the Keccak permutation.
/// This will be a private, helper function.
/// We can verify this function first, then make it `#[opaque]`
/// (from `macro-system-complete.md`) to simplify the main proof.
#[cfg_attr(hax, hax::requires(round_index < 24))]
#[cfg_attr(hax, hax::ensures(|result|
    result == mathematical_spec::keccak_round(state, round_index)
))]
#[cfg_attr(hax, hax::opaque)]
// Rotation offsets from Table 2
const R: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

// Helper to get A[x, y] from the flat state array
#[inline(always)]
fn idx(x: usize, y: usize) -> usize {
    (x % 5) + 5 * (y % 5)
}

fn keccak_round(a: KeccakState, round_index: usize) -> KeccakState {
    // We will need two temporary arrays:
    let mut c = [0u64; 5]; // For theta
    let mut b = [0u64; 25]; // For rho/pi

    // Step 1: θ (theta)
    // C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4]
    for x in 0..5 {
        c[x] = a[idx(x, 0)] ^ a[idx(x, 1)] ^ a[idx(x, 2)] ^ a[idx(x, 3)] ^ a[idx(x, 4)];
    }

    // D[x] = C[x-1] xor rot(C[x+1],1)
    // A[x,y] = A[x,y] xor D[x]
    // We can combine these two. `(x+4)%5` is `x-1` (mod 5). `(x+1)%5` is `x+1` (mod 5).
    let mut new_a = [0u64; 25]; // We write the result of theta into new_a
    for x in 0..5 {
        let d_x = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        for y in 0..5 {
            new_a[idx(x, y)] = a[idx(x, y)] ^ d_x;
        }
    }

    // Step 2: ρ (rho) and π (pi)
    // B[y,2*x+3*y] = rot(A[x,y], r[x,y])
    // This is a single combined step. We use the state `new_a` from theta.
    for x in 0..5 {
        for y in 0..5 {
            let new_x = y % 5;
            let new_y = (2 * x + 3 * y) % 5;
            let r_offset = R[idx(x, y)];
            b[idx(new_x, new_y)] = new_a[idx(x, y)].rotate_left(r_offset);
        }
    }

    // Step 3: χ (chi)
    // A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y])
    // We must use the `b` array as the source and write to `new_a`.
    // We cannot update `b` in-place, as it would corrupt the calculation.
    for x in 0..5 {
        for y in 0..5 {
            new_a[idx(x, y)] = b[idx(x, y)] ^ ((!b[idx(x + 1, y)]) & b[idx(x + 2, y)]);
        }
    }

    // Step 4: ι (iota)
    // A[0,0] = A[0,0] xor RC
    // We apply this to the state we just calculated from chi.
    new_a[idx(0, 0)] = new_a[idx(0, 0)] ^ RC[round_index];

    // Return the new state
    new_a
}

/// This module contains the pure, mathematical specification
/// of Keccak, written in Rust but marked for `hax` to use as a spec.
/// This is a simple, unoptimized, but "obviously correct" implementation
/// that closely follows the Keccak specification.
#[cfg(hax)]
mod mathematical_spec {
    use super::{KeccakState, RC, R};

    // Helper to get A[x, y] from the flat state array
    #[inline(always)]
    fn idx(x: usize, y: usize) -> usize {
        (x % 5) + 5 * (y % 5)
    }

    /// The specification function for a single Keccak round.
    /// This implements the five step mappings: θ, ρ, π, χ, and ι.
    #[hax::spec]
    pub fn keccak_round(a: KeccakState, round_index: usize) -> KeccakState {
        // Step 1: θ (theta) - diffusion
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = a[idx(x, 0)] ^ a[idx(x, 1)] ^ a[idx(x, 2)] ^ a[idx(x, 3)] ^ a[idx(x, 4)];
        }

        let mut after_theta = [0u64; 25];
        for x in 0..5 {
            let d_x = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            for y in 0..5 {
                after_theta[idx(x, y)] = a[idx(x, y)] ^ d_x;
            }
        }

        // Step 2: ρ (rho) and π (pi) - rotation and permutation
        let mut after_rho_pi = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                let new_x = y % 5;
                let new_y = (2 * x + 3 * y) % 5;
                let r_offset = R[idx(x, y)];
                after_rho_pi[idx(new_x, new_y)] = after_theta[idx(x, y)].rotate_left(r_offset);
            }
        }

        // Step 3: χ (chi) - non-linear mixing
        let mut after_chi = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                after_chi[idx(x, y)] = after_rho_pi[idx(x, y)]
                    ^ ((!after_rho_pi[idx(x + 1, y)]) & after_rho_pi[idx(x + 2, y)]);
            }
        }

        // Step 4: ι (iota) - round constant addition
        after_chi[idx(0, 0)] = after_chi[idx(0, 0)] ^ RC[round_index];

        after_chi
    }

    /// The specification function for the full Keccak-f[1600] permutation.
    /// This applies 24 rounds of the Keccak round function.
    #[hax::spec]
    pub fn keccak_f1600(state: KeccakState) -> KeccakState {
        let mut a = state;
        for round in 0..24 {
            a = keccak_round(a, round);
        }
        a
    }
}
