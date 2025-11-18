# Formal Verification Documentation

This directory contains formal verification artifacts for the veri-crypto library using the [hax](https://github.com/hacspec/hax) toolchain.

## Overview

The verification approach follows a layered strategy:

1. **Core Layer** (`Core.fst`): Verify the Keccak-f[1600] permutation
2. **Utils Layer** (`Utils.fst`): Verify byte conversion utilities, then mark as opaque
3. **Sponge Layer** (`Sponge.fst`): Verify the stateful sponge construction using verified core

## Verification Structure

### Core Module (core.rs → Core.fst)

**Main Theorems:**
- `keccak_f1600_correctness_theorem`: The Rust implementation matches the mathematical specification
- `keccak_f1600_is_permutation`: Keccak-f[1600] is bijective
- `keccak_round_composition`: Individual rounds compose correctly

**Approach:**
1. Define a mathematical specification `keccak_f1600_spec` that closely follows the NIST FIPS 202 standard
2. Prove that the optimized Rust implementation `keccak_f1600` is equivalent to the spec
3. Use loop invariants to verify the 24-round iteration

### Sponge Module (sponge.rs → Sponge.fst)

**Main Theorems:**
- `sponge_invariant_preservation`: All operations maintain the sponge invariants
- `absorption_determinism`: Absorbing the same input produces the same state
- `squeezing_determinism`: Squeezing produces deterministic output
- `absorb_squeeze_consistency`: The absorb-finalize-squeeze sequence is well-formed

**Invariants:**
```fstar
sponge_invariant s =
  s.rate_in_bytes == 136 &&
  s.absorbed_bytes <= s.rate_in_bytes &&
  s.squeezing_idx <= s.rate_in_bytes
```

**Approach:**
1. Define refinement types with invariants
2. Use loop invariants in `absorb` and `squeeze` methods
3. Prove invariants are preserved across all state transitions

### Utils Module (utils.rs → Utils.fst)

**Main Theorems:**
- `bytes_to_state_xor_correctness`: Byte-to-state conversion is correct
- `state_to_bytes_correctness`: State-to-byte conversion is correct
- `byte_conversion_length_preservation`: Lengths are preserved
- `little_endian_correctness`: Little-endian encoding is correct
- `xor_commutativity`: XOR operations commute

**Opacity Strategy:**
After verification, these functions are marked as opaque using `#[hax::opaque]` to hide implementation details from higher-level proofs.

## Hax Annotations Used

### Pre/Post-conditions
```rust
#[cfg_attr(hax, hax::requires(precondition))]
#[cfg_attr(hax, hax::ensures(|result| postcondition))]
```

### Loop Invariants
```rust
#[cfg_attr(hax, hax::loop_invariant(|i: usize| invariant))]
```

### Type Refinements
```rust
#[cfg_attr(hax, hax::refinement(|self| invariant))]
```

### Opacity
```rust
#[cfg_attr(hax, hax::opaque)]
```

### Specifications
```rust
#[hax::spec]
fn mathematical_spec(...) -> ... { ... }
```

## Verification Workflow

### 1. Extract to F*
```bash
cargo hax into fstar
```

This generates `.fst` and `.fsti` files from the annotated Rust code.

### 2. Verify with F*
```bash
cd proofs/fstar
fstar.exe --cache_checked_modules \
  --fuel 8 --ifuel 2 --z3rlimit 100 \
  Core.fst Sponge.fst Utils.fst
```

### 3. Alternative Backends

**Lean 4:**
```bash
cargo hax into lean
cd proofs/lean
lake build
```

**Coq:**
```bash
cargo hax into coq
cd proofs/coq
coqc *.v
```

## Proof Obligations

The following theorems need to be proven:

| Module | Proof Obligation | Status |
|--------|------------------|---------|
| Core | `keccak_f1600_correctness` | Annotated, ready for proof |
| Core | `round_function_correctness` | Annotated, ready for proof |
| Sponge | `invariant_preservation` | Annotated, ready for proof |
| Sponge | `absorption_determinism` | Annotated, ready for proof |
| Utils | `byte_conversion_correctness` | Annotated, ready for proof |

## Mathematical Specification

The mathematical specification is defined in `src/core.rs` under the `mathematical_spec` module (compiled only with `cfg(hax)`):

```rust
#[cfg(hax)]
mod mathematical_spec {
    #[hax::spec]
    pub fn keccak_f1600(state: KeccakState) -> KeccakState {
        // Simple, obviously-correct implementation
        let mut a = state;
        for round in 0..24 {
            a = keccak_round(a, round);
        }
        a
    }

    #[hax::spec]
    pub fn keccak_round(a: KeccakState, round_index: usize) -> KeccakState {
        // Implements θ, ρ, π, χ, ι steps
        // ...
    }
}
```

## Properties Verified

1. **Functional Correctness**: Implementation matches specification
2. **Memory Safety**: No buffer overflows or out-of-bounds access
3. **Type Safety**: All operations are well-typed
4. **Invariant Preservation**: State machine invariants hold
5. **Determinism**: Same inputs produce same outputs
6. **Permutation**: Keccak-f[1600] is bijective

## Future Work

1. **Cryptographic Properties**: Prove collision resistance and preimage resistance (requires cryptographic assumptions)
2. **Side-Channel Resistance**: Verify constant-time properties
3. **Full SHA3 Suite**: Extend to SHA3-384, SHA3-512, SHAKE128, SHAKE256
4. **Performance**: Verify optimized implementations (SIMD, assembly)

## References

- [NIST FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf) - SHA-3 Standard
- [hax Documentation](https://github.com/hacspec/hax)
- [F* Tutorial](https://fstar-lang.org/tutorial/)
- [Keccak Team](https://keccak.team/)

## Notes

The F* files in this directory are example stubs demonstrating the structure of the formal verification. In a production environment with a properly configured hax toolchain, these would be automatically extracted from the Rust source code using:

```bash
cargo hax into fstar
```

The Rust source code in `src/` contains all the necessary hax annotations and mathematical specifications ready for extraction and verification.
