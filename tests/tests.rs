#[cfg(test)]
mod tests {
    use crate::core::keccak_f1600;
    use crate::sponge::Sponge;
    use crate::{sha3_256, sponge_kdf};

    #[test]
    fn test_sha3_256_empty() {
        // Test vector from NIST
        let result = sha3_256(b"");
        let expected =
            hex::decode("a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a")
                .unwrap();
        assert_eq!(result.to_vec(), expected);
    }

    #[test]
    fn test_sha3_256_abc() {
        // Test vector from NIST
        let result = sha3_256(b"abc");
        let expected =
            hex::decode("3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532")
                .unwrap();
        assert_eq!(result.to_vec(), expected);
    }

    #[test]
    fn test_sha3_256_long() {
        // Test with longer input
        let input = b"The quick brown fox jumps over the lazy dog";
        let result = sha3_256(input);
        let expected =
            hex::decode("69070dda01975c8c120c3aada1b282394e7f032fa9cf32f4cb2259a0897dfc04")
                .unwrap();
        assert_eq!(result.to_vec(), expected);
    }

    #[test]
    fn test_keccak_permutation_zero_state() {
        // Test that permutation of zero state is deterministic
        let zero_state = [0u64; 25];
        let result = keccak_f1600(zero_state);

        // The result should be non-zero after permutation
        assert_ne!(result, zero_state);

        // Running twice should give same result
        let result2 = keccak_f1600(zero_state);
        assert_eq!(result, result2);
    }

    #[test]
    fn test_sponge_absorb_squeeze() {
        let mut sponge = Sponge::new_sha3_256();

        // Absorb some data
        sponge.absorb(b"test data");
        sponge.finalize();

        // Squeeze output
        let mut output1 = [0u8; 32];
        sponge.squeeze(&mut output1);

        // Create a new sponge with same input
        let mut sponge2 = Sponge::new_sha3_256();
        sponge2.absorb(b"test data");
        sponge2.finalize();

        let mut output2 = [0u8; 32];
        sponge2.squeeze(&mut output2);

        // Should produce same output
        assert_eq!(output1, output2);
    }

    #[test]
    fn test_kdf_deterministic() {
        let key = b"test_key";
        let info = b"test_info";

        // KDF should be deterministic
        let output1 = sponge_kdf(key, info, 64);
        let output2 = sponge_kdf(key, info, 64);

        assert_eq!(output1, output2);
        assert_eq!(output1.len(), 64);
    }

    #[test]
    fn test_kdf_different_info() {
        let key = b"test_key";

        // Different info should produce different outputs
        let output1 = sponge_kdf(key, b"info1", 32);
        let output2 = sponge_kdf(key, b"info2", 32);

        assert_ne!(output1, output2);
    }

    #[test]
    fn test_kdf_different_lengths() {
        let key = b"test_key";
        let info = b"test_info";

        // Test different output lengths
        let output_16 = sponge_kdf(key, info, 16);
        let output_32 = sponge_kdf(key, info, 32);
        let output_64 = sponge_kdf(key, info, 64);

        assert_eq!(output_16.len(), 16);
        assert_eq!(output_32.len(), 32);
        assert_eq!(output_64.len(), 64);

        // First 16 bytes of longer outputs should match output_16
        assert_eq!(&output_32[..16], &output_16[..]);
        assert_eq!(&output_64[..16], &output_16[..]);
    }

    #[test]
    fn test_sponge_multiple_absorb() {
        let mut sponge1 = Sponge::new_sha3_256();
        sponge1.absorb(b"Hello");
        sponge1.absorb(b"World");
        sponge1.finalize();

        let mut output1 = [0u8; 32];
        sponge1.squeeze(&mut output1);

        // Single absorb with concatenated data
        let mut sponge2 = Sponge::new_sha3_256();
        sponge2.absorb(b"HelloWorld");
        sponge2.finalize();

        let mut output2 = [0u8; 32];
        sponge2.squeeze(&mut output2);

        // Should produce same result
        assert_eq!(output1, output2);
    }

    #[test]
    fn test_sponge_squeeze_multiple() {
        let mut sponge = Sponge::new_sha3_256();
        sponge.absorb(b"test");
        sponge.finalize();

        // Squeeze in parts
        let mut part1 = [0u8; 16];
        let mut part2 = [0u8; 16];
        sponge.squeeze(&mut part1);
        sponge.squeeze(&mut part2);

        // Create new sponge for comparison
        let mut sponge2 = Sponge::new_sha3_256();
        sponge2.absorb(b"test");
        sponge2.finalize();

        // Squeeze all at once
        let mut full = [0u8; 32];
        sponge2.squeeze(&mut full);

        // Parts should match full output
        assert_eq!(&full[..16], &part1[..]);
        assert_eq!(&full[16..], &part2[..]);
    }

    #[test]
    fn test_hash_collision_resistance() {
        // Test that similar inputs produce very different outputs
        let hash1 = sha3_256(b"test1");
        let hash2 = sha3_256(b"test2");

        // Count differing bits (should be approximately half)
        let mut diff_bits = 0;
        for i in 0..32 {
            diff_bits += (hash1[i] ^ hash2[i]).count_ones();
        }

        // Should have significant difference (>50 bits different)
        assert!(diff_bits > 50);
    }
}
