use veri_rust_crypto::sponge_kdf;

fn main() {
    println!("=== Key Derivation Function (KDF) Example ===\n");

    // Example: Derive keys for a secure messaging session

    // Shared secret from a key exchange (e.g., Diffie-Hellman)
    let shared_secret = b"this_is_a_shared_secret_from_DH_key_exchange";

    // Context information to make the derivation unique
    let session_info = b"ClientA||ServerB||Session2024";

    // Derive an encryption key (32 bytes for AES-256)
    let encryption_key = sponge_kdf(shared_secret, b"encryption||Session2024", 32);
    println!("Encryption Key (32 bytes):");
    println!("  {}", hex::encode(&encryption_key));
    println!();

    // Derive an authentication key (32 bytes for HMAC-SHA256)
    let auth_key = sponge_kdf(shared_secret, b"authentication||Session2024", 32);
    println!("Authentication Key (32 bytes):");
    println!("  {}", hex::encode(&auth_key));
    println!();

    // Example: Key ratcheting for forward secrecy
    println!("=== Key Ratcheting Example ===\n");

    let mut current_key = shared_secret.to_vec();
    for i in 0..3 {
        let ratchet_info = format!("ratchet||epoch_{}", i);
        let next_key = sponge_kdf(&current_key, ratchet_info.as_bytes(), 32);
        println!("Epoch {} key: {}", i, hex::encode(&next_key));
        current_key = next_key;
    }
    println!();

    // Example: Derive multiple keys from same secret
    println!("=== Multi-Key Derivation ===\n");

    // Derive 96 bytes total: encryption (32) + auth (32) + IV (16) + extra (16)
    let all_keys = sponge_kdf(shared_secret, b"all_keys||Session2024", 96);

    let (encryption_part, rest) = all_keys.split_at(32);
    let (auth_part, rest) = rest.split_at(32);
    let (iv_part, extra_part) = rest.split_at(16);

    println!("Derived from single KDF call:");
    println!("  Encryption: {}", hex::encode(encryption_part));
    println!("  Auth:       {}", hex::encode(auth_part));
    println!("  IV:         {}", hex::encode(iv_part));
    println!("  Extra:      {}", hex::encode(extra_part));
}
