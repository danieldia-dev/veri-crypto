use veri_rust_crypto::sha3_256;

fn main() {
    // Example 1: Hash a simple string
    let message = b"Hello, Veri-Rust-Crypto!";
    let hash = sha3_256(message);

    println!("Message: {}", String::from_utf8_lossy(message));
    println!("SHA3-256: {}", hex::encode(hash));
    println!();

    // Example 2: Hash an empty message
    let empty_hash = sha3_256(b"");
    println!("Empty message SHA3-256: {}", hex::encode(empty_hash));
    println!();

    // Example 3: Hash a longer message
    let long_message = b"The quick brown fox jumps over the lazy dog. The quick brown fox jumps over the lazy dog.";
    let long_hash = sha3_256(long_message);
    println!(
        "Long message: {}",
        String::from_utf8_lossy(&long_message[..50])
    );
    println!("SHA3-256: {}", hex::encode(long_hash));

    // Example 4: Demonstrate hash properties
    let message1 = b"message1";
    let message2 = b"message2";
    let hash1 = sha3_256(message1);
    let hash2 = sha3_256(message2);

    println!("\nDemonstrating hash properties:");
    println!("hash('message1') = {}", hex::encode(hash1));
    println!("hash('message2') = {}", hex::encode(hash2));
    println!("Different inputs produce completely different outputs!");
}
