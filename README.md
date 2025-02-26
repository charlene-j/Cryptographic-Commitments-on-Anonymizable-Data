# Cryptographic Commitments on Anonymizable Data
This repository provides a Rust implementation of our LDP-C (LDP Commitment) scheme named ORRC (Optimized Randomized Response Commitment)
which is a tuple of seven algorithm: $\mathsf{Setup}$, $\mathsf{Commit}$, $\mathsf{VerCommit}$, $\mathsf{Open}$, $\mathsf{VerOpen}$, $\mathsf{OpenLDP}$ and $\mathsf{VerOpenLDP}$. Furthermore, we implemented a signature including the algorithms $\mathsf{Gen}$, $\mathsf{Sign}$ and $\mathsf{Ver}$.

## How to use the implementation
To compile the code with the optimized features, use the `cargo build --release` command in the terminal.
To run the code, use the `cargo run --release` command, the command enables the execution of the code which is located in the "main.rs" file, the program determines the runtime of each algorithm over a number of iterations. The number of iterations is defined by the 'iter' variable in the file and it can be configured. In addition, the size of the parameters $\ell_1$ and $\ell_2$ can be chosen by the user in the "main.rs" file.
The "lib.rs" file contains a serie of tests that permit the verification of the correct functionality of our algorithms, theses tests can be run with the `cargo test` command in the terminal.

## Dependencies and versions
cargo version: 1.75.0

rustc version: 1.75.0

[dependencies]

curve25519-dalek ="4.1.3"

rand_core = { version = "0.6.4", features = ["getrandom"] }
rand = "0.8.5"

log = "0.4.20"

pretty_env_logger = "0.5.0"

sha2 = "0.10.8"

digest = "0.10.7"

zeroize = "1.7.0"


