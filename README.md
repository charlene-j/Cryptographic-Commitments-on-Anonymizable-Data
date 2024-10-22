# Cryptographic Commitments on Anonymizable Data
This repository provides a Rust implementation of our LDP-C (LDP Commitment) scheme named ORRC (Optimised Randomised Response Commitment)
which is a tuple of seven algorithm: $\mathsf{Setup}$, $\mathsf{Commit}$, $\mathsf{VerCommit}$, $\mathsf{Open}$, $\mathsf{VerOpen}$, $\mathsf{OpenLDP}$ and $\mathsf{VerOpenLDP}$. Furthermore, we implemented a signature including the algorithms $\mathsf{Gen}$, $\mathsf{Sign}$ and $\mathsf{Ver}$.

## How to use the implementation
To compile the code with the optimised features, use the `cargo build --release` command in the terminal.
To run the code, use the `cargo run --release` command, the command enables the execution of the code which is located in the 'main.rs' file, the program determines the runtime of each algorithm over a number of iterations. The number of iterations is defined by the 'iter' variable in the file and it can be configured. In addition, the size of the parameters $l_1$ and $l_2$ can be chosen by the user in the "main.rs" file.
The "lib.rs" file contains a serie of tests that permit the verification of the correct functionality of our algorithms, theses tests can be run with the `cargo test` command in the terminal.
