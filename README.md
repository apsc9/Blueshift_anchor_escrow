# Blueshift Anchor Escrow

A decentralized escrow application built on Solana using the [Anchor Framework](https://www.anchor-lang.com/). This program allows two parties to exchange SPL tokens trustlessly.

## Overview

The Blueshift Anchor Escrow program facilitates a secure token swap between a **Maker** and a **Taker**.
1.  **Maker:** Initiates the escrow by depositing Token A and specifying the amount of Token B they want in return.
2.  **Taker:** Fulfills the order by sending the requested amount of Token B to the Maker, receiving Token A in exchange.
3.  **Refund:** The Maker can withdraw their tokens and close the escrow if the offer has not yet been taken.

## Features

-   **Make:** Create an escrow offer, deposit tokens into a vault, and set exchange terms.
-   **Take:** Accept an escrow offer, transfer the required tokens to the maker, and receive the deposited tokens.
-   **Refund:** Cancel an active escrow and retrieve deposited tokens.
-   **Secure Vault:** Tokens are held in a Program Derived Address (PDA) controlled vault, ensuring they can only be moved according to the program's logic.

## Architecture

### Accounts

-   **Escrow Account:** A PDA that stores the terms of the trade (Maker, Mints, Receive Amount, Seed, Bump).
    -   Seeds: `[b"escrow", maker_pubkey, seed_u64]`
-   **Vault:** An Associated Token Account (ATA) owned by the Escrow PDA that holds the Maker's deposited tokens (Token A).

### Instructions

1.  **`make`**:
    -   Initializes the `Escrow` account.
    -   Creates a `Vault` account (ATA for Mint A, owned by Escrow PDA).
    -   Transfers the specified `amount` of Token A from Maker to Vault.
    -   Sets the `receive` amount (Token B expected).

2.  **`take`**:
    -   Verifies the Taker sends the correct amount of Token B to the Maker.
    -   Transfers Token A from the Vault to the Taker.
    -   Closes the Vault and Escrow accounts, refunding rent to the Maker.

3.  **`refund`**:
    -   Allows the Maker to cancel the trade.
    -   Transfers Token A from the Vault back to the Maker.
    -   Closes the Vault and Escrow accounts, refunding rent to the Maker.

## Getting Started

### Prerequisites

-   [Rust](https://www.rust-lang.org/tools/install)
-   [Solana CLI](https://docs.solana.com/cli/install-solana-cli-tools)
-   [Anchor](https://www.anchor-lang.com/docs/installation)
-   [Node.js](https://nodejs.org/) & [Yarn](https://yarnpkg.com/)

### Installation

1.  Clone the repository:
    ```bash
    git clone <repository-url>
    cd blueshift_anchor_escrow
    ```

2.  Install dependencies:
    ```bash
    yarn install
    ```

3.  Build the program:
    ```bash
    anchor build
    ```

### Testing

The project includes a comprehensive test suite using TypeScript and Mocha.

1.  **Important:** Ensure you have the `@solana/spl-token` dependency installed for tests to run correctly.
    ```bash
    yarn add @solana/spl-token
    ```

2.  Run the tests:
    ```bash
    anchor test
    ```

## Directory Structure

```
blueshift_anchor_escrow/
├── programs/
│   └── blueshift_anchor_escrow/
│       ├── src/
│       │   ├── instructions/
│       │   │   ├── make.rs      # Logic for creating an escrow
│       │   │   ├── take.rs      # Logic for fulfilling an escrow
│       │   │   ├── refund.rs    # Logic for cancelling an escrow
│       │   │   └── mod.rs
│       │   ├── state.rs         # Account structs (Escrow)
│       │   ├── errors.rs        # Custom errors
│       │   └── lib.rs           # Program entry point
│       └── Cargo.toml
├── tests/
│   └── blueshoft_anchor_escrow.ts # TypeScript integration tests
├── Anchor.toml                  # Anchor configuration
└── package.json
```

## Deployment

To deploy to a cluster (e.g., Devnet):

1.  Configure your Solana CLI:
    ```bash
    solana config set --url devnet
    ```

2.  Update `Anchor.toml` to point to `devnet`.

3.  Build and deploy:
    ```bash
    anchor build
    anchor deploy
    ```

## License

ISC
