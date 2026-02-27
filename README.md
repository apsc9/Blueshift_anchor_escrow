# Blueshift Anchor Escrow

A decentralized escrow program on Solana using [Anchor](https://www.anchor-lang.com/). Two parties exchange SPL tokens trustlessly, with support for expiry deadlines, protocol fees, and partial fills.

## Overview

1. **Maker** creates an escrow — deposits Token A, sets how much Token B they want, a deadline, and an optional fee.
2. **Taker** fills the escrow (fully or partially) — sends Token B, receives proportional Token A.
3. **Refund** — Maker can cancel and reclaim tokens at any time.

## Features

- **Expiry / Deadline** — Maker sets an `expires_at` timestamp. Expired escrows cannot be taken but can always be refunded.
- **Protocol Fees** — Maker sets `fee_bps` (0–10,000 = 0%–100%). On take, fee is deducted from the Token B payment and sent to a treasury PDA.
- **Partial Fills** — Taker specifies `fill_amount` (how much Token B to pay). Proportional Token A is released; escrow stays alive until fully filled.
- **Secure Vault** — Tokens are held in a PDA-controlled vault, movable only by program logic.

## Architecture

### Escrow State

| Field | Type | Description |
|-------|------|-------------|
| `seed` | `u64` | Unique seed per maker |
| `maker` | `Pubkey` | Creator of the escrow |
| `mint_a` | `Pubkey` | Token deposited by maker |
| `mint_b` | `Pubkey` | Token expected from taker |
| `receive` | `u64` | Remaining Token B needed (decreases with partial fills) |
| `deposit_amount` | `u64` | Original Token A deposited (immutable, for reference) |
| `expires_at` | `i64` | Unix timestamp deadline |
| `fee_bps` | `u16` | Fee in basis points |
| `bump` | `u8` | PDA bump |

### Instructions

**`make(seed, receive, amount, expires_at, fee_bps)`**
- Creates the escrow PDA and vault
- Deposits `amount` of Token A into the vault
- Validates `expires_at` is in the future and `fee_bps ≤ 10,000`

**`take(fill_amount)`**
- Validates escrow is not expired and `0 < fill_amount ≤ remaining receive`
- Computes proportional Token A: `(fill_amount × vault.amount) / remaining_receive`
- Transfers `fill_amount - fee` of Token B to maker, fee to treasury
- On final fill (fully consumed): closes vault and escrow, returns rent to maker

**`refund`**
- Maker-only — returns Token A from vault, closes vault and escrow

## Getting Started

### Prerequisites

- [Rust](https://www.rust-lang.org/tools/install)
- [Solana CLI](https://docs.solana.com/cli/install-solana-cli-tools)
- [Anchor](https://www.anchor-lang.com/docs/installation)
- [Node.js](https://nodejs.org/) & [Yarn](https://yarnpkg.com/)

### Installation

```bash
git clone <repository-url>
cd blueshift_anchor_escrow
yarn install
anchor build
```

### Testing

29 tests covering make, take, refund, cross-instruction lifecycle, expiry, fees, and partial fills.

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
