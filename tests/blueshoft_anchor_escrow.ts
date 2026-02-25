import * as anchor from "@coral-xyz/anchor";
import { Program, AnchorError } from "@coral-xyz/anchor";
import { BlueshiftAnchorEscrow } from "../target/types/blueshift_anchor_escrow";
import {
  createMint,
  getAssociatedTokenAddress,
  getOrCreateAssociatedTokenAccount,
  mintTo,
  getAccount,
  TOKEN_PROGRAM_ID,
  ASSOCIATED_TOKEN_PROGRAM_ID,
} from "@solana/spl-token";
import { BN } from "bn.js";
import assert from "assert";

// Type alias — BN is a class (value), InstanceType<> extracts its instance type
type BNType = InstanceType<typeof BN>;

// ─────────────────────────────────────────────────────────────────────────────
// SHARED HELPER
// ─────────────────────────────────────────────────────────────────────────────

/**
 * Derive the Escrow PDA — mirrors the Rust seeds:
 *   seeds = [b"escrow", maker.key().as_ref(), seed.to_le_bytes().as_ref()]
 */
function deriveEscrowPda(
  makerKey: anchor.web3.PublicKey,
  seed: BNType,
  programId: anchor.web3.PublicKey
): anchor.web3.PublicKey {
  const [pda] = anchor.web3.PublicKey.findProgramAddressSync(
    [
      Buffer.from("escrow"),
      makerKey.toBuffer(),
      seed.toArrayLike(Buffer, "le", 8), // u64 little-endian, 8 bytes — must match Rust
    ],
    programId
  );
  return pda;
}

// ─────────────────────────────────────────────────────────────────────────────
// DESCRIBE: MAKE INSTRUCTION
// ─────────────────────────────────────────────────────────────────────────────
describe("make instruction", () => {
  const provider = anchor.AnchorProvider.env();
  anchor.setProvider(provider);

  const program = anchor.workspace
    .BlueshiftAnchorEscrow as Program<BlueshiftAnchorEscrow>;

  // The provider wallet acts as the maker and signs automatically via .rpc()
  const maker = provider.wallet;

  // A separate payer to fund mint creation — keeps maker's role clean
  const payer = anchor.web3.Keypair.generate();

  // Token mints — set up once in before()
  let mintA: anchor.web3.PublicKey;
  let mintB: anchor.web3.PublicKey;

  // Maker's ATA for mintA — the source of tokens for all make calls
  let makerAtaA: anchor.web3.PublicKey;

  // 2000 tokens (6 decimals)
  const TOTAL_MINTED = 2_000_000_000n;

  const confirmTx = async (signature: string) => {
    const latestBlockhash = await provider.connection.getLatestBlockhash();
    await provider.connection.confirmTransaction({
      signature,
      ...latestBlockhash,
    });
  };

  // ── makeTx: reusable helper to call the make instruction ─────────────────
  // In Anchor 0.31, escrow, vault, and makerAtaA are auto-resolved from their
  // PDA seeds defined in the IDL. We only need to pass accounts Anchor can't
  // figure out on its own: maker, mintA, mintB, tokenProgram.
  const makeTx = async (seed: BNType, receive: BNType, amount: BNType) => {
    const escrowPda = deriveEscrowPda(maker.publicKey, seed, program.programId);
    const vault = await getAssociatedTokenAddress(mintA, escrowPda, true);

    await program.methods
      .make(seed, receive, amount)
      .accounts({
        maker: maker.publicKey,
        mintA,
        mintB,
        tokenProgram: TOKEN_PROGRAM_ID,
      } as any) // Anchor 0.31 auto-resolves escrow, vault, makerAtaA from IDL seeds
      .rpc();

    return { escrowPda, vault };
  };

  // ── BEFORE: shared one-time setup ────────────────────────────────────────
  before(async () => {
    const airdropSig = await provider.connection.requestAirdrop(
      payer.publicKey,
      10 * anchor.web3.LAMPORTS_PER_SOL
    );
    await confirmTx(airdropSig);

    mintA = await createMint(provider.connection, payer, payer.publicKey, null, 6);
    mintB = await createMint(provider.connection, payer, payer.publicKey, null, 6);

    makerAtaA = (
      await getOrCreateAssociatedTokenAccount(
        provider.connection, payer, mintA, maker.publicKey
      )
    ).address;

    await mintTo(provider.connection, payer, mintA, makerAtaA, payer.publicKey, TOTAL_MINTED);
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 1 — Happy Path: escrow created, vault funded, state stored
  // ───────────────────────────────────────────────────────────────────────────
  it("happy path: escrow created, vault funded, state stored", async () => {
    const seed = new BN(1);
    const receive = new BN(200_000);
    const amount = new BN(500_000);

    const makerAtaABefore = await getAccount(provider.connection, makerAtaA);
    const balanceBefore = makerAtaABefore.amount;

    const { escrowPda, vault } = await makeTx(seed, receive, amount);

    // [1] vault holds exactly the deposited amount
    const vaultAccount = await getAccount(provider.connection, vault);
    assert.equal(vaultAccount.amount, BigInt(amount.toString()),
      "Vault should hold exactly the deposited amount");

    // [2] maker's ATA decreased by amount
    const makerAtaAAfter = await getAccount(provider.connection, makerAtaA);
    assert.equal(makerAtaAAfter.amount, balanceBefore - BigInt(amount.toString()),
      "Maker's ATA should have decreased by the deposited amount");

    // [3] escrow state is correctly stored on-chain
    const escrow = await program.account.escrow.fetch(escrowPda);
    assert.ok(escrow.maker.equals(maker.publicKey), "escrow.maker mismatch");
    assert.ok(escrow.mintA.equals(mintA), "escrow.mintA mismatch");
    assert.ok(escrow.mintB.equals(mintB), "escrow.mintB mismatch");
    assert.equal(escrow.seed.toString(), seed.toString(), "escrow.seed mismatch");
    assert.equal(escrow.receive.toString(), receive.toString(), "escrow.receive mismatch");

    // [4] vault is owned/controlled by the escrow PDA — NOT the maker
    assert.ok(vaultAccount.owner.equals(escrowPda),
      "Vault must be owned by the escrow PDA, not the maker");
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 2 - amount = 0 must fail (InvalidAmount)
  // ───────────────────────────────────────────────────────────────────────────
  it("Rejects amount = 0 with InvalidAmount", async () => {
    try {
      await makeTx(new BN(2), new BN(100_000), new BN(0));
      assert.fail("Transaction should have failed with InvalidAmount but succeeded");
    } catch (err) {
      assert.ok(err instanceof AnchorError, "Expected an AnchorError");
      assert.strictEqual(err.error.errorCode.code, "InvalidAmount");
    }
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 3 — receive = 0 must fail (InvalidAmount)
  // ───────────────────────────────────────────────────────────────────────────
  it("Rejects receive = 0 with InvalidAmount", async () => {
    try {
      await makeTx(new BN(3), new BN(0), new BN(500_000));
      assert.fail("Transaction should have failed with InvalidAmount but succeeded");
    } catch (err) {
      assert.ok(err instanceof AnchorError, "Expected an AnchorError");
      assert.strictEqual(err.error.errorCode.code, "InvalidAmount");
    }
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 4 — Two different seeds produce two independent escrows
  // ───────────────────────────────────────────────────────────────────────────
  it("two different seeds create two independent escrows", async () => {
    const receive = new BN(100_000);
    const amount = new BN(300_000);

    const { escrowPda: escrowA, vault: vaultA } = await makeTx(new BN(10), receive, amount);
    const { escrowPda: escrowB, vault: vaultB } = await makeTx(new BN(20), receive, amount);

    assert.ok(!escrowA.equals(escrowB), "Escrow PDAs must differ");
    assert.ok(!vaultA.equals(vaultB), "Vault addresses must differ");

    const [accA, accB] = await Promise.all([
      getAccount(provider.connection, vaultA),
      getAccount(provider.connection, vaultB),
    ]);
    assert.equal(accA.amount, BigInt(amount.toString()), "VaultA balance mismatch");
    assert.equal(accB.amount, BigInt(amount.toString()), "VaultB balance mismatch");
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 5 — Duplicate seed reuse must fail (account already in use)
  // ───────────────────────────────────────────────────────────────────────────
  it("same maker + same seed cannot create a second escrow", async () => {
    try {
      // seed=1 was used in Test 1 — reuse it intentionally
      await makeTx(new BN(1), new BN(200_000), new BN(100_000));
      assert.fail("Transaction should have failed — escrow PDA already exists");
    } catch (err) {
      const errMsg = err.toString().toLowerCase();
      const isAlreadyInUse =
        errMsg.includes("already in use") ||
        errMsg.includes("0x0") ||
        errMsg.includes("custom program error");
      assert.ok(isAlreadyInUse, `Expected 'already in use' error but got: ${err.toString()}`);
    }
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 6  — Insufficient token balance fails at token transfer
  // ───────────────────────────────────────────────────────────────────────────
  it("insufficient token balance fails at token transfer", async () => {
    try {
      await makeTx(new BN(6), new BN(100_000), new BN("999999999999"));
      assert.fail("Transaction should have failed due to insufficient token balance");
    } catch (err) {
      const errStr = err.toString();
      const isInsufficientFunds =
        errStr.includes("0x1") ||
        errStr.toLowerCase().includes("insufficient") ||
        errStr.includes("custom program error: 0x1");
      assert.ok(isInsufficientFunds, `Expected insufficient funds error but got: ${errStr}`);
    }
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// DESCRIBE: TAKE INSTRUCTION
// ─────────────────────────────────────────────────────────────────────────────
//
// The take flow:
//   1. Taker sends escrow.receive tokens of mintB  → maker_ata_b
//   2. Vault (mintA tokens) → taker_ata_a, then vault is closed
//   3. Escrow PDA is closed, rent refunded to maker
//
// Anchor 0.31 auto-resolution for take:
//   - escrow  → PDA from [escrow, maker, seed]   (resolved via relations from escrow data)
//   - maker   → resolved via relations: ["escrow"]
//   - vault   → ATA(mint_a, escrow)
//   - taker_ata_a → ATA(mint_a, taker)
//   - maker_ata_b → ATA(mint_b, maker)
//   We must provide: taker, mintA, mintB, takerAtaB, tokenProgram
// ─────────────────────────────────────────────────────────────────────────────
describe("take instruction", () => {
  const provider = anchor.AnchorProvider.env();
  anchor.setProvider(provider);

  const program = anchor.workspace
    .BlueshiftAnchorEscrow as Program<BlueshiftAnchorEscrow>;

  const maker = provider.wallet;
  const taker = anchor.web3.Keypair.generate();
  const payer = anchor.web3.Keypair.generate();

  let mintA: anchor.web3.PublicKey;
  let mintB: anchor.web3.PublicKey;
  let makerAtaA: anchor.web3.PublicKey;
  let takerAtaB: anchor.web3.PublicKey;

  // Seeds 100–199 reserved for take suite (no collision with make suite 1–20)
  const TAKE_SEED = new BN(100);
  const DEPOSIT_AMOUNT = new BN(500_000);
  const RECEIVE_AMOUNT = new BN(200_000);

  const confirmTx = async (sig: string) => {
    const bh = await provider.connection.getLatestBlockhash();
    await provider.connection.confirmTransaction({ signature: sig, ...bh });
  };

  // ── Helper: create a fresh make() escrow ─────────────────────────────────
  const setupEscrow = async (seed: BNType, receive: BNType, amount: BNType) => {
    const escrowPda = deriveEscrowPda(maker.publicKey, seed, program.programId);
    const vault = await getAssociatedTokenAddress(mintA, escrowPda, true);

    await program.methods
      .make(seed, receive, amount)
      .accounts({
        maker: maker.publicKey,
        mintA,
        mintB,
        tokenProgram: TOKEN_PROGRAM_ID,
      } as any)
      .rpc();

    return { escrowPda, vault };
  };

  // ── Helper: call take ─────────────────────────────────────────────────────
  const takeTx = async (
    escrowPda: anchor.web3.PublicKey,
    opts: {
      takerKp?: anchor.web3.Keypair;
      mintAOver?: anchor.web3.PublicKey;
      mintBOver?: anchor.web3.PublicKey;
      makerOver?: anchor.web3.PublicKey;
    } = {}
  ) => {
    const aTaker = opts.takerKp ?? taker;
    const aMintA = opts.mintAOver ?? mintA;
    const aMintB = opts.mintBOver ?? mintB;
    const aMaker = opts.makerOver ?? maker.publicKey;

    // Derive accounts the test needs for assertions
    const vault = await getAssociatedTokenAddress(aMintA, escrowPda, true);
    const takerAtaA = await getAssociatedTokenAddress(aMintA, aTaker.publicKey);
    const aTakerAtaB = await getAssociatedTokenAddress(aMintB, aTaker.publicKey);
    const makerAtaB = await getAssociatedTokenAddress(aMintB, aMaker);

    await program.methods
      .take()
      .accounts({
        taker: aTaker.publicKey,
        maker: aMaker,         // Anchor needs maker so it can derive makerAtaB
        escrow: escrowPda,      // needed so Anchor reads escrow.maker via relations
        mintA: aMintA,
        mintB: aMintB,
        vault,                    // ATA(mintA, escrow)
        takerAtaA,                // ATA(mintA, taker)  — init_if_needed target
        takerAtaB: aTakerAtaB,    // ATA(mintB, taker)  — source of payment, mut required
        makerAtaB,                // ATA(mintB, maker)  — init_if_needed target
        associatedTokenProgram: ASSOCIATED_TOKEN_PROGRAM_ID,
        tokenProgram: TOKEN_PROGRAM_ID,
        systemProgram: anchor.web3.SystemProgram.programId,
      } as any)
      .signers([aTaker])
      .rpc();

    return { vault, takerAtaA, makerAtaB, takerAtaB: aTakerAtaB };
  };

  // ── BEFORE ────────────────────────────────────────────────────────────────
  before(async () => {
    const [payerSig, takerSig] = await Promise.all([
      provider.connection.requestAirdrop(payer.publicKey, 10 * anchor.web3.LAMPORTS_PER_SOL),
      provider.connection.requestAirdrop(taker.publicKey, 10 * anchor.web3.LAMPORTS_PER_SOL),
    ]);
    await confirmTx(payerSig);
    await confirmTx(takerSig);

    mintA = await createMint(provider.connection, payer, payer.publicKey, null, 6);
    mintB = await createMint(provider.connection, payer, payer.publicKey, null, 6);

    makerAtaA = (await getOrCreateAssociatedTokenAccount(
      provider.connection, payer, mintA, maker.publicKey
    )).address;
    await mintTo(provider.connection, payer, mintA, makerAtaA, payer.publicKey, 10_000_000_000n);

    // taker_ata_b is `mut` (not init_if_needed) in take.rs — must exist + be funded before take
    takerAtaB = (await getOrCreateAssociatedTokenAccount(
      provider.connection, payer, mintB, taker.publicKey
    )).address;
    await mintTo(provider.connection, payer, mintB, takerAtaB, payer.publicKey, 10_000_000_000n);
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 7 — Happy path: full exchange, vault + escrow closed
  // ───────────────────────────────────────────────────────────────────────────
  it("happy path: full exchange, vault closed, escrow closed", async () => {
    const takerBBefore = (await getAccount(provider.connection, takerAtaB)).amount;

    const { escrowPda } = await setupEscrow(TAKE_SEED, RECEIVE_AMOUNT, DEPOSIT_AMOUNT);
    const { vault, takerAtaA, makerAtaB } = await takeTx(escrowPda);

    // [1] taker received mintA from vault
    const takerAtaAAcc = await getAccount(provider.connection, takerAtaA);
    assert.equal(takerAtaAAcc.amount, BigInt(DEPOSIT_AMOUNT.toString()),
      "Taker should receive all mintA from vault");

    // [2] maker received mintB from taker
    const makerAtaBAcc = await getAccount(provider.connection, makerAtaB);
    assert.equal(makerAtaBAcc.amount, BigInt(RECEIVE_AMOUNT.toString()),
      "Maker should receive agreed mintB amount");

    // [3] taker's mintB decreased by receive amount
    const takerAtaBAfter = (await getAccount(provider.connection, takerAtaB)).amount;
    assert.equal(takerAtaBAfter, takerBBefore - BigInt(RECEIVE_AMOUNT.toString()),
      "Taker mintB balance should decrease by receive amount");

    // [4] vault closed
    try {
      await getAccount(provider.connection, vault);
      assert.fail("Vault should be closed");
    } catch (err) {
      assert.ok(err.message?.includes("could not find account") ||
        err.name === "TokenAccountNotFoundError");
    }

    // [5] escrow PDA closed
    const escrowInfo = await provider.connection.getAccountInfo(escrowPda);
    assert.strictEqual(escrowInfo, null, "Escrow PDA should be closed");
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 8 — Wrong maker account (InvalidMaker)
  // ───────────────────────────────────────────────────────────────────────────
  it("wrong maker account is rejected (ConstraintSeeds or InvalidMaker)", async () => {
    const { escrowPda } = await setupEscrow(new BN(101), RECEIVE_AMOUNT, DEPOSIT_AMOUNT);
    const fakeMaker = anchor.web3.Keypair.generate();

    try {
      await takeTx(escrowPda, { makerOver: fakeMaker.publicKey });
      assert.fail("Expected rejection but transaction succeeded");
    } catch (err) {
      // Anchor evaluates seeds constraints before has_one constraints.
      // Re-deriving the escrow PDA with the fake maker gives a different address
      // than the actual escrow → ConstraintSeeds fires first. In some Anchor
      // versions has_one may fire instead. Both mean the same thing: wrong maker.
      assert.ok(err instanceof AnchorError, `Expected AnchorError, got: ${err}`);
      const code = err.error.errorCode.code;
      assert.ok(
        code === "ConstraintSeeds" || code === "InvalidMaker",
        `Expected ConstraintSeeds or InvalidMaker, got: ${code}`
      );
    }
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 9  — Wrong mint_a (InvalidMintA)
  // ───────────────────────────────────────────────────────────────────────────
  it("wrong mint_a is rejected (AccountNotInitialized or InvalidMintA)", async () => {
    const { escrowPda } = await setupEscrow(new BN(102), RECEIVE_AMOUNT, DEPOSIT_AMOUNT);
    const fakeMintA = await createMint(provider.connection, payer, payer.publicKey, null, 6);

    try {
      await takeTx(escrowPda, { mintAOver: fakeMintA });
      assert.fail("Expected rejection but transaction succeeded");
    } catch (err) {
      // The vault is derived from mintA. When we pass fakeMintA, the vault
      // ATA for fakeMintA + escrow doesn't exist on-chain → AccountNotInitialized
      // fires BEFORE the has_one = mint_a constraint can run.
      // Both mean the same thing: wrong mint_a was rejected.
      assert.ok(err instanceof AnchorError, `Expected AnchorError, got: ${err}`);
      const code = err.error.errorCode.code;
      assert.ok(
        code === "AccountNotInitialized" || code === "InvalidMintA",
        `Expected AccountNotInitialized or InvalidMintA, got: ${code}`
      );
    }
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 10 — Wrong mint_b (InvalidMintB)
  // ───────────────────────────────────────────────────────────────────────────
  it("wrong mint_b is rejected with InvalidMintB", async () => {
    const { escrowPda } = await setupEscrow(new BN(103), RECEIVE_AMOUNT, DEPOSIT_AMOUNT);
    const fakeMintB = await createMint(provider.connection, payer, payer.publicKey, null, 6);

    // Create taker's ATA for fakeMintB (taker_ata_b must exist before take)
    await getOrCreateAssociatedTokenAccount(
      provider.connection, taker, fakeMintB, taker.publicKey
    );

    try {
      await takeTx(escrowPda, { mintBOver: fakeMintB });
      assert.fail("Expected InvalidMintB but succeeded");
    } catch (err) {
      assert.ok(err instanceof AnchorError, `Expected AnchorError, got: ${err}`);
      assert.strictEqual(err.error.errorCode.code, "InvalidMintB");
    }
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 11 — Insufficient mintB balance (token program error)
  // ───────────────────────────────────────────────────────────────────────────
  it("insufficient token B balance fails with token program error", async () => {
    const { escrowPda } = await setupEscrow(new BN(104), RECEIVE_AMOUNT, DEPOSIT_AMOUNT);

    const poorTaker = anchor.web3.Keypair.generate();
    await confirmTx(await provider.connection.requestAirdrop(
      poorTaker.publicKey, 5 * anchor.web3.LAMPORTS_PER_SOL
    ));

    const poorTakerAtaB = (await getOrCreateAssociatedTokenAccount(
      provider.connection, poorTaker, mintB, poorTaker.publicKey
    )).address;
    await mintTo(provider.connection, payer, mintB, poorTakerAtaB, payer.publicKey, 1n);

    try {
      await takeTx(escrowPda, { takerKp: poorTaker });
      assert.fail("Expected insufficient funds error");
    } catch (err) {
      const errStr = err.toString();
      assert.ok(errStr.includes("0x1") || errStr.toLowerCase().includes("insufficient"),
        `Expected insufficient funds error but got: ${errStr}`);
    }
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 12  — Zero mintB balance
  // ───────────────────────────────────────────────────────────────────────────
  it("zero token B balance fails", async () => {
    const { escrowPda } = await setupEscrow(new BN(105), RECEIVE_AMOUNT, DEPOSIT_AMOUNT);

    const emptyTaker = anchor.web3.Keypair.generate();
    await confirmTx(await provider.connection.requestAirdrop(
      emptyTaker.publicKey, 5 * anchor.web3.LAMPORTS_PER_SOL
    ));
    // Create ATA but mint 0 tokens
    await getOrCreateAssociatedTokenAccount(
      provider.connection, emptyTaker, mintB, emptyTaker.publicKey
    );

    try {
      await takeTx(escrowPda, { takerKp: emptyTaker });
      assert.fail("Expected insufficient funds error");
    } catch (err) {
      const errStr = err.toString();
      assert.ok(errStr.includes("0x1") || errStr.toLowerCase().includes("insufficient"),
        `Expected insufficient funds error but got: ${errStr}`);
    }
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// DESCRIBE: REFUND INSTRUCTION
// ─────────────────────────────────────────────────────────────────────────────
//
// The refund flow:
//   Only the original maker can call refund:
//   1. Vault tokens → maker_ata_a (deposited tokens returned)
//   2. Vault closed (rent → maker)
//   3. Escrow PDA closed (rent → maker)
//
// Anchor 0.31 auto-resolution for refund:
//   - escrow    → PDA (seeds: [escrow, maker, seed])
//   - vault     → ATA(mint_a, escrow)
//   - maker_ata_a → ATA(mint_a, maker)
//   We must provide: maker (signer), mintA, tokenProgram
// ─────────────────────────────────────────────────────────────────────────────
describe("refund instruction", () => {
  const provider = anchor.AnchorProvider.env();
  anchor.setProvider(provider);

  const program = anchor.workspace
    .BlueshiftAnchorEscrow as Program<BlueshiftAnchorEscrow>;

  const maker = provider.wallet;
  const payer = anchor.web3.Keypair.generate();

  let mintA: anchor.web3.PublicKey;
  let mintB: anchor.web3.PublicKey;
  let makerAtaA: anchor.web3.PublicKey;

  const DEPOSIT_AMOUNT = new BN(500_000);
  const RECEIVE_AMOUNT = new BN(200_000);

  // Seeds 200–299 reserved for refund suite
  const confirmTx = async (sig: string) => {
    const bh = await provider.connection.getLatestBlockhash();
    await provider.connection.confirmTransaction({ signature: sig, ...bh });
  };

  const setupEscrow = async (seed: BNType, receive: BNType, amount: BNType) => {
    const escrowPda = deriveEscrowPda(maker.publicKey, seed, program.programId);
    const vault = await getAssociatedTokenAddress(mintA, escrowPda, true);

    await program.methods
      .make(seed, receive, amount)
      .accounts({
        maker: maker.publicKey,
        mintA,
        mintB,
        tokenProgram: TOKEN_PROGRAM_ID,
      } as any)
      .rpc();

    return { escrowPda, vault };
  };

  const refundTx = async (
    escrowPda: anchor.web3.PublicKey,
    opts: { mintAOver?: anchor.web3.PublicKey } = {}
  ) => {
    const aMintA = opts.mintAOver ?? mintA;
    const vault = await getAssociatedTokenAddress(aMintA, escrowPda, true);

    await program.methods
      .refund()
      .accounts({
        maker: maker.publicKey,
        escrow: escrowPda,        // needed so Anchor can verify seeds & read state
        mintA: aMintA,
        vault,                      // ATA(mintA, escrow)
        makerAtaA: await getAssociatedTokenAddress(aMintA, maker.publicKey), // init_if_needed target
        associatedTokenProgram: ASSOCIATED_TOKEN_PROGRAM_ID,
        tokenProgram: TOKEN_PROGRAM_ID,
        systemProgram: anchor.web3.SystemProgram.programId,
      } as any)
      .rpc();

    return { vault };
  };

  // ── BEFORE ────────────────────────────────────────────────────────────────
  before(async () => {
    await confirmTx(await provider.connection.requestAirdrop(
      payer.publicKey, 10 * anchor.web3.LAMPORTS_PER_SOL
    ));

    mintA = await createMint(provider.connection, payer, payer.publicKey, null, 6);
    mintB = await createMint(provider.connection, payer, payer.publicKey, null, 6);

    makerAtaA = (await getOrCreateAssociatedTokenAccount(
      provider.connection, payer, mintA, maker.publicKey
    )).address;
    await mintTo(provider.connection, payer, mintA, makerAtaA, payer.publicKey, 10_000_000_000n);
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 13 — Happy path: tokens returned, vault + escrow closed
  // ───────────────────────────────────────────────────────────────────────────
  it("happy path: tokens returned, vault and escrow closed", async () => {
    const balanceBefore = (await getAccount(provider.connection, makerAtaA)).amount;

    const { escrowPda } = await setupEscrow(new BN(200), RECEIVE_AMOUNT, DEPOSIT_AMOUNT);

    // Sanity: tokens left maker's ATA on make
    const balanceAfterMake = (await getAccount(provider.connection, makerAtaA)).amount;
    assert.equal(balanceAfterMake, balanceBefore - BigInt(DEPOSIT_AMOUNT.toString()),
      "Sanity: maker ATA should decrease after make");

    const { vault } = await refundTx(escrowPda);

    // [1] tokens restored
    const balanceAfterRefund = (await getAccount(provider.connection, makerAtaA)).amount;
    assert.equal(balanceAfterRefund, balanceBefore, "Maker ATA should be fully restored");

    // [2] vault closed
    try {
      await getAccount(provider.connection, vault);
      assert.fail("Vault should be closed after refund");
    } catch (err) {
      assert.ok(err.message?.includes("could not find account") ||
        err.name === "TokenAccountNotFoundError");
    }

    // [3] escrow closed
    const escrowInfo = await provider.connection.getAccountInfo(escrowPda);
    assert.strictEqual(escrowInfo, null, "Escrow PDA should be closed");
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 14 — Non-maker cannot call refund
  // ───────────────────────────────────────────────────────────────────────────
  it("non-maker cannot call refund", async () => {
    const { escrowPda } = await setupEscrow(new BN(201), RECEIVE_AMOUNT, DEPOSIT_AMOUNT);

    const attacker = anchor.web3.Keypair.generate();
    await confirmTx(await provider.connection.requestAirdrop(
      attacker.publicKey, 2 * anchor.web3.LAMPORTS_PER_SOL
    ));

    const attackerAtaA = (await getOrCreateAssociatedTokenAccount(
      provider.connection, attacker, mintA, attacker.publicKey
    )).address;
    const vault = await getAssociatedTokenAddress(mintA, escrowPda, true);

    try {
      await program.methods
        .refund()
        .accounts({
          maker: attacker.publicKey,
          escrow: escrowPda,
          mintA,
          vault,
          makerAtaA: attackerAtaA,
          associatedTokenProgram: ASSOCIATED_TOKEN_PROGRAM_ID,
          tokenProgram: TOKEN_PROGRAM_ID,
          systemProgram: anchor.web3.SystemProgram.programId,
        } as any)
        .signers([attacker])
        .rpc();
      assert.fail("Non-maker should not be able to call refund");
    } catch (err) {
      const errStr = err.toString();
      const isExpected =
        (err instanceof AnchorError && err.error.errorCode.code === "InvalidMaker") ||
        errStr.includes("ConstraintSeeds") ||
        errStr.includes("Error Code");
      assert.ok(isExpected, `Expected refund rejection, got: ${errStr}`);
    }
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 15 — Wrong mint_a (InvalidMintA)
  // ───────────────────────────────────────────────────────────────────────────
  it("wrong mint_a is rejected (AccountNotInitialized or InvalidMintA)", async () => {
    const { escrowPda } = await setupEscrow(new BN(202), RECEIVE_AMOUNT, DEPOSIT_AMOUNT);
    const fakeMintA = await createMint(provider.connection, payer, payer.publicKey, null, 6);

    await getOrCreateAssociatedTokenAccount(
      provider.connection, payer, fakeMintA, maker.publicKey
    );

    try {
      await refundTx(escrowPda, { mintAOver: fakeMintA });
      assert.fail("Expected rejection but transaction succeeded");
    } catch (err) {
      // Same as TAKE-3: vault for fakeMintA doesn't exist → AccountNotInitialized
      // fires before the has_one = mint_a constraint can run.
      assert.ok(err instanceof AnchorError, `Expected AnchorError, got: ${err}`);
      const code = err.error.errorCode.code;
      assert.ok(
        code === "AccountNotInitialized" || code === "InvalidMintA",
        `Expected AccountNotInitialized or InvalidMintA, got: ${code}`
      );
    }
  });

  // ───────────────────────────────────────────────────────────────────────────
  // TEST 16 — init_if_needed: refund works even if maker_ata_a already exists
  // ───────────────────────────────────────────────────────────────────────────
  it("init_if_needed handles pre-existing maker_ata_a correctly", async () => {
    const balanceBefore = (await getAccount(provider.connection, makerAtaA)).amount;
    const { escrowPda } = await setupEscrow(new BN(203), RECEIVE_AMOUNT, DEPOSIT_AMOUNT);

    const { vault } = await refundTx(escrowPda);

    // Tokens fully restored
    const balanceAfter = (await getAccount(provider.connection, makerAtaA)).amount;
    assert.equal(balanceAfter, balanceBefore, "Maker ATA balance should be restored");

    // Vault closed
    try {
      await getAccount(provider.connection, vault);
      assert.fail("Vault should be closed");
    } catch (err) {
      assert.ok(err.message?.includes("could not find account") ||
        err.name === "TokenAccountNotFoundError");
    }

    // Escrow closed
    const escrowInfo = await provider.connection.getAccountInfo(escrowPda);
    assert.strictEqual(escrowInfo, null, "Escrow PDA should be closed");
  });
});