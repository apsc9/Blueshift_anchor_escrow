import * as anchor from "@coral-xyz/anchor";
import { Program } from "@coral-xyz/anchor";
import { BlueshiftAnchorEscrow } from "../target/types/blueshift_anchor_escrow";
import {
  createMint,
  getAssociatedTokenAddress,
  getOrCreateAssociatedTokenAccount,
  mintTo,
  TOKEN_PROGRAM_ID,
  ASSOCIATED_TOKEN_PROGRAM_ID,
} from "@solana/spl-token";
import { BN } from "bn.js";

describe("blueshift_anchor_escrow", () => {
  // Configure the client to use the local cluster.
  const provider = anchor.AnchorProvider.env();
  anchor.setProvider(provider);

  const program = anchor.workspace.blueshiftAnchorEscrow as Program<BlueshiftAnchorEscrow>;

  const maker = provider.wallet; // The provider wallet is the maker
  const payer = anchor.web3.Keypair.generate(); // Payer for mint creation/airdrop

  let mintA: anchor.web3.PublicKey;
  let mintB: anchor.web3.PublicKey;
  let makerAtaA: anchor.web3.PublicKey;
  // let makerAtaB: anchor.web3.PublicKey; // Not needed for 'make' but usually for 'take'

  const seed = new BN(123456);

  before(async () => {
    // 1. Airdrop SOL to payer to fund mint creation
    const airdropTx = await provider.connection.requestAirdrop(
      payer.publicKey,
      10 * anchor.web3.LAMPORTS_PER_SOL
    );
    await confirmTx(airdropTx);

    // 2. Create Mint A and Mint B
    mintA = await createMint(
      provider.connection,
      payer,
      payer.publicKey,
      null,
      6
    );
    mintB = await createMint(
      provider.connection,
      payer,
      payer.publicKey,
      null,
      6
    );

    // 3. Create Maker's ATA for Mint A
    // We use the payer to pay for the account creation, but the owner is the provider.wallet (maker)
    makerAtaA = (
      await getOrCreateAssociatedTokenAccount(
        provider.connection,
        payer,
        mintA,
        maker.publicKey
      )
    ).address;

    // 4. Mint tokens to Maker's ATA A
    await mintTo(
      provider.connection,
      payer,
      mintA,
      makerAtaA,
      payer.publicKey,
      1000_000_000
    );
  });

  const confirmTx = async (signature: string) => {
    const latestBlockhash = await provider.connection.getLatestBlockhash();
    await provider.connection.confirmTransaction({
      signature,
      ...latestBlockhash,
    });
  };

  it("Is initialized (Make Escrow)!", async () => {
    const receive = new BN(100);
    const amount = new BN(500);

    // Derive Escrow PDA
    // seeds = [b"escrow", maker.key().as_ref(), seed.to_le_bytes().as_ref()]
    const [escrowPda] = anchor.web3.PublicKey.findProgramAddressSync(
      [
        Buffer.from("escrow"),
        maker.publicKey.toBuffer(),
        seed.toArrayLike(Buffer, "le", 8),
      ],
      program.programId
    );

    // Derive Vault PDA
    // The vault is an ATA owned by the Escrow PDA for Mint A
    const vault = await getAssociatedTokenAddress(mintA, escrowPda, true);

    console.log("Escrow PDA:", escrowPda.toBase58());
    console.log("Vault PDA:", vault.toBase58());

    const tx = await program.methods
      .make(seed, receive, amount)
      .accounts({
        maker: maker.publicKey,
        escrow: escrowPda,
        mintA: mintA,
        mintB: mintB,
        makerAtaA: makerAtaA,
        vault: vault,
        associatedTokenProgram: ASSOCIATED_TOKEN_PROGRAM_ID,
        tokenProgram: TOKEN_PROGRAM_ID,
        systemProgram: anchor.web3.SystemProgram.programId,
      })
      .signers([]) // maker is the provider wallet, so it signs automatically
      .rpc();

    console.log("Your transaction signature", tx);
  });
});