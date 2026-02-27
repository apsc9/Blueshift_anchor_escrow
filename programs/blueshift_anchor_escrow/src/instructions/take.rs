use anchor_lang::prelude::*;
use anchor_spl::token_interface::{Mint, TokenAccount, TokenInterface, transfer_checked, TransferChecked, close_account, CloseAccount};
use anchor_spl::associated_token::AssociatedToken;
use crate::state::Escrow;
use crate::errors::EscrowError;


#[derive(Accounts)]
pub struct Take<'info> {
    #[account(mut)]
    pub taker: Signer<'info>,
    #[account(mut)]
    pub maker: SystemAccount<'info>,

    // ── KEY CHANGE for partial fills ──────────────────────────────────────
    //
    // Previously this had `close = maker`, which would automatically close
    // the escrow account at the end of every take instruction. With partial
    // fills, the escrow must survive between fills — we only close it when
    // the remaining receive drops to 0. So we removed `close = maker` and
    // instead call `self.escrow.close(maker)` manually in the handler when
    // the fill is the final one.
    #[account(
        mut,
        seeds = [b"escrow", maker.key().as_ref(), escrow.seed.to_le_bytes().as_ref()],
        bump = escrow.bump,
        has_one = maker @ EscrowError::InvalidMaker,
        has_one = mint_a @ EscrowError::InvalidMintA,
        has_one = mint_b @ EscrowError::InvalidMintB,
    )]
    pub escrow: Box<Account<'info, Escrow>>,
    pub mint_a: Box<InterfaceAccount<'info, Mint>>,
    pub mint_b: Box<InterfaceAccount<'info, Mint>>,
    #[account(
        mut,
        associated_token::mint = mint_a,
        associated_token::authority = escrow,
        associated_token::token_program = token_program,
    )]
    pub vault: Box<InterfaceAccount<'info, TokenAccount>>,
    
    #[account(
        init_if_needed,
        payer=taker,
        associated_token::mint = mint_a,
        associated_token::authority = taker,
        associated_token::token_program = token_program,
    )]
    pub taker_ata_a: Box<InterfaceAccount<'info, TokenAccount>>,
    #[account(
        mut,
        associated_token::mint= mint_b,
        associated_token::authority = taker,
        associated_token::token_program = token_program,
    )]
    pub taker_ata_b: Box<InterfaceAccount<'info, TokenAccount>>,
    #[account(
        init_if_needed,
        payer=taker,
        associated_token::mint = mint_b,
        associated_token::authority = maker,
        associated_token::token_program = token_program,
    )]
    pub maker_ata_b: Box<InterfaceAccount<'info, TokenAccount>>,

    /// CHECK: This is a PDA used only as the authority/owner for treasury token accounts.
    #[account(
        seeds = [b"treasury"],
        bump,
    )]
    pub treasury: AccountInfo<'info>,
    #[account(
        init_if_needed,
        payer = taker,
        associated_token::mint = mint_b,
        associated_token::authority = treasury,
        associated_token::token_program = token_program,
    )]
    pub treasury_ata_b: Box<InterfaceAccount<'info, TokenAccount>>,

    //programs
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub token_program: Interface<'info, TokenInterface>,
    pub system_program: Program<'info, System>
}

impl<'info> Take<'info> {

    // ── Transfer token_B from taker → maker (minus fee) + treasury ───────
    //
    // With partial fills, the taker pays `fill_amount` of token_B (not the
    // full `escrow.receive`). The fee is calculated on fill_amount, not on
    // the total receive — each fill pays its proportional fee.
    //
    //   fee          = (fill_amount × fee_bps) / 10_000
    //   maker_amount = fill_amount - fee
    //
    fn transfer_to_maker(&mut self, fill_amount: u64) -> Result<()> {
        let fee_bps = self.escrow.fee_bps as u64;

        // fee is proportional to the fill, not the total receive
        let fee = fill_amount
            .checked_mul(fee_bps)
            .unwrap()
            .checked_div(10_000)
            .unwrap();
        let maker_amount = fill_amount.checked_sub(fee).unwrap();

        // transfer (fill_amount - fee) to maker
        transfer_checked(
            CpiContext::new(
                self.token_program.to_account_info(),
                TransferChecked {
                    from: self.taker_ata_b.to_account_info(),
                    to: self.maker_ata_b.to_account_info(),
                    mint: self.mint_b.to_account_info(),
                    authority: self.taker.to_account_info(),
                },
            ),
            maker_amount,
            self.mint_b.decimals,
        )?;

        // transfer fee to treasury (skip if fee is 0)
        if fee > 0 {
            transfer_checked(
                CpiContext::new(
                    self.token_program.to_account_info(),
                    TransferChecked {
                        from: self.taker_ata_b.to_account_info(),
                        to: self.treasury_ata_b.to_account_info(),
                        mint: self.mint_b.to_account_info(),
                        authority: self.taker.to_account_info(),
                    },
                ),
                fee,
                self.mint_b.decimals,
            )?;
        }

        Ok(())
    }

    // ── Transfer proportional token_A from vault → taker ─────────────────
    //
    // THE RATIO MATH (derived from the original exchange rate):
    //
    //   The maker's original terms: deposit_amount token_A ↔ receive token_B
    //   Exchange rate: 1 token_B = (deposit_amount / receive) token_A
    //
    //   For a partial fill of fill_amount token_B:
    //     token_a_to_release = (fill_amount × deposit_amount) / receive
    //
    //   We use u128 for the intermediate multiplication to prevent overflow
    //   (two u64s multiplied can exceed u64::MAX).
    //
    //   On the LAST fill (fill_amount == remaining receive), this simplifies
    //   to releasing whatever is left in the vault — avoiding rounding dust.
    //
    fn withdraw_from_vault(&mut self, token_a_amount: u64) -> Result<()> {
        let signer_seeds: [&[&[u8]]; 1] = [&[
            b"escrow",
            self.maker.to_account_info().key.as_ref(),
            &self.escrow.seed.to_le_bytes()[..],
            &[self.escrow.bump],
        ]];

        transfer_checked(
            CpiContext::new_with_signer(
                self.token_program.to_account_info(),
                TransferChecked {
                    from: self.vault.to_account_info(),
                    to: self.taker_ata_a.to_account_info(),
                    mint: self.mint_a.to_account_info(),
                    authority: self.escrow.to_account_info(),
                },
                &signer_seeds,
            ),
            token_a_amount,
            self.mint_a.decimals,
        )?;

        Ok(())
    }

    // ── Close vault + escrow (only on final fill) ────────────────────────
    //
    // Called only when fill_amount == remaining receive (full consumption).
    // Closes the vault (returns rent to maker) and then closes the escrow
    // account itself (also returns rent to maker).
    //
    fn close_vault_and_escrow(&mut self) -> Result<()> {
        let signer_seeds: [&[&[u8]]; 1] = [&[
            b"escrow",
            self.maker.to_account_info().key.as_ref(),
            &self.escrow.seed.to_le_bytes()[..],
            &[self.escrow.bump],
        ]];

        // close the vault — returns remaining rent to maker
        close_account(
            CpiContext::new_with_signer(
                self.token_program.to_account_info(),
                CloseAccount {
                    account: self.vault.to_account_info(),
                    authority: self.escrow.to_account_info(),
                    destination: self.maker.to_account_info(),
                },
                &signer_seeds,
            )
        )?;

        // close the escrow PDA — returns its rent to maker
        //
        // This replaces the old `close = maker` declarative constraint.
        // We do it here manually so it only happens on the final fill.
        self.escrow.close(self.maker.to_account_info())?;

        Ok(())
    }
}

pub fn handler(ctx: Context<Take>, fill_amount: u64) -> Result<()> {
    
    let clock = Clock::get()?;
    require!(clock.unix_timestamp < ctx.accounts.escrow.expires_at, EscrowError::EscrowExpired);


    let remaining_receive = ctx.accounts.escrow.receive;
    require!(fill_amount > 0 && fill_amount <= remaining_receive, EscrowError::InvalidFillAmount);


    // How much token_A to release for this fill?
    //
    //   token_a_to_release = (fill_amount × vault.amount) / remaining_receive
    //
    // We use vault.amount (current vault balance) NOT deposit_amount, because
    // both vault.amount and remaining_receive decrease proportionally after
    // each partial fill. Using the original deposit_amount with an updated
    // remaining_receive would drift the exchange rate in favor of later takers.
    //
    // Special case: if this is the LAST fill (fill_amount == remaining),
    // just release whatever's left in the vault. This avoids rounding
    // dust that could leave 1-2 tokens stranded.
    //
    let is_final_fill = fill_amount == remaining_receive;

    let token_a_to_release = if is_final_fill {
        // drain the vault completely — no rounding issues
        ctx.accounts.vault.amount
    } else {
        // proportional release using u128 to prevent overflow
        (fill_amount as u128)
            .checked_mul(ctx.accounts.vault.amount as u128).unwrap()
            .checked_div(remaining_receive as u128).unwrap() as u64
    };

    // TRANSFER token_B: taker → maker (minus fee) + treasury 
    ctx.accounts.transfer_to_maker(fill_amount)?;

    // TRANSFER token_A: vault → taker
    ctx.accounts.withdraw_from_vault(token_a_to_release)?;

    //  UPDATE or CLOSE
    //
    // If this was the final fill, close vault + escrow (returns rent).
    // Otherwise, update escrow.receive so the next fill uses the reduced
    // remaining amount.
    //
    if is_final_fill {
        ctx.accounts.close_vault_and_escrow()?;
    } else {
        // Decrement the remaining receive — next taker sees a smaller amount
        ctx.accounts.escrow.receive = remaining_receive
            .checked_sub(fill_amount)
            .unwrap();
    }

    Ok(())
}


// taker performs mainly these actions:
// 1. pay token_b to maker (fill_amount minus fee, fee to treasury)
// 2. receive proportional token_a from vault
// 3. if final fill: close vault + escrow, returning rent to maker

// taker: user that accepts the terms of maker and is making the exchange
// maker: user initially setting the terms of exchange
// escrow : account where all the terms of this exchange lives
// mint_a : token that the maker has deposited
// mint_b : token that the maker wants in return
// vault : token account associated with mint_a and escrow which will send the tokens to the taker
// taker_ata_a: token account associated with the taker and mint_a that will receive the tokens from the vault
// taker_ata_b: token account associated with the taker and mint_b that will send the token to the maker
// maker_ata_b: token account associated with the maker and mint_b that will receive the tokens from the taker
// treasury: PDA for collecting protocol fees
// treasury_ata_b: treasury's token_b account for receiving fees
// associated_token_program: program used to created associated token account
// token_program: program used to CPI the transfer
// system_program: program used to create the escrow
