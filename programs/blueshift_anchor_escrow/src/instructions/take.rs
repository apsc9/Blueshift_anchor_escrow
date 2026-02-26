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
    #[account(
        mut,
        seeds = [b"escrow", maker.key().as_ref(), escrow.seed.to_le_bytes().as_ref()],
        bump = escrow.bump,
        close = maker,
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

    //programs
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub token_program: Interface<'info, TokenInterface>,
    pub system_program: Program<'info, System>
}

impl<'info> Take<'info> {
    fn transfer_to_maker(&mut self) -> Result<()> {
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
            self.escrow.receive,
            self.mint_b.decimals,
        )?;
        Ok(())
    }

    // transfer from vault to taker_ata_a and close the vault
    fn withdraw_and_close_vault(&mut self) -> Result<()> {
        // create signer seeds for the vault
        let signer_seeds: [&[&[u8]]; 1] = [&[
            b"escrow",
            self.maker.to_account_info().key.as_ref(),
            &self.escrow.seed.to_le_bytes()[..],
            &[self.escrow.bump],
        ]];

        // transfer token from vault to taker_ata_a
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
            self.vault.amount,
            self.mint_a.decimals,
        )?;

        //close the vault
        close_account(
            CpiContext::new_with_signer(
                self.token_program.to_account_info(),
                CloseAccount {
                    account: self.vault.to_account_info(),
                    authority: self.escrow.to_account_info(),
                    destination: self.maker.to_account_info(),
                },
                &signer_seeds,   
            ))?;
            Ok(())
    }
}

pub fn handler(ctx: Context<Take>) -> Result<()> {
    // check if escrow has expired — only live escrows can be taken
    let clock = Clock::get()?;
    require!(clock.unix_timestamp < ctx.accounts.escrow.expires_at, EscrowError::EscrowExpired);

    // transfer token B to maker
    ctx.accounts.transfer_to_maker()?;

    // withdraw and close the vault
    ctx.accounts.withdraw_and_close_vault()?;

    Ok(())
}


// taker performs mainly these actions:
// 1. close escrow, send tokens back to maker
// 2. move token a from vault to taker, then close the vault
// 3. transfer eqvt amount of token b from taker to maker

// taker: user that accepts the terms of maker and is making the exchange
// maker: user initially setting the terms of exchange
// escrow : account where all the terms of this exchange lives
// mint_a : token that the maker has deposited
// mint_b : token that the maker wants in return
// vault : token account associated with mint_a and escrow which will send the tokens to the taker
// taker_ata_a: token account associated with the taker and mint_a that will receive the tokens from the vault
// taker_ata_b: token account associated with the taker and mint_b that will send the token to the maker
// maker_ata_b: token account associated with the maker and mint_b that will receive the tokens from the taker
// associated_token_program: program used to created associated token account
// token_program: program used to CPI the transfer
// system_program: program used to create the escrow


