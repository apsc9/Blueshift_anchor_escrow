use anchor_lang::prelude::*;
use anchor_spl::token_interface::{Mint, TokenAccount, TokenInterface, transfer_checked, TransferChecked, close_account, CloseAccount};
use anchor_spl::associated_token::AssociatedToken;
use crate::state::Escrow;
use crate::errors::EscrowError;

#[derive(Accounts)]
pub struct Refund<'info> {
    #[account(mut)]
    pub maker: Signer<'info>,

    #[account(
        mut,
        close = maker,
        seeds = [b"escrow", maker.key().as_ref(), escrow.seed.to_le_bytes().as_ref()],
        bump = escrow.bump,
        has_one = maker @ EscrowError::InvalidMaker,
        has_one = mint_a @ EscrowError::InvalidMintA,
        
    )]
    pub escrow: Box<Account<'info, Escrow>>,

    #[account(
        mint::token_program = token_program
    )]
    pub mint_a: Box<InterfaceAccount<'info, Mint>>,

    #[account(
        mut,
        associated_token::mint = mint_a,
        associated_token::authority = escrow,
        associated_token::token_program = token_program,
    )]
    pub vault: Box<InterfaceAccount<'info, TokenAccount>>,

    #[account(
        init_if_needed,
        payer = maker,
        associated_token::mint = mint_a,
        associated_token::authority = maker,
        associated_token::token_program = token_program,
    )]
    pub maker_ata_a: Box<InterfaceAccount<'info, TokenAccount>>,

    pub associated_token_program: Program<'info, AssociatedToken>,
    pub token_program: Interface<'info, TokenInterface>,
    pub system_program: Program<'info, System>,
}

impl<'info> Refund<'info> {
    pub fn refund_and_close_vault(&mut self) -> Result<()> {
        let signer_seeds: [&[&[u8]]; 1] = [&[
            b"escrow",
            self.maker.to_account_info().key.as_ref(),
            &self.escrow.seed.to_le_bytes()[..],
            &[self.escrow.bump],
        ]];

        // transfer from vault to maker_ata_a
        transfer_checked(
            CpiContext::new_with_signer(
                self.token_program.to_account_info(),
                TransferChecked {
                    from: self.vault.to_account_info(),
                    mint: self.mint_a.to_account_info(),
                    to: self.maker_ata_a.to_account_info(),
                    authority: self.escrow.to_account_info(),
                },
                &signer_seeds,
            ),
            self.vault.amount,
            self.mint_a.decimals,
        )?;

        // close the vault
        close_account(
            CpiContext::new_with_signer(
                self.token_program.to_account_info(),
                CloseAccount {
                    account: self.vault.to_account_info(),
                    destination: self.maker.to_account_info(),
                    authority: self.escrow.to_account_info(),
                },
                &signer_seeds,
            )
        )?;

        Ok(())
    }
}

pub fn handler(ctx: Context<Refund>) -> Result<()> {
    ctx.accounts.refund_and_close_vault()?;
    Ok(())
}


// close the escrow pda and transfer the rent back to maker
// move the token a balance out of the vault and back to the vault and close the vault 

// maker : one who set the terms of the transfer
// escrow : account which contains all these terms
// mint_a : token that the maker deposits
// vault: token account associated with escrow and mint_a where the tokens were deposited
// maker_ata_a: token account associated with maker and mint_a which will receive the tokend from vault
// associated token program: token program used to create token accounts
// token_program : program used to cpi the transfer
// system_program: program used to create escrow 