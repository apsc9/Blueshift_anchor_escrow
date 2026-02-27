#![allow(unexpected_cfgs)]
use anchor_lang::prelude::*;
mod state;
mod errors;
mod instructions;
use instructions::*;

declare_id!("EuAQ3zNBHTPeUhFNbM6PsRr1dW6Q1eH4PrRzUz32iW8c");

#[program]
pub mod blueshift_anchor_escrow {
    use super::*;
 
    #[instruction(discriminator = 0)]
    pub fn make(ctx: Context<Make>, seed: u64, receive: u64, amount: u64, expires_at: i64, fee_bps: u16) -> Result<()> {
        instructions::make::handler(ctx, seed, receive, amount, expires_at, fee_bps)
    }
    #[instruction(discriminator = 1)]
    pub fn take(ctx: Context<Take>, fill_amount: u64) -> Result<()> {
        instructions::take::handler(ctx, fill_amount)
    }

    #[instruction(discriminator = 2)]
    pub fn refund(ctx: Context<Refund>) -> Result<()> {
        instructions::refund::handler(ctx)
    }
}