use anchor_lang::prelude::*;
#[error_code]
pub enum EscrowError {
    #[msg("Invalid amount")]
    InvalidAmount,
    #[msg("Invalid maker")]
    InvalidMaker,
    #[msg("Invalid mint_a")]
    InvalidMintA,
    #[msg("Invalid mint_b")]
    InvalidMintB,
    #[msg("Escrow has expired")]
    EscrowExpired,
    #[msg("Expiry must be in the future")]
    ExpiryInPast,
    #[msg("Fee basis points must be <= 10000")]
    InvalidFeeBps,
}