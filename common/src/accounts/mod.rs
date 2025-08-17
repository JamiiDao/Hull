// use core::fmt;

// pub struct Account {
//     fee_payer: bool,
//     account_type: AccountType,
//     owner: [u8; 32],
// }

// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
// pub enum AccountType {
//     User,
//     Native,
//     PDA,
//     // For PDA Data
//     Data(Data),
//     Program,
//     Mint,
//     Token,
//     AssociatedTokenAccount,
//     Vote,
//     Stake,
// }

// impl fmt::Display for AccountType {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(
//             f,
//             "{}",
//             match self {
//                 Self::Native => " Account",
//                 Self::PDA => "Program Derived Account",
//                 Self::Program => "Executable Program Account",
//             }
//         )
//     }
// }

// // Fee payer must be owned by the Solana Program
// // Program must be owned by the BPF loader

// pub struct Data {
//     version: Semver,
// }
