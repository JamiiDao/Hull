macro_rules! create_native_program_info {
    ($identifier:expr, $address:expr, $loader:expr) => {{
        let loader: LoaderProgram = $loader;
        let public_key_bytes = five8_const::decode_32_const($address);

        PrebuiltProgramInfo {
            common: PrebuiltProgramCommon {
                identifier: $identifier,
                address: $address,
                public_key_bytes,
            },
            loader,
        }
    }};
}

macro_rules! create_native_program_info_extra {
    ($identifier:expr, $address:expr, $loader:expr) => {{
        let loader: PrebuiltProgramInfo = $loader;

        let public_key_bytes = five8_const::decode_32_const($address);

        PrebuiltProgramInfoExtra {
            common: PrebuiltProgramCommon {
                identifier: $identifier,
                public_key_bytes,

                address: $address,
            },
            loader,
        }
    }};
}

macro_rules! create_native_sysvar_program_info {
    ($identifier:expr, $address:expr, ) => {{
        let public_key_bytes = five8_const::decode_32_const($address);

        PrebuiltSysvarProgramInfo {
            common: PrebuiltProgramCommon {
                identifier: $identifier,
                address: $address,
                public_key_bytes,
            },
            loader: PrebuiltPrograms::sysvar(),
        }
    }};
}

/// Handles fetching information about native prebuilt Solana programs.
/// The information is from [solana-sdk-ids](https://docs.rs/solana-sdk-ids/latest/src/solana_sdk_ids/lib.rs.html#1-121)
/// Each program is owned by some other program expect for the [NativeLoader](LoaderProgram::Native).
/// Programs loaded by other programs apart from the [LoaderProgram] enum
pub struct PrebuiltPrograms;

impl PrebuiltPrograms {
    /// The system program `11111111111111111111111111111111` info which is loaded by the [NativeLoader](LoaderProgram::Native).
    pub const fn system_program() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "system_program",
            "11111111111111111111111111111111",
            LoaderProgram::Native
        )
    }

    /// The address lookup table `AddressLookupTab1e1111111111111111111111111` info
    pub const fn address_lookup_table() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "address_lookup_table",
            "AddressLookupTab1e1111111111111111111111111",
            LoaderProgram::BpfV3
        )
    }

    /// The compute budget program `ComputeBudget111111111111111111111111111111` info
    pub const fn compute_budget() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "compute_budget",
            "ComputeBudget111111111111111111111111111111",
            LoaderProgram::Native
        )
    }

    /// The configuration program `Config1111111111111111111111111111111111111` info
    pub const fn config() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "config",
            "Config1111111111111111111111111111111111111",
            LoaderProgram::BpfV3
        )
    }

    /// The Ed25519SigVerify111111111111111111111111111 info
    pub const fn ed25519_program() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "ed25519_program",
            "Ed25519SigVerify111111111111111111111111111",
            LoaderProgram::Native
        )
    }

    /// The feature program `Feature111111111111111111111111111111111111` info for activating/deactivation new features
    pub const fn feature() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "feature",
            "Feature111111111111111111111111111111111111",
            LoaderProgram::BpfV3
        )
    }

    /// The incinerator `1nc1nerator11111111111111111111111111111111` designated address for burning lamports.
    /// Lamports credited to this address will be removed from the total supply
    /// (burned) at the end of the current block.
    pub const fn incinerator() -> PrebuiltProgramInfoExtra {
        create_native_program_info_extra!(
            "incinerator",
            "1nc1nerator11111111111111111111111111111111",
            Self::system_program()
        )
    }

    /// The Secp256k1 program `KeccakSecp256k11111111111111111111111111111` info
    pub const fn secp256k1_program() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "secp256k1_program",
            "KeccakSecp256k11111111111111111111111111111",
            LoaderProgram::Native
        )
    }

    /// The Secp256r1 program `Secp256r1SigVerify1111111111111111111111111` info
    pub const fn secp256r1_program() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "secp256r1_program",
            "Secp256r1SigVerify1111111111111111111111111",
            LoaderProgram::Native
        )
    }

    /// The staking program `Stake11111111111111111111111111111111111111` info
    pub const fn stake() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "stake",
            "Stake11111111111111111111111111111111111111",
            LoaderProgram::BpfV3
        )
    }

    /// The stake configuration program `StakeConfig11111111111111111111111111111111` info
    pub const fn stake_config() -> PrebuiltProgramInfoExtra {
        create_native_program_info_extra!(
            "stake::config",
            "StakeConfig11111111111111111111111111111111",
            Self::config()
        )
    }

    /// The vote program `Vote111111111111111111111111111111111111111` info
    pub const fn vote() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "vote",
            "Vote111111111111111111111111111111111111111",
            LoaderProgram::Native
        )
    }

    /// The sysvar program `Sysvar1111111111111111111111111111111111111` info
    pub const fn sysvar() -> PrebuiltProgramInfoExtra {
        create_native_program_info_extra!(
            "sysvar",
            "Sysvar1111111111111111111111111111111111111",
            Self::system_program()
        )
    }

    /// The sysvar clock program `SysvarC1ock11111111111111111111111111111111` info
    pub const fn sysvar_clock() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::clock",
            "SysvarC1ock11111111111111111111111111111111",
        )
    }

    /// The sysvar epoch rewards program `SysvarEpochRewards1111111111111111111111111` info
    pub const fn sysvar_epoch_rewards() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::epoch_rewards",
            "SysvarEpochRewards1111111111111111111111111",
        )
    }

    /// The sysvar epoch schedule program `SysvarEpochSchedu1e111111111111111111111111` info
    pub const fn sysvar_epoch_schedule() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::epoch_schedule",
            "SysvarEpochSchedu1e111111111111111111111111",
        )
    }

    /// The sysvar fees program `SysvarFees111111111111111111111111111111111` info
    pub const fn sysvar_fees() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::fees",
            "SysvarFees111111111111111111111111111111111",
        )
    }

    /// The sysvar instructions program `Sysvar1nstructions1111111111111111111111111` info
    pub const fn sysvar_instructions() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::instructions",
            "Sysvar1nstructions1111111111111111111111111",
        )
    }

    /// The last restart slot program `SysvarLastRestartS1ot1111111111111111111111` info
    pub const fn sysvar_last_restart_slot() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::last_restart_slot",
            "SysvarLastRestartS1ot1111111111111111111111",
        )
    }

    /// The recent blockhashes program `SysvarRecentB1ockHashes11111111111111111111` info
    pub const fn sysvar_recent_blockhashes() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::recent_blockhashes",
            "SysvarRecentB1ockHashes11111111111111111111",
        )
    }

    /// The sysvar rent program `SysvarRent111111111111111111111111111111111` info
    pub const fn sysvar_rent() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::rent",
            "SysvarRent111111111111111111111111111111111",
        )
    }

    /// The sysvar rewards program `SysvarRewards111111111111111111111111111111` info
    pub const fn sysvar_rewards() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::rewards",
            "SysvarRewards111111111111111111111111111111",
        )
    }

    /// The slot hashes program `SysvarS1otHashes111111111111111111111111111` info
    pub const fn sysvar_slot_hashes() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::slot_hashes",
            "SysvarS1otHashes111111111111111111111111111",
        )
    }

    /// The sysvar history slot `SysvarS1otHistory11111111111111111111111111` info
    pub const fn sysvar_slot_history() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::slot_history",
            "SysvarS1otHistory11111111111111111111111111",
        )
    }

    /// The sysvar stake history `SysvarStakeHistory1111111111111111111111111` info
    pub const fn sysvar_stake_history() -> PrebuiltSysvarProgramInfo {
        create_native_sysvar_program_info!(
            "sysvar::stake_history",
            "SysvarStakeHistory1111111111111111111111111",
        )
    }

    /// The ZK token proof program `ZkTokenProof1111111111111111111111111111111` info
    pub const fn zk_token_proof_program() -> PrebuiltProgramInfoExtra {
        create_native_program_info_extra!(
            "zk_token_proof_program",
            "ZkTokenProof1111111111111111111111111111111",
            Self::system_program()
        )
    }

    /// The ZK Elgamal program `ZkE1Gama1Proof11111111111111111111111111111` info
    pub const fn zk_elgamal_proof_program() -> PrebuiltProgramInfo {
        create_native_program_info!(
            "zk_elgamal_proof_program",
            "ZkE1Gama1Proof11111111111111111111111111111",
            LoaderProgram::Native
        )
    }
}

/// A prebuilt program information containing:
/// - Base58 address
/// - identifier name
/// - public key bytes
/// - loader program that loads the current address
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct PrebuiltProgramInfo {
    /// Common characteristic of a prebuilt native program as defined by [PrebuiltProgramCommon]
    pub common: PrebuiltProgramCommon,
    /// The program that loads this address
    pub loader: LoaderProgram,
}

/// A prebuilt program information containing:
/// - Base58 address
/// - identifier name
/// - public key bytes
/// - loader program which is another program address not part of the [LoaderProgram].
///
/// Example the [`SysvarStakeHistory1111111111111111111111111`](PrebuiltPrograms::sysvar_stake_history()) is loaded by the Sysvar
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct PrebuiltProgramInfoExtra {
    /// Common characteristic of a prebuilt native program as defined by [PrebuiltProgramCommon]
    pub common: PrebuiltProgramCommon,
    /// The program that loads this address
    pub loader: PrebuiltProgramInfo,
}

/// A prebuilt program information containing:
/// - Base58 address
/// - identifier name
/// - public key bytes
/// - loader program which is another program address not part of the [LoaderProgram].
///
/// This program can be loaded by another program which in turn might be loaded by another program
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct PrebuiltSysvarProgramInfo {
    /// Common characteristic of a prebuilt native program as defined by [PrebuiltProgramCommon]
    pub common: PrebuiltProgramCommon,
    /// The program that loads this address
    pub loader: PrebuiltProgramInfoExtra,
}

/// A prebuilt program information containing:
/// - Base58 address
/// - identifier name
/// - public key bytes
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct PrebuiltProgramCommon {
    /// The short name identifier of the program as used in Solana sdk modules
    pub identifier: &'static str,
    /// The base58 identifier of the program
    pub address: &'static str,
    /// The Base58 public key of the address in bytes evaluated at compile time
    pub public_key_bytes: [u8; 32],
}

/// Every program itself is owned by another program, which is its loader.
/// Currently, five loader programs exist described in this enum,
/// These loaders are necessary to create and manage custom programs:
///
/// - Deploy a new program or buffer
/// - Close a program or buffer
/// - Redeploy / upgrade an existing program
/// - Transfer the authority over a program
/// - Finalize a program
///
/// Loader-v3 and loader-v4 support modifications to programs after their initial deployment.
/// Permission to do so is regulated by the authority of a program because the account ownership of each program resides with the loader.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum LoaderProgram {
    /// Own other programs
    Native,
    /// Management instructions are disabled, but programs still execute
    BpfV1,
    /// Management instructions are disabled, but programs still execute
    BpfV2,
    /// Is being phased out
    BpfV3,
    /// v4 is expected to become the standard loader
    LoaderV4,
}

impl LoaderProgram {
    /// Base58 address for a program
    pub const fn address(&self) -> &'static str {
        match self {
            Self::Native => "NativeLoader1111111111111111111111111111111",
            Self::BpfV1 => "BPFLoader1111111111111111111111111111111111",
            Self::BpfV2 => "BPFLoader2111111111111111111111111111111111",
            Self::BpfV3 => "BPFLoaderUpgradeab1e11111111111111111111111",
            Self::LoaderV4 => "LoaderV411111111111111111111111111111111111",
        }
    }

    /// The short name identifier for a program
    pub const fn identifier(&self) -> &'static str {
        match self {
            Self::Native => "native_loader",
            Self::BpfV1 => "bpf_loader_deprecated",
            Self::BpfV2 => "bpf_loader",
            Self::BpfV3 => "bpf_loader_upgradeable",
            Self::LoaderV4 => "loader_v4",
        }
    }

    /// The public key bytes of a program
    pub const fn public_key_bytes(&self) -> [u8; 32] {
        five8_const::decode_32_const(self.address())
    }

    /// The owner of a program
    pub const fn loader(&self) -> Option<Self> {
        match self {
            Self::Native => Option::None,
            _ => Some(Self::Native),
        }
    }
}
