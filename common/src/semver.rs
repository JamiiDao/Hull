use core::fmt;

use crate::HullSvmError;

/// [Semver](https://semver.org/) versioning that can be stored in an array.
/// It String format is
///
/// `major_version.minor_version.patch_version` + optional `.release_candidate_version || beta_version` || alpha_version
///
/// The maximum number version is a `u8` for each value, for example the major version can be a
/// maximum of 255.
///
/// [Semver] also provides a `try_into()` implementation that you can provide a byte slice
/// that will return [HullSvmError::InvalidSemverBytes] if the byte slice is not [Semver::PACKED_LEN] long.
///
/// - To use the  [SemverTextBuffer] to convert a [Semver] to UTF-8 byte slice enable `display_and_debug` features.
///
/// - To be able to sort a [Semver] using  [PartialOrd] and [Ord] traits enable `ordering` feature
///
/// ### Usage
/// ```rust
/// use hull_svm_common::Semver;
///
/// let semver = Semver::new(); // Creates a default semver version `0.0.0`
///
/// semver.set_major_version(1); // Sets the major semver version number
///
/// semver.set_minor_version(1); // Sets the minor semver version number
///
/// semver.set_patch_version(1); // Sets the patch semver version number
///
/// semver.set_release_candidate_version(1); // Sets the release candidate (rc) semver version number
///
/// semver.set_beta_version(1); // Sets the beta beta version number
///
/// semver.set_alpha_version(1); // Sets the alpha semver version number
///
/// semver.get_major_version(); // Gets the major semver version number
/// semver.get_minor_version(); // Gets the minor semver version number
/// semver.get_patch_version(); // Gets the patch semver version number
/// semver.get_release_candidate_version(); // Gets the release_candidate semver version number
/// semver.get_beta_version(); // Gets the beta semver version number
/// semver.get_alpha_version(); // Gets the alpha semver version number
///
/// let packed_semver_array = semver.to_bytes(); //Convert to a byte array
/// let back_to_semver = Semver::from_bytes(packed_semver_array); // Convert back to a byte array
/// let packed_semver_array_slice: &[u8] = &packed_semver_array; // Simulate a `&[u8]`
/// let back_to_semver_but_with_slice: Semver = packed_semver_array_slice.try_into()?;
///
/// Ok::<(), hull_svm_common::HullSvmError>(())
/// ```
#[derive(PartialEq, Eq, Clone, Copy, Default)]
pub struct Semver {
    major: u8,
    minor: u8,
    patch: u8,
    alpha: Option<u8>,
    beta: Option<u8>,
    release_candidate: Option<u8>,
}

impl Semver {
    /// The length of the array of a [Self](Semver) converted to bytes
    pub const PACKED_LEN: usize = 5;
    /// The array for the packed bytes of [Self](Semver)
    pub const PACKED: [u8; 5] = [0u8; Self::PACKED_LEN];
    const ALPHA_RANK: u8 = 0;
    const BETA_RANK: u8 = 1;
    const RELEASE_CANDIDATE_RANK: u8 = 2;
    const STABLE_RANK: u8 = 3;
    const NO_RANK: u8 = 4;
    const MAJOR_INDEX: usize = 0;
    const MINOR_INDEX: usize = 1;
    const PATCH_INDEX: usize = 2;
    const RANK_INDEX: usize = 3;
    const UNSTABLE_INDEX: usize = 4;

    /// Instantiate a new [Semver].
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the major version of the [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.set_major_version(1);
    /// ```
    pub fn set_major_version(mut self, version: u8) -> Self {
        self.major = version;

        self
    }

    /// Set the minor version of the [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.set_minor_version(1);
    /// ```
    pub fn set_minor_version(mut self, version: u8) -> Self {
        self.minor = version;

        self
    }

    /// Set the patch version of the [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.set_patch_version(1);
    /// ```
    pub fn set_patch_version(mut self, version: u8) -> Self {
        self.patch = version;

        self
    }

    // Sets the release candidate (rc) version.
    // This will override the beta and alpha version setting them to [Option::None]
    // if they were already set to [Option::Some(T)].
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.set_release_candidate_version(1);
    /// ```
    pub fn set_release_candidate_version(mut self, version: u8) -> Self {
        self.release_candidate.replace(version);
        self.beta.take();
        self.alpha.take();

        self
    }

    // Sets the beta version.
    // This will override the release_candidate and alpha version setting them to [Option::None]
    // if they were already set to [Option::Some(T)]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.set_beta_version(1);
    /// ```
    pub fn set_beta_version(mut self, version: u8) -> Self {
        self.beta.replace(version);

        self.release_candidate.take();
        self.alpha.take();

        self
    }

    // Sets the alpha version.
    // This will override the release_candidate and beta version setting them to [Option::None]
    // if they were already set to [Option::Some(T)]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.set_alpha_version(1);
    /// ```
    pub fn set_alpha_version(mut self, version: u8) -> Self {
        self.alpha.replace(version);

        self.release_candidate.take();
        self.beta.take();

        self
    }

    /// Get the major version of the [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.get_major_version();
    /// ```
    pub fn get_major_version(&self) -> u8 {
        self.major
    }

    /// Get the minor version of the [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.get_minor_version();
    /// ```
    pub fn get_minor_version(&self) -> u8 {
        self.minor
    }

    /// Get the patch version of the [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.get_patch_version();
    /// ```
    pub fn get_patch_version(&self) -> u8 {
        self.patch
    }

    /// Get the release_candidate version version of the [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.get_release_candidate_version();
    /// ```
    pub fn get_release_candidate_version(&self) -> Option<u8> {
        self.release_candidate
    }

    /// Get the beta version of the [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.get_beta_version();
    /// ```
    pub fn get_beta_version(&self) -> Option<u8> {
        self.beta
    }

    /// Get the alpha version of the [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.get_alpha_version();
    /// ```
    pub fn get_alpha_version(&self) -> Option<u8> {
        self.alpha
    }

    /// Convert [Semver] to an array of bytes
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// semver.to_bytes();
    /// ```
    pub fn to_bytes(&self) -> [u8; Self::PACKED_LEN] {
        let mut packed = Self::PACKED;

        packed[Self::MAJOR_INDEX] = self.major;
        packed[Self::MINOR_INDEX] = self.minor;
        packed[Self::PATCH_INDEX] = self.patch;
        packed[Self::RANK_INDEX] = Self::NO_RANK;

        let mut pack_unstable = |option: u8, value: Option<u8>| {
            if let Some(value_exists) = value {
                packed[Self::RANK_INDEX] = option;
                packed[Self::UNSTABLE_INDEX] = value_exists;
            }
        };

        pack_unstable(Self::RELEASE_CANDIDATE_RANK, self.release_candidate);
        pack_unstable(Self::BETA_RANK, self.beta);
        pack_unstable(Self::ALPHA_RANK, self.alpha);

        packed
    }

    /// Convert to an array of bytes to a [Semver]
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Semver;
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// let semver_bytes = semver.to_bytes();
    /// let back_to_semver = Semver::from_bytes(semver_bytes);
    /// ```
    pub fn from_bytes(bytes: [u8; Self::PACKED_LEN]) -> Self {
        let mut unpacked = Self {
            major: bytes[Self::MAJOR_INDEX],
            minor: bytes[Self::MINOR_INDEX],
            patch: bytes[Self::PATCH_INDEX],
            ..Default::default()
        };

        if bytes[Self::RANK_INDEX] != Self::NO_RANK {
            if bytes[Self::RANK_INDEX] == Self::RELEASE_CANDIDATE_RANK {
                unpacked
                    .release_candidate
                    .replace(bytes[Self::UNSTABLE_INDEX]);
            }

            if bytes[Self::RANK_INDEX] == Self::BETA_RANK {
                unpacked.beta.replace(bytes[Self::UNSTABLE_INDEX]);
            }

            if bytes[Self::RANK_INDEX] == Self::ALPHA_RANK {
                unpacked.alpha.replace(bytes[Self::UNSTABLE_INDEX]);
            }
        }

        unpacked
    }
}

impl TryFrom<&[u8]> for Semver {
    type Error = HullSvmError;
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let to_byte_array: [u8; Self::PACKED_LEN] =
            value.try_into().or(Err(HullSvmError::InvalidSemverBytes))?;

        Ok(Self::from_bytes(to_byte_array))
    }
}

/// Use [SemverTextBuffer] to convert [Semver] to a byte slice that can be
/// converted to a valid UTF-8 stack allocated string `(&str)`
/// ### Usage
/// ```rust
/// use hull_svm_common::{Semver, SemverTextBuffer};
///
/// let semver = Semver::new(); // Creates a default semver version `0.0.0`
/// let utf8_byte_slice = SemverTextBuffer::new().parse(&semver);
/// println!("{:?}", core::str::from_utf8(utf8_byte_slice.get_buffer()));
/// ```
#[cfg(feature = "display_and_debug")]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct SemverTextBuffer([u8; Self::TEXT_BUFFER_SIZE]);

#[cfg(feature = "display_and_debug")]
impl SemverTextBuffer {
    const SEPERATOR_CHAR_SIZE: usize = 1;
    const U8_MAX_CHARS: usize = 3;
    const MAX_UNSTABLE_CHAR_SIZE: usize = 5;
    const CHAR_BUFFER: [u8; crate::Utils::ASCII_DIGIT_BUFFER_SIZE] =
        [0u8; crate::Utils::ASCII_DIGIT_BUFFER_SIZE];
    const MARKER_POSITION: usize = 0;
    const MARKER_LEN: usize = 1;
    const RC_CHARS: &[u8] = b"rc";
    const RC_CHAR_LENGTH: usize = Self::RC_CHARS.len();
    const BETA_CHARS: &[u8] = b"beta";
    const BETA_CHAR_LENGTH: usize = Self::BETA_CHARS.len();
    const ALPHA_CHARS: &[u8] = b"alpha";
    const ALPHA_CHAR_LENGTH: usize = Self::ALPHA_CHARS.len();

    const TEXT_BUFFER_SIZE: usize = Self::MARKER_LEN
        + (SemverTextBuffer::U8_MAX_CHARS * 4)
        + (SemverTextBuffer::SEPERATOR_CHAR_SIZE * 4)
        + SemverTextBuffer::MAX_UNSTABLE_CHAR_SIZE;

    /// Instantiate a new zero filled buffer
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::SemverTextBuffer;
    ///
    /// let text_buffer = SemverTextBuffer::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// ### Usage
    /// ```rust
    /// use hull_svm_common::{Semver, SemverTextBuffer};
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// let utf8_byte_slice = SemverTextBuffer::new().parse(&semver);
    /// println!("{:?}", core::str::from_utf8(utf8_byte_slice.get_buffer()));
    /// ```
    pub fn get_buffer(&self) -> &[u8] {
        let len = self.0[Self::MARKER_POSITION] as usize;
        &self.0[1..len]
    }

    /// ### Usage
    /// ```rust
    /// use hull_svm_common::{Semver, SemverTextBuffer};
    ///
    /// let semver = Semver::new(); // Creates a default semver version `0.0.0`
    /// let utf8_byte_slice = SemverTextBuffer::new().parse(&semver); // Parse a `Semver` struct
    /// ```
    pub fn parse(mut self, semver: &Semver) -> Self {
        use crate::Utils;

        let mut char_buffer = Self::CHAR_BUFFER;
        let mut valid_buffer_length = Self::MARKER_LEN;

        let mut stable_ops = |marker: usize, inner_buffer: &[u8], separator: bool| {
            self.0[valid_buffer_length..valid_buffer_length + marker]
                .copy_from_slice(&inner_buffer[..marker]);
            valid_buffer_length += marker;
            if separator {
                self.0[valid_buffer_length] = b'.';
                valid_buffer_length += Self::SEPERATOR_CHAR_SIZE;
            }
        };

        let major_marker = Utils::u8_to_ascii_digits(semver.major, &mut char_buffer);
        stable_ops(major_marker, &char_buffer, true);
        let minor_marker = Utils::u8_to_ascii_digits(semver.minor, &mut char_buffer);
        stable_ops(minor_marker, &char_buffer, true);
        let patch_marker = Utils::u8_to_ascii_digits(semver.patch, &mut char_buffer);
        stable_ops(patch_marker, &char_buffer, false);

        let mut unreleased_ops =
            |value: Option<u8>, char_buffer: &mut [u8; 3], chars: &[u8], char_size: usize| {
                if let Some(inner_value) = value {
                    self.0[valid_buffer_length] = b'-';
                    valid_buffer_length += Self::SEPERATOR_CHAR_SIZE;

                    self.0[valid_buffer_length..valid_buffer_length + char_size]
                        .copy_from_slice(chars);
                    valid_buffer_length += char_size;
                    self.0[valid_buffer_length] = b'.';
                    valid_buffer_length += Self::SEPERATOR_CHAR_SIZE;

                    let inner_value_marker = Utils::u8_to_ascii_digits(inner_value, char_buffer);

                    self.0[valid_buffer_length..valid_buffer_length + inner_value_marker]
                        .copy_from_slice(&char_buffer[..inner_value_marker]);
                    valid_buffer_length += inner_value_marker;
                }
            };

        let mut char_buffer = Self::CHAR_BUFFER;

        unreleased_ops(
            semver.release_candidate,
            &mut char_buffer,
            Self::RC_CHARS,
            Self::RC_CHAR_LENGTH,
        );
        unreleased_ops(
            semver.beta,
            &mut char_buffer,
            Self::BETA_CHARS,
            Self::BETA_CHAR_LENGTH,
        );
        unreleased_ops(
            semver.alpha,
            &mut char_buffer,
            Self::ALPHA_CHARS,
            Self::ALPHA_CHAR_LENGTH,
        );

        self.0[Self::MARKER_POSITION] = valid_buffer_length as u8;

        self
    }
}

#[cfg(feature = "ordering")]
impl PartialOrd for Semver {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(feature = "ordering")]
impl Ord for Semver {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let prerelease_rank = |value: &Semver| -> (u8, u8) {
            // Lower rank means "earlier" in semver ordering
            if let Some(a) = value.alpha {
                (Self::ALPHA_RANK, a)
            } else if let Some(b) = value.beta {
                (Self::BETA_RANK, b)
            } else if let Some(rc) = value.release_candidate {
                (Self::RELEASE_CANDIDATE_RANK, rc)
            } else {
                // Stable versions get the highest rank so they sort after all prereleases
                (Self::STABLE_RANK, 0)
            }
        };

        // Compare major, minor, patch first
        (self.major, self.minor, self.patch)
            .cmp(&(other.major, other.minor, other.patch))
            // If equal, compare prerelease state
            .then_with(|| {
                let self_pre = prerelease_rank(self);
                let other_pre = prerelease_rank(other);
                self_pre.cmp(&other_pre)
            })
    }
}

#[cfg(feature = "display_and_debug")]
impl fmt::Display for Semver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            core::str::from_utf8(SemverTextBuffer::new().parse(self).get_buffer()).unwrap()
        )
    }
}

#[cfg(feature = "display_and_debug")]
impl fmt::Debug for Semver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Semver")
            .field("major", &self.major)
            .field("minor", &self.minor)
            .field("patch", &self.patch)
            .field("release_candidate", &self.release_candidate)
            .field("beta", &self.beta)
            .field("alpha", &self.alpha)
            .finish()
    }
}

#[cfg(test)]
mod test_semver_sanity {
    use super::{Semver, SemverTextBuffer};

    use core::str::Utf8Error;

    #[test]
    fn to_bytes() {
        let full_semver = Semver {
            major: u8::MAX,
            minor: u8::MAX,
            patch: u8::MAX,
            alpha: Some(u8::MAX),
            ..Default::default()
        };
        let full_semver_bytes = full_semver.to_bytes();

        let one_0_0 = Semver {
            major: 1,
            ..Default::default()
        };
        let one_0_0_bytes = one_0_0.to_bytes();

        let one_2_1 = Semver {
            major: 1,
            minor: 2,
            patch: 1,
            ..Default::default()
        };
        let one_2_1_bytes = one_2_1.to_bytes();

        let one_2_2 = Semver {
            major: 1,
            minor: 2,
            patch: 2,
            ..Default::default()
        };
        let one_2_2_bytes = one_2_2.to_bytes();

        let one_0_0_alpha_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            alpha: Some(1),
            ..Default::default()
        };
        let one_0_0_alpha_1_bytes = one_0_0_alpha_1.to_bytes();

        let six_0_0_alpha_0 = Semver {
            major: 6,
            minor: 0,
            patch: 0,
            alpha: Some(0),
            ..Default::default()
        };
        let six_0_0_alpha_0_bytes = six_0_0_alpha_0.to_bytes();

        let one_0_0_beta_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            beta: Some(1),
            ..Default::default()
        };
        let one_0_0_beta_1_bytes = one_0_0_beta_1.to_bytes();

        let one_0_0_rc_0 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            release_candidate: Some(0),
            ..Default::default()
        };
        let one_0_0_rc_0_bytes = one_0_0_rc_0.to_bytes();

        let one_0_0_rc_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            release_candidate: Some(1),
            ..Default::default()
        };
        let one_0_0_rc_1_bytes = one_0_0_rc_1.to_bytes();
        let zero_0_0 = Semver::default();
        let zero_0_0_bytes = zero_0_0.to_bytes();

        assert_eq!([0, 0, 0, Semver::NO_RANK, 0], zero_0_0_bytes,);
        assert_eq!([255, 255, 255, Semver::ALPHA_RANK, 255], full_semver_bytes,);
        assert_eq!([6, 0, 0, Semver::ALPHA_RANK, 0], six_0_0_alpha_0_bytes,);
        assert_eq!([1, 2, 2, Semver::NO_RANK, 0], one_2_2_bytes,);
        assert_eq!([1, 2, 1, Semver::NO_RANK, 0], one_2_1_bytes,);
        assert_eq!([1, 0, 0, Semver::NO_RANK, 0], one_0_0_bytes,);
        assert_eq!(
            [1, 0, 0, Semver::RELEASE_CANDIDATE_RANK, 1],
            one_0_0_rc_1_bytes,
        );
        assert_eq!(
            [1, 0, 0, Semver::RELEASE_CANDIDATE_RANK, 0],
            one_0_0_rc_0_bytes,
        );
        assert_eq!([1, 0, 0, Semver::BETA_RANK, 1], one_0_0_beta_1_bytes,);
        assert_eq!([1, 0, 0, Semver::ALPHA_RANK, 1], one_0_0_alpha_1_bytes,);
    }

    #[test]
    fn to_bytes_from_bytes() {
        let full_semver = Semver {
            major: u8::MAX,
            minor: u8::MAX,
            patch: u8::MAX,
            alpha: Some(u8::MAX),
            ..Default::default()
        };
        let full_semver_bytes = full_semver.to_bytes();

        let one_0_0 = Semver {
            major: 1,
            ..Default::default()
        };
        let one_0_0_bytes = one_0_0.to_bytes();

        let one_2_1 = Semver {
            major: 1,
            minor: 2,
            patch: 1,
            ..Default::default()
        };
        let one_2_1_bytes = one_2_1.to_bytes();

        let one_2_2 = Semver {
            major: 1,
            minor: 2,
            patch: 2,
            ..Default::default()
        };
        let one_2_2_bytes = one_2_2.to_bytes();

        let one_0_0_alpha_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            alpha: Some(1),
            ..Default::default()
        };
        let one_0_0_alpha_1_bytes = one_0_0_alpha_1.to_bytes();

        let six_0_0_alpha_0 = Semver {
            major: 6,
            minor: 0,
            patch: 0,
            alpha: Some(0),
            ..Default::default()
        };
        let six_0_0_alpha_0_bytes = six_0_0_alpha_0.to_bytes();

        let one_0_0_beta_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            beta: Some(1),
            ..Default::default()
        };
        let one_0_0_beta_1_bytes = one_0_0_beta_1.to_bytes();

        let one_0_0_rc_0 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            release_candidate: Some(0),
            ..Default::default()
        };
        let one_0_0_rc_0_bytes = one_0_0_rc_0.to_bytes();

        let one_0_0_rc_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            release_candidate: Some(1),
            ..Default::default()
        };
        let one_0_0_rc_1_bytes = one_0_0_rc_1.to_bytes();

        let zero_0_0 = Semver::default();
        let zero_0_0_bytes = zero_0_0.to_bytes();

        assert_eq!(full_semver, Semver::from_bytes(full_semver_bytes),);
        assert_eq!(six_0_0_alpha_0, Semver::from_bytes(six_0_0_alpha_0_bytes),);
        assert_eq!(one_2_2, Semver::from_bytes(one_2_2_bytes),);
        assert_eq!(one_2_1, Semver::from_bytes(one_2_1_bytes),);
        assert_eq!(one_0_0, Semver::from_bytes(one_0_0_bytes),);
        assert_eq!(one_0_0_rc_1, Semver::from_bytes(one_0_0_rc_1_bytes),);
        assert_eq!(one_0_0_rc_0, Semver::from_bytes(one_0_0_rc_0_bytes),);
        assert_eq!(one_0_0_beta_1, Semver::from_bytes(one_0_0_beta_1_bytes),);
        assert_eq!(one_0_0_alpha_1, Semver::from_bytes(one_0_0_alpha_1_bytes),);
        assert_eq!(zero_0_0, Semver::from_bytes(zero_0_0_bytes),);
    }

    #[cfg_attr(feature = "ordering", test)]
    fn sorting_ord_partial_ord() {
        let full_semver = Semver {
            major: u8::MAX,
            minor: u8::MAX,
            patch: u8::MAX,
            alpha: Some(u8::MAX),
            ..Default::default()
        };
        let one_0_0 = Semver {
            major: 1,
            ..Default::default()
        };
        let one_1_0 = Semver {
            major: 1,
            minor: 1,
            ..Default::default()
        };

        let one_1_1 = Semver {
            major: 1,
            minor: 1,
            patch: 1,
            ..Default::default()
        };

        let one_2_1 = Semver {
            major: 1,
            minor: 2,
            patch: 1,
            ..Default::default()
        };

        let one_1_2 = Semver {
            major: 1,
            minor: 1,
            patch: 2,
            ..Default::default()
        };

        let one_2_2 = Semver {
            major: 1,
            minor: 2,
            patch: 2,
            ..Default::default()
        };

        let one_0_0_alpha_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            alpha: Some(1),
            ..Default::default()
        };

        let six_0_0_alpha_0 = Semver {
            major: 6,
            minor: 0,
            patch: 0,
            alpha: Some(0),
            ..Default::default()
        };

        let one_0_0_beta_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            beta: Some(1),
            ..Default::default()
        };

        let one_0_0_rc_0 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            release_candidate: Some(0),
            ..Default::default()
        };

        let one_0_0_rc_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            release_candidate: Some(1),
            ..Default::default()
        };

        let zero_0_0 = Semver::default();

        let mut versions = [
            zero_0_0,
            full_semver,
            one_0_0,
            one_1_0,
            one_1_1,
            one_2_1,
            one_0_0_alpha_1,
            one_0_0_beta_1,
            one_0_0_rc_1,
            one_2_2,
            one_1_2,
            six_0_0_alpha_0,
            one_0_0_rc_0,
        ];
        versions.sort_by(|a, b| b.cmp(a));

        assert_eq!(
            &versions,
            &[
                full_semver,
                six_0_0_alpha_0,
                one_2_2,
                one_2_1,
                one_1_2,
                one_1_1,
                one_1_0,
                one_0_0,
                one_0_0_rc_1,
                one_0_0_rc_0,
                one_0_0_beta_1,
                one_0_0_alpha_1,
                zero_0_0
            ]
        );
    }

    #[cfg_attr(feature = "display_and_debug", test)]
    fn to_str() {
        let full_semver = Semver {
            major: u8::MAX,
            minor: u8::MAX,
            patch: u8::MAX,
            alpha: Some(u8::MAX),
            ..Default::default()
        };
        let one_0_0 = Semver {
            major: 1,
            ..Default::default()
        };

        let one_2_1 = Semver {
            major: 1,
            minor: 2,
            patch: 1,
            ..Default::default()
        };

        let one_2_2 = Semver {
            major: 1,
            minor: 2,
            patch: 2,
            ..Default::default()
        };

        let one_0_0_alpha_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            alpha: Some(1),
            ..Default::default()
        };

        let six_0_0_alpha_0 = Semver {
            major: 6,
            minor: 0,
            patch: 0,
            alpha: Some(0),
            ..Default::default()
        };

        let one_0_0_beta_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            beta: Some(1),
            ..Default::default()
        };

        let one_0_0_rc_0 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            release_candidate: Some(0),
            ..Default::default()
        };

        let one_0_0_rc_1 = Semver {
            major: 1,
            minor: 0,
            patch: 0,
            release_candidate: Some(1),
            ..Default::default()
        };

        assert_eq!(
            Ok::<&str, Utf8Error>("255.255.255-alpha.255"),
            str::from_utf8(SemverTextBuffer::new().parse(&full_semver).get_buffer())
        );
        assert_eq!(
            Ok::<&str, Utf8Error>("6.0.0-alpha.0"),
            str::from_utf8(SemverTextBuffer::new().parse(&six_0_0_alpha_0).get_buffer())
        );
        assert_eq!(
            Ok::<&str, Utf8Error>("1.2.2"),
            str::from_utf8(SemverTextBuffer::new().parse(&one_2_2).get_buffer())
        );
        assert_eq!(
            Ok::<&str, Utf8Error>("1.2.1"),
            str::from_utf8(SemverTextBuffer::new().parse(&one_2_1).get_buffer())
        );
        assert_eq!(
            Ok::<&str, Utf8Error>("1.0.0"),
            str::from_utf8(SemverTextBuffer::new().parse(&one_0_0).get_buffer())
        );
        assert_eq!(
            Ok::<&str, Utf8Error>("1.0.0-rc.1"),
            str::from_utf8(SemverTextBuffer::new().parse(&one_0_0_rc_1).get_buffer())
        );
        assert_eq!(
            Ok::<&str, Utf8Error>("1.0.0-rc.0"),
            str::from_utf8(SemverTextBuffer::new().parse(&one_0_0_rc_0).get_buffer())
        );
        assert_eq!(
            Ok::<&str, Utf8Error>("1.0.0-beta.1"),
            str::from_utf8(SemverTextBuffer::new().parse(&one_0_0_beta_1).get_buffer())
        );
        assert_eq!(
            Ok::<&str, Utf8Error>("1.0.0-alpha.1"),
            str::from_utf8(SemverTextBuffer::new().parse(&one_0_0_alpha_1).get_buffer())
        );
    }
}
