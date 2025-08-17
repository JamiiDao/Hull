/// Helper method instead of using the longer fn() -> Result<T, [HullSvmError]>
/// you can use fn() -> [HullSvmResult]<T>
#[allow(rustdoc::invalid_html_tags)]
pub type HullSvmResult<T> = Result<T, HullSvmError>;

/// The error handler used across Hull SVM framework crates
#[derive(Debug, thiserror::Error)]
pub enum HullSvmError {
    /// The bytes supplied are not valid Semver
    #[error("The bytes supplied are not valid Semver")]
    InvalidSemverBytes,
}
