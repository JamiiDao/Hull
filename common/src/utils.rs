/// Utilities that can be reused  
pub struct Utils;

impl Utils {
    /// A buffer size of 3 since an ASCII digit of `u8` can have a maximum of 3 characters .
    pub const ASCII_DIGIT_BUFFER_SIZE: usize = 3;
    /// Convert a `u8` into an ASCII character.
    /// ### Usage
    /// ```rust
    /// use hull_svm_common::Utils;
    ///
    /// let mut buffer = [0u8; Utils::ASCII_DIGIT_BUFFER_SIZE];
    /// let valid_length = Utils::u8_to_ascii_digits(8, &mut buffer); // The index up to which you can parse a valid `&str`
    /// println!("{:?}", core::str::from_utf8(&buffer[..valid_length]));
    /// ```
    pub fn u8_to_ascii_digits(
        mut u8_value: u8,
        buf: &mut [u8; Self::ASCII_DIGIT_BUFFER_SIZE],
    ) -> usize {
        let mut i = buf.len();
        loop {
            i -= 1;
            buf[i] = (u8_value % 10) + b'0';
            u8_value /= 10;
            if u8_value == 0 {
                break;
            }
        }
        let len = buf.len() - i;
        buf.copy_within(i.., 0); // shift to start
        len
    }
}
