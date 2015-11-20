
#![allow(non_snake_case)]

use std;
use std::collections::BitVec;


#[derive(Debug, Clone, Copy)]
pub enum ConversionError {
    /// Raised if there was some problem calling either `toInts4()` or `toInts8()` on a `String`.
    StrToInt,
    /// Raised if there was some problem calling either `toStr()` on an integer.
    IntToStr,
}

/// `toStr(n, x)` is the n-byte unsigned little-endian binary representation of integer x.
///
/// # Examples
/// ```
/// use crypto::hs1util::toStr;
///
/// let s1: Vec<u8> = toStr(4, &3).unwrap();
/// assert!(vec![0, 0, 0, 3] == s1);
///
/// let s2: Vec<u8> = toStr(4, &256).unwrap();
/// assert!(vec![0, 0, 1, 0] == s2);
///
/// let s3: Vec<u8> = toStr(4, &4294967295).unwrap();
/// assert!(vec![255, 255, 255, 255] == s3);
/// ```
pub fn toStr<'a>(n: usize, x: &'a usize) -> Result<Vec<u8>, ConversionError> {
    let s: String = format!("{:b}", x.to_le());

    if n * 8 - s.len() > usize::max_value() {
        return Err(ConversionError::IntToStr);
    }

    let mut p: BitVec = BitVec::from_elem(n * 8 - s.len(), false);
    let mut b: BitVec = BitVec::from_fn(s.len(), |i| { s.char_at(i) == '1' });
    
    p.append(&mut b);
    Ok(p.to_bytes())
}

/// Returns a vector of integers obtained by breaking `S` into 4-byte chunks and little-endian
/// interpreting each chunk as as an unsigned integer.
///
/// # Examples
/// ```
/// use crypto::hs1util::toInts4;
///
/// let result: Vec<u32> = toInts4(&vec![0, 0, 0, 3]).unwrap();
/// assert!(result[0] == 3u32);
///
/// let another: Vec<u32> = toInts4(&vec![0, 0, 0, 5, 0, 0, 0, 6]).unwrap();
/// assert!(another[0] == 5u32);
/// assert!(another[1] == 6u32);
///
/// let and_another: Vec<u32> = toInts4(&vec![0, 0, 1, 0]).unwrap();
/// assert!(and_another[0] == 256u32);
///
/// let yet_another: Vec<u32> = toInts4(&vec![255, 255, 255, 255]).unwrap();
/// assert!(yet_another[0] == 4294967295u32);
/// ```
pub fn toInts4(S: &Vec<u8>) -> Result<Vec<u32>, ConversionError> {
    if S.len() % 4 !=  0 {
        println!("The length of S in bytes must be some multiple of 4.");
        return Err(ConversionError::StrToInt);
    }
    let mut ints: Vec<u32> = Vec::new();

    unsafe {
        let chunks: std::slice::Chunks<u8> = S.chunks(4);
        for c in chunks {
            ints.push(std::mem::transmute::<[u8; 4], u32>([c[0], c[1], c[2], c[3]]).to_be());
        }
    }
    Ok(ints)
}

/// Returns a vector of integers obtained by breaking `S` into 8-byte chunks and little-endian
/// interpreting each chunk as as an unsigned integer.
///
/// # Examples
/// ```
/// use crypto::hs1util::toInts8;
///
/// let result: Vec<u64> = toInts8(&vec![0, 0, 0, 0, 0, 0, 0, 3]).unwrap();
/// assert!(result[0] == 3u64);
///
/// let another: Vec<u64> = toInts8(&vec![0, 0, 0, 5, 0, 0, 0, 6, 255, 255, 255, 255, 0, 0, 1, 0]).unwrap();
/// println!("another = {:?}", another);
/// assert!(another[0] == 21474836486u64);
/// assert!(another[1] == 18446744069414584576u64);
///
/// let and_another: Vec<u64> = toInts8(&vec![0, 0, 0, 0, 0, 0, 1, 0]).unwrap();
/// assert!(and_another[0] == 256u64);
///
/// let yet_another: Vec<u64> = toInts8(&vec![255, 255, 255, 255, 255, 255, 255, 255]).unwrap();
/// assert!(yet_another[0] == 18446744073709551615u64);
/// ```
pub fn toInts8(S: &Vec<u8>) -> Result<Vec<u64>, ConversionError> {
    if S.len() % 8 !=  0 {
        println!("The length of S in bytes must be some multiple of 8.");
        return Err(ConversionError::StrToInt);
    }
    let mut ints: Vec<u64> = Vec::new();

    unsafe {
        let chunks: std::slice::Chunks<u8> = S.chunks(8);
        for c in chunks {
            ints.push(std::mem::transmute::<[u8; 8], u64>([c[0], c[1], c[2], c[3],
                                                           c[4], c[5], c[6], c[7]]).to_be());
        }
    }
    Ok(ints)
}

#[cfg(test)]
mod tests {
    use hs1util::*;

    #[test]
    fn test_hs1util_toStr_toInts4_3() {
        let orig: usize = 3;
        assert_eq!(toInts4(&toStr(4, &orig).unwrap()).unwrap()[0], orig as u32);
    }
    #[test]
    fn test_hs1util_toStr_toInts4_256() {
        let orig: usize = 256;
        assert_eq!(toInts4(&toStr(4, &orig).unwrap()).unwrap()[0], orig as u32);
    }
    #[test]
    fn test_hs1util_toStr_toInts4_4294967295() {
        let orig: usize = 4294967295;
        assert_eq!(toInts4(&toStr(4, &orig).unwrap()).unwrap()[0], orig as u32);
    }
    #[test]
    fn test_hs1util_toStr_toInts8_3() {
        let orig: usize = 3;
        assert_eq!(toInts8(&toStr(8, &orig).unwrap()).unwrap()[0], orig as u64);
    }
    #[test]
    fn test_hs1util_toStr_toInts8_256() {
        let orig: usize = 256;
        assert_eq!(toInts8(&toStr(8, &orig).unwrap()).unwrap()[0], orig as u64);
    }
    #[test]
    fn test_hs1util_toStr_toInts8_18446744073709551615() {
        let orig: usize = 18446744073709551615;
        assert_eq!(toInts8(&toStr(8, &orig).unwrap()).unwrap()[0], orig as u64);
    }
}
