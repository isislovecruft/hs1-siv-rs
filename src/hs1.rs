// XXX Pick a license
//
// Authors: Isis Agora Lovecruft <isis@en.ciph.re> 0xA3ADB67A2CDB8B35

/*! A reference implementation of the HS1-SIV symmetric, authenticated-encryption cipher. */

// We use variable and function names from the HS1-SIV paper throughout this implementation, most
// of which do not conform to Rust's standard of using snake case.
#![allow(non_snake_case)]

use std::cmp::min;
use std::iter::{Extend, repeat};
use std::mem::transmute;
use std::result::Result;
use std::slice::Chunks;
use std::vec::Vec;

use chacha20::ChaCha20;
use cryptoutil::xor_keystream;
use symmetriccipher::SynchronousStreamCipher;


/// May be raised upon HS1 decryption when the authenticator cannot be verified.
#[derive(Debug, Clone, Copy)]
pub struct AuthenticationError;

/// HS1-SIV key material.
///
/// A Key is a vector `(kS, kN, kP, kA)`, where:
///
/// * `kS`, is a string of 32 bytes,
/// * `kN`, is a vector of `b/4 + 4(t-1)` integers from ℤ_2^32,
/// * `kP`, is a vector of `t` integers from ℤ_2^60, and
/// * `kA`, is a vector of `3t` integers from ℤ_2^64,
#[derive(Clone)]
pub struct Key{
    S: [u8; 32],
    N: Vec<u32>,
    P: Vec<u64>,
    A: Vec<u64>,
}

/// Parameters for initialising HS1-SIV with established levels of varying security and efficiency.
///
/// There are four parameters used throughout this specification: `b`, `t`, `r`, and `l`.
///
/// # Pre-defined Parameter Sets
///
/// Most likely, you should only ever need to use one of the following pre-defined sets of
/// parameters:
///
///    * `HS1_SIV_LO` is a pre-defined set of `Parameters` where `b=64`, `t=2`, `r=8`, and `l=8`.
///    * `HS1_SIV` is a pre-defined set of `Parameters` where `b=64`, `t=4`, `r=12`, and `l=16`.
///    * `HS1_SIV_HI` is a pre-defined set of `Parameters` where `b=64`, `t=6`, `r=20`, and `l=32`.
///
/// Parameter `b` specifies the number of bytes used in part of the hashing algorithm (larger `b`
/// tends to produce higher throughput on longer messages).
///
/// Parameter `t` selects the collision level of the hashing algorithm (higher `t` produces higher
/// security and lower throughput).
///
/// Parameter `r` specifies the number of internal rounds used by the stream cipher (higher `r`
/// produces higher security and lower throughput).
///
/// Parameter `l` specifies the byte-length of synthetic IV used (higher `l` improves security and
/// increases ciphertext lengths by `l` bytes).
#[derive(Clone, Copy)]
pub struct                          Parameters{b: u8, t: u8, r: u8, l: u8}
pub static HS1_SIV_LO: Parameters = Parameters{b: 64, t:  2, r:  8, l:  8};
pub static    HS1_SIV: Parameters = Parameters{b: 64, t:  4, r: 12, l: 16};
pub static HS1_SIV_HI: Parameters = Parameters{b: 64, t:  6, r: 20, l: 32};

/// HS1-SIV uses a new PRF called HS1 to provide authenticated encryption via Rogaway and
/// Shrimpton’s SIV mode [6].  HS1 (mnemonic for “Hash-Stream 1”) is designed for high software
/// speed on systems with good 32-bit processing, including Intel SSE, ARM Neon, and 32-bit
/// architectures without SIMD support. HS1 uses a universal hash function to consume arbitrary
/// strings and a stream cipher to produce its output.
///
/// # Features
///
/// HS1-SIV is designed to have the following features.
///
/// ## Competitive speed on multiple architectures.
/// HS1-SIV is designed to exploit 32-bit multiplication and SIMD processing, which are
/// well-supported on almost all current CPUs.  This ensures a consistent performance profile over a
/// wide range of processors, including modern embedded ones.
///
/// ## Provable security.
/// HS1-Hash and SIV are based on well-known and proven constructions. [4] [6]
///
/// The only security assumption needed is that the Chacha stream cipher is a good pseudo-random
/// generator and secure against related-key attacks.
///
/// ## Nonce misuse resistant.
/// No harm is done when a nonce is reused, except that it is revealed whether corresponding
/// (associated data, plaintext) pairs have been repeated. If (associated data, plaintext) pairs are
/// known to never repeat, no nonce need be used at all.
///
/// ## Scalable.
/// Different security levels are available for different tasks, with varying throughput.
///
/// ## General-purpose PRF.
/// The general nature of HS1 makes it useful for a variety of tasks, such as entropy harvesting,
/// random generation, and other IV-based encryption and authentication schemes. A single software
/// library could provide multiple services under a single key by simply partitioning the nonce
/// space and providing access to HS1.  With the exception of provable security, all of the above
/// features are improvements over GCM.
///
pub struct HS1 {
    /// The parameter set which HS1-SIV was initialised with.
    parameters: Parameters,
    // An instance of the ChaCha fast stream cipher, used internally for subkey derivation.
    //chacha: ChaCha20,
    // Symmetric authentication-encryption key material.
    //key: Key,
}

pub trait Subkeygen {
    fn subkeygen(&self, K: &[u8]) -> Key;
}

pub trait PRF {
    fn prf(&self, k: &Key, M: &String, N: &Vec<u8>, y: i64) -> Vec<u8>;
}

pub trait Hash {
    fn hash(&self, kN: &Vec<u32>, kP: &u64, kA: &Vec<u64>, M: &Vec<u8>) -> Vec<u8>;
}

pub trait Encrypt {
    fn encrypt(&self, K: &[u8], M: &String, A: &String, N: &Vec<u8>) -> (String, String);
}

pub trait Decrypt {
    fn decrypt(&self, K: &[u8], T: &String, C: &String, A: &String, N: &Vec<u8>)
               -> Result<String, AuthenticationError>;
}

impl HS1 {
    /// Initialise a new HS1 cipher and it's underlying ChaCha cipher and state.
    // pub fn new(params: Parameters, key: &[u8], nonce: &[u8]) -> HS1 {
    //     let rounds: Option<i8> = Some(params.r as i8);
    //     let hs1:    HS1        = HS1{ parameters: params };
    //     let k:      Key        = HS1::subkeygen(key);
    // 
    //     hs1.chacha = ChaCha20::new(&k.S, &nonce, rounds);
    //     hs1
    // }
    pub fn new(parameters: Parameters) -> HS1 {
        HS1{ parameters: parameters }
    }
}

/// HS1-Subkeygen takes any length key and uses ChaCha to produce all internal keys needed by HS1.
///
/// # Inputs
///
/// - `K`, a non-empty string of up to 32 bytes
///
/// # Output
///
/// - `k`, a vector `(KS, kN, kP, kA)`, where:
///   - `kS`, is a string of 32 bytes,
///   - `kN`, is a vector of `b/4 + 4(t-1)` integers from ℤ_2^32,
///   - `kP`, is a vector of `t` integers from ℤ_2^60, and
///   - `kA`, is a vector of `3t` integers from ℤ_2^64,
///
/// # Algorithm
///
/// 1. ChachaLen = 32
/// 2. NHLen = b + 16(t-1)
/// 3. PolyLen = 8t
/// 4. ASULen = 24t
/// 5. y = ChachaLen + NHLen + PolyLen + ASULen
/// 6. K' = (K || K || K || K || …)[0, 32]
/// 7. N = toStr(12, b*2^48 + t*2^40 + r*2^32 + l*2^16 + |K|)
/// 8. T = Chacha[r](K', 0, N, 0^y)`, where:
///    - K' is a 32-byte key,
///    - 0 is the initial counter value,
///    - N is a 12-byte IV, and
///    - 0^y is a y-byte string comprised entirely of `0`s, which will be encrypted to
///      produce the new subkey.
/// 9.  kS = T[0, ChachaLen]
/// 10. kN = toInts(4, T[ChachaLen, NHLen])
/// 11. kP = map(mod 2^60, toInts(8, T[ChachaLen, + NHLen, PolyLen]))
/// 12. kA = toInts(8, T[ChachaLen + NHLen + PolyLen, ASULen])

impl Subkeygen for HS1 {
    fn subkeygen(&self, K: &[u8]) -> Key {
        let chachaLen:  usize = 32;
        let nhLen:      usize = self.parameters.b as usize + 16 * (self.parameters.t as usize - 1);
        let polyLen:    usize =  8 * self.parameters.t as usize;
        let asuLen:     usize = 24 * self.parameters.t as usize;
        let y:          usize = chachaLen + nhLen + polyLen + asuLen;
        let mut kPrime: [u8; 32];
        let mut N:      Vec<u8>;
        let mut out:    Vec<u8> = repeat(0).take(y).collect();

        if K.len() >= 32 {
            kPrime = take32(K);
        } else {
            let mut kVec: Vec<u8> = Vec::with_capacity(32);
            while kVec.len() < 32 {
                for byte in K.iter() {
                    kVec.push(*byte);
                }
            }
            kPrime = take32(&kVec[..]);
        }
        assert_eq!(kPrime.len(), 32);

        N = toStr(12, &(self.parameters.b as u64 * 2u64.pow(48) +
                        self.parameters.t as u64 * 2u64.pow(40) +
                        self.parameters.r as u64 * 2u64.pow(32) +
                        self.parameters.l as u64 * 2u64.pow(16) +
                        K.len() as u64)).into_bytes();
        N.truncate(12);

        ChaCha20::new(&kPrime, &[0u8], Some(self.parameters.r as i8)).process(&N[..], &mut out[..]);
        assert_eq!(out.len(), y); // XXX check that chacha is really returning y bytes to us

        Key {
            // XXX oh god… the syntax of .. all over the place in this section is fucking horrible.
            S: take32(&out[..chachaLen]),  // XXX would be nice to remove the take32() here…
            N: toInts4(&out[chachaLen..][..nhLen].to_vec()),
            P: toInts8(&out[chachaLen + nhLen..][..polyLen].to_vec()).iter().map(|x| *x % 2u64.pow(60)).collect(),
            A: toInts8(&out[chachaLen + nhLen + polyLen..][..asuLen].to_vec()),
        }
    }
}

// XXX_QUESTION: The equation of step #2 in the paper appears to be missing a parenthesis.

/// Hash `M` a total of `t` times with different keys and combine the result with the stream
/// cipher’s key.
///
/// # Inputs
///
/// - `k`, a vector `(KS, kN, kP, kA)`, where
///   - `kS`, is a string of 32 bytes,
///   - `kN`, is a vector of `b/4 + 4(t-1)` integers from ℤ_2^32,
///   - `kP`, is a vector of `t` integers from ℤ_2^60, and
///   - `kA`, is a vector of `3t` integers from ℤ_2^64,
/// - `M`, a string of any length,
/// - `N`, a 12-byte string,
/// - `y`, a integer in ℤ_2^38
///
/// # Output
///
/// - `Y`, a string of `y` bytes
///
/// # Algorithm
///
/// 1. A_i = HS1-Hash[b,t](kN[4i, b/4], kP[i], kA[3i, 3], M) for each 0 ≤ i < t
/// 2. Y   = ChaCha[r](pad(32, A_0 || A_1 || … || A_(t-1)) ⊕ kS), 0, N, 0^y)
///
/// # Side Channels
///
/// An adversary with the ability to conduct timing-based side channel attacks on a machine running
/// this code will some advantage to determine the `Parameter` set used (i.e. `HS1_SIV_LO`,
/// `HS1_SIV`, `HS1_SIV_HI`).
///
/// # Example
// XXX rewrite example
/// ```
/// use num::pow;
///
/// let hs1    = &HS1_SIV;
/// let n_elem = get_kN_length(hs1.parameters);
/// let mut kS: Vec<i8>         = Vec::with_capacity(32);
/// let mut kN: Vec<i32>        = Vec::with_capacity(n_elem);
/// let mut kP: Vec<i64>        = Vec::with_capacity(hs1.parameters.t);
/// let mut kA: Vec<i64>        = Vec::with_capacity(hs1.parameters.t * 3);
/// let mut k:  Vec<Vec<isize>> = Vec::with_capacity(4);
/// let M: String = "foo bar baz qux";
/// let N: String = "aaaaaaaaaaaa";
/// let y: i64 = 80507069266;
///
/// // Put some static bytes and integers into the test vectors:
/// for i in 0..32 {
///     kS.push(0xAA);
/// }
/// for i in 0..n_elem {
///     kN.push(num::pow(2, 32) - 1);
/// }
/// for i in 0..hs1.parameters.t {
///     kP.push(num::pow(2, 60) - 1);
/// }
/// for i in 0..hs1.parameters.t * 3 {
///     kA.push(num::pow(2, 64) - 1);
/// }
/// k = vec![KS, kN, kP, KA];
///
/// let result = hs1::prf(&k, &M, &N, &y);
/// println!("HS1-PRF result is {}", result);
/// ```
impl PRF for HS1 {
    fn prf(&self, k: &Key, M: &String, N: &Vec<u8>, y: i64) -> Vec<u8> {
        assert_eq!(N.len(), 12);

        let mut A:   Vec<u8> = Vec::with_capacity(self.parameters.t as usize);
        let mut key: Vec<u8> = repeat(0).take(y as usize).collect();
        let mut out: Vec<u8> = repeat(0).take(y as usize).collect();

        // 1. `A_i = HS1-Hash[b,t](kN[4i, b/4], kP[i], kA[3i, 3], M) for each 0 ≤ i < t`
        for i in 0 .. self.parameters.t {
            let a: Vec<u32> = k.N[i as usize * 4 .. (self.parameters.b / 4) as usize].to_vec();
            let b: u64      = k.P[i as usize];
            let c: Vec<u64> = k.A[i as usize * 3 .. 3].to_vec();

            let hashed = self.hash(&a, &b, &c, &M.clone().into_bytes());
            for byte in hashed.iter() {
                A.push(*byte); // Concatenate A_i (either 4 or 8 bytes) into the input
            }
        }
        // 2. `Y   = ChaCha[r](pad(32, A_0 || A_1 || … || A_(t-1)) ⊕ kS), 0, N, 0^y)`
        xor_keystream(&mut key, &pad(32, &A), &k.S[..]);
        ChaCha20::new(&key, &[0u8], Some(self.parameters.r as i8)).process(&N[..], &mut out[..]);
        out.to_vec()
    }
}

// XXX_QUESTION: In step #5 of HS1-SIV-Hash, it is written `kP ^ (n-1)`, etc.  However in the notation
// section of the paper, it says:
//
// > A string of k zero-bytes is represented 0^k.
//
// Are we supposed to raise the vector `kP` to the power of `(n-1)`, or are we supposed to take
// that many bytes from the vector?

/// The hash family HS1-Hash is `(1/2^(28) + l/b2^(60))-AU` for all `M` up to `l` bytes, when
/// `k_N` and `k_P` are chosen randomly and `t ≤ 4`.
///
/// The hash family is `(1/2^(28) + 1/2^(32) + l/b2^(60))-SU` when additionally `k_A` is
/// randomly chosen and `t > 4`.
///
/// # Inputs
///
/// - `kN`, is a vector of `b/4` integers from ℤ_2^32,
/// - `kP`, is an integer from ℤ_2^60,
/// - `kA`, is a vector of 3 integers from ℤ_2^64,
/// - `M`, a string of any length.
///
/// # Output
///
/// - `Y`, an 8-byte (if t ≤ 4) or 4-byte (if t > 4) string.
///
/// # Algorithm:
///
/// 1. n = max(⌈|M|/b⌉, 1)
/// 2. M_1 || M_2 || … || M_n = M and |M_i| = b for each 1 ≤ i ≤ n.
/// 3. m_i = toInts(4, pad(16, M_i)) for each 1 ≤ i ≤ n.
/// 4. a_i = NH(kN, m_i) mod 2^60 + (|M_i| mod 16) for each 1 ≤ i ≤ n.
/// 5. h = kP^n + (a_1 × kP^(n-1)) + (a_2 × kP^(n-2)) + … + (a_n × kP^0) mod (2^61 - 1)
/// 6. if (t ≤ 4) Y = toStr(8, h)
/// 7. else Y = toStr(4, (kA[0] + kA[1] × (h mod 2^32) + kA[2] × (h div 2 ^32)) div 2^32)

impl Hash for HS1 {
    fn hash(&self, kN: &Vec<u32>, kP: &u64, kA: &Vec<u64>, M: &Vec<u8>) -> Vec<u8> {
        let n:     u32;
        let Mi:    Chunks<u8>;
        let mut a: Vec<u32> = Vec::new();
        let mut Y: Vec<u8>;

        // 1. n = max(⌈|M|/b⌉, 1)
        n = if M.len() < 1 { 1 } else { M.len() as u32 / self.parameters.b as u32 };

        // 2. M_1 || M_2 || … || M_n = M and |M_i| = b for each 1 ≤ i ≤ n.
        Mi = M.chunks(self.parameters.b as usize);

        // 3. m_i = toInts(4, pad(16, M_i)) for each 1 ≤ i ≤ n.
        for (chunk, _) in Mi.enumerate() {
            let padded: Vec<u8>  = pad(16, &vec!(chunk as u8));
            let mi:     Vec<u32> = toInts4(&padded);

            // 4. a_i = NH(kN, m_i) mod 2^60 + (|M_i| mod 16) for each 1 ≤ i ≤ n.
            a.push(&nh(kN, &mi) % 2u32.pow(60) + (self.parameters.b as u32 % 16));
        }

        // 5. h = kP^n + (a_1 × kP^(n-1)) + (a_2 × kP^(n-2)) + ... + (a_n × kP^0) mod (2^61 - 1)
        let mut h:   u64 = kP.pow(n);
        for (ai, j) in a.iter().zip(n .. 0) {
            h += *ai as u64 * kP.pow(j);
        }
        h = h % (2u64.pow(61) - 1); // XXX Maybe we should define a Wrapping<T> for h?

        // 6. if (t ≤ 4) Y = toStr(8, h)
        if self.parameters.t <= 4 {
            Y = toStr(8, &h).into_bytes();
            Y.truncate(8);
        } else {
            // 7. else Y = toStr(4, (kA[0] + kA[1] × (h mod 2^32) + kA[2] × (h div 2 ^32)) div 2^32)
            let modulus: u64 = 2u64.pow(32);
            Y = toStr(4, &((kA.get(0).unwrap() +
                            kA.get(1).unwrap() * (h % modulus) +
                            kA.get(2).unwrap() * (h / modulus)) / modulus)).into_bytes();
            Y.truncate(4);
        }
        Y
    }
}

/// The `l`-byte string `T` serves as authenticator for `A` and `M`, and serves as IV for the
/// encryption of `M`.  If `N` is a nonce, then repeat encryptions yield different `T` and `C`.
/// Algorithm parameters `b`, `t`, `r`, and `l` effect security and performance.
///
/// # Inputs
///
/// - `K`, a non-empty string of up to 32 bytes,
/// - `M`, a string shorter than 2^64 bytes,
/// - `A`, a string shorter than 2^64 bytes,
/// - `N`, a 12-byte string
///
/// # Output
///
/// - `(T, C)`, strings of `l` and `|M|` bytes, respectively.
///
/// # Algorithm:
///
/// 1. k = HS1-subkeygen[b,t,r,l](K)
/// 2. M' = pad(16, A) || pad(16, M) || toStr(8, |A|) || toStr(8, |M|)
/// 3. T = HS1[b,t,r](k, M', N, l)
/// 4. C = M ⊕ HS1[b,t,r](k, T, N, 64 + |M|)[64, |M|]

impl Encrypt for HS1 {
    fn encrypt(&self, K: &[u8], M: &String, A: &String, N: &Vec<u8>) -> (String, String) {
        assert!(K.len() <= 32);
        assert!(M.len() <  2usize.pow(64));
        assert!(A.len() <  2usize.pow(64));
        assert!(N.len() == 12);

        let k:       Key = self.subkeygen(&K);
        let m:       String;
        let C:       String;
        let T:       String;
        let t:       Vec<u8>;
        let mut out: Vec<u8> = repeat(0).take(M.len()).collect();

        m = [padStr(16, &A),
             padStr(16, &M),
             toStr(8, &(A.len() as u64)),
             toStr(8, &(M.len() as u64))].concat();

        t = self.prf(&k, &m, &N, self.parameters.l as i64);
        T = String::from_utf8(t).unwrap();
        xor_keystream(&mut out[..], M.as_bytes(),
                      &self.prf(&k, &T, &N, (64 + M.len()) as i64)[..]);
        C = String::from_utf8(out.to_vec()).unwrap();

        assert_eq!(T.len(), self.parameters.l as usize);
        assert_eq!(C.len(), M.len());

        (T, C)
    }
}

// XXX_QUESTION: In the "Algorithm" section of Fig.5: Decryption, the numbering got all wonky.

/// The `l`-byte string `T` serves as authenticator for `A` and `M`, and serves as IV for the
/// decryption of `C`. Algorithm parameters `b`, `t`, `r`, and `l` effect security and
/// performance.
///
/// # Inputs:
///
/// - `K`, a non-empty string of up to 32 bytes,
/// - `(T, C)`, an `l`-byte string and a string shorter than 2^64 bytes, respectively.
/// - `A`, a string shorter than 2^64 bytes,
/// - `N`, a 12-byte string
///
/// # Output
///
/// - `M`, a `|C|`-byte string, or `AuthenticationError`.
///
/// # Algorithm:
///
/// 1. k = HS1-subkeygen[b,t,r,l](K)
/// 2. M = C ⊕ HS1[b,t,r](k, T, N, 64 + |C|)[64, |C|]
/// 3. M' = pad(16, A) || pad(16, M) || toStr(8, |A|) || toStr(8, |M|)
/// 4. T' = HS1[b,t,r](k, M', N, l)
/// 5. if (T = T') then return M
/// 6. else return AuthenticationError

impl Decrypt for HS1 {
    fn decrypt(&self, K: &[u8], T: &String, C: &String, A: &String, N: &Vec<u8>)
               -> Result<String, AuthenticationError> {
        assert!(K.len() <= 32);
        assert!(T.len() == self.parameters.l as usize);
        assert!(C.len() < 2usize.pow(64));
        assert!(A.len() <  2usize.pow(64));
        assert!(N.len() == 12);

        let k:       Key = self.subkeygen(&K);
        let M:       String;
        let m:       String;
        let t:       String;
        let mut out: Vec<u8> = repeat(0).take(C.len()).collect();

        xor_keystream(&mut out[..], &C.as_bytes(),
                      &self.prf(&k, &T, N, (64 + C.len()) as i64)[64 .. C.len()]);
        M = String::from_utf8(out.to_vec()).unwrap();
        m = [padStr(16, &A),
             padStr(16, &M),
             toStr(8, &(A.len() as u64)),
             toStr(8, &(M.len() as u64))].concat();
        t = String::from_utf8(self.prf(&k, &m, N, self.parameters.l as i64)).unwrap();

        if *T == *t { Ok(M) } else { Err(AuthenticationError) }
    }
}

//-------------------------------------------------------------------------------------------------
//                                      Utility Functions
//-------------------------------------------------------------------------------------------------

/// Pad the `input` to the given `length` by adding 0s to the end of the `input`.
///
/// # Inputs
///
///  * `length` is an integer specifying the length to pad to.
///  * `input` is a `vec::Vec<u8>` (a.k.a. a vector of octets).
///
/// # Examples
///
///     let foo: mut [u8] = [0x41, 0x42, 0x43];
///     pad(5, foo);
///     assert_eq!(foo, [0x41, 0x42, 0x43, 0x00, 0x00])

fn pad(multiple: usize, input: &Vec<u8>) -> Vec<u8> {
    let needed:     usize   = input.len() % multiple;
    let mut padded: Vec<u8> = input.clone();

    for _ in 0..needed {
        padded.push(0x00);
    }
    padded
}

/// Utility for using pad() on a std::str::String.
fn padStr(multiple: usize, input: &String) -> String {
    let mut i: Vec<u8> = Vec::with_capacity(input.len());

    i.extend(input.as_bytes());

    String::from_utf8(pad(multiple, &i)).unwrap()
}

/// Given vectors of integers, `v1` and `v2`, returns the result of the following algorithm:
///
///                   n/4 ⎛                                         ⎞
///     NH(v1, v2) =   Σ  ⎜(v1[4i-3]+v2[4i-3]) × (v1[4i-1]+v2[4i-1])⎟
///                   i=1 ⎝ + (v1[4i-2]+v2[4i-2]) × (v1[4i]+v2[4i]) ⎠
///
/// where `n = min(|v1|, |v2|)` and is alway a multiple of 4.

fn nh(v1: &Vec<u32>, v2: &Vec<u32>) -> u32 {
    let mut sum: u32   = 0;
    let n:       usize = min(v1.len(), v2.len());

    for i in 1..n/4 {
        let a1: &u32 = v1.get(4 * i - 3).unwrap();
        let a2: &u32 = v2.get(4 * i - 3).unwrap();
        let b1: &u32 = v1.get(4 * i - 1).unwrap();
        let b2: &u32 = v2.get(4 * i - 1).unwrap();
        let c1: &u32 = v1.get(4 * i - 2).unwrap();
        let c2: &u32 = v2.get(4 * i - 2).unwrap();
        let d1: &u32 = v1.get(4 * i).unwrap();
        let d2: &u32 = v2.get(4 * i).unwrap();
        sum += (a1 + a2) * (b1 + b2) + (c1 + c2) * (d1 + d2);
    }
    sum
}

/// Returns a vector of integers obtained by breaking `S` into `n`-byte chunks and little-endian
/// interpreting each chunk as as an unsigned integer.
///
/// # Example:
///
///     let result: Vec<u32> = toInts(2, 0x05000600);
///     assert!(Some(result.first) == 5);
///     assert!(Some(result.last)  == 6);
// XXX see i64::from_str_radix()
fn toInts4(S: &Vec<u8>) -> Vec<u32> {
    assert_eq!(S.len() % 4, 0); // The string should be some multiple of 4 bytes

    let mut ints: Vec<u32> = Vec::new();

    unsafe {
        let chunks: Chunks<u8> = S.chunks(4);
        for chunk in chunks {
            let fixed: [u8; 4] = take4(chunk);
            let mutated: u32 = transmute::<[u8; 4], u32>(fixed);
            ints.push(mutated);
        }
    }
    ints
}

// TODO: Can we make this generic to the above toInts4() function?
fn toInts8(S: &Vec<u8>) -> Vec<u64> {
    assert_eq!(S.len() % 8, 0); // The string should be some multiple of 8 bytes

    let mut ints: Vec<u64> = Vec::new();

    unsafe {
        let chunks: Chunks<u8> = S.chunks(8);
        for chunk in chunks {
            let fixed: [u8; 8] = take8(chunk);
            let mutated: u64 = transmute::<[u8; 8], u64>(fixed);
            ints.push(mutated);
        }
    }
    ints
}

/// `toStr(n, x)` is the n-byte unsigned little-endian binary representation of integer x.
///
/// # Example
///
/// assert!(toStr(2, 3) == 0x0300);
///
fn toStr <'a> (n: usize, x: &'a u64) -> String {
    let y: String = x.to_le().to_string();
    padStr(n, &y)
}

fn take4  <'a> (x: &'a [u8]) -> [u8; 4] {
    assert!(x.len() >= 4);
    [x[0], x[1], x[2], x[3]]
}

fn take8  <'a> (x: &'a [u8]) -> [u8; 8] {
    assert!(x.len() >= 8);
    [x[0], x[1], x[2], x[3],
     x[4], x[5], x[6], x[7]]
}

fn take32 <'a> (x: &'a [u8]) -> [u8; 32] {
    assert!(x.len() >= 12);
    [x[0],  x[1],  x[2],  x[3],
     x[4],  x[5],  x[6],  x[7],
     x[8],  x[9],  x[10], x[11],
     x[12], x[13], x[14], x[15],
     x[16], x[17], x[18], x[19],
     x[20], x[21], x[22], x[23],
     x[24], x[25], x[26], x[27],
     x[28], x[29], x[30], x[31]]
}

#[cfg(test)]
mod tests {
    use hs1::{HS1_SIV_LO, HS1_SIV, HS1_SIV_HI};
    use hs1::{HS1, AuthenticationError, Key};
    use hs1::{Subkeygen, Encrypt, Decrypt, PRF};

    static test_key_32_bytes: [u8; 32] = [
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16,
        0x17, 0x18, 0x19, 0x20, 0x21, 0x22, 0x23, 0x24,
        0x25, 0x26, 0x27, 0x28, 0x29, 0x30, 0x31, 0x32,];

    #[test]
    fn test_hs1_siv_hi_init() {
        let key: Key = HS1::subkeygen(test_key_32_bytes);
        let hs1: HS1 = HS1::new(HS1_SIV_HI, key, &[0u8]);
    }
}
