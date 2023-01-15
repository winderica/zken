use ark_ec::AffineRepr;
use ark_ff::{Fp2, Fp256, FpConfig, Fp2Config, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use num::{bigint::Sign, BigInt, BigUint, Integer, One, Signed};
use num_modular::{ModularPow, ModularUnaryOps};

pub trait ToVecF<F: PrimeField> {
    fn to_vec_f(&self, width: usize) -> Vec<F>;
}

pub trait Mod<E: Clone + Integer> {
    fn mod_exp(&self, e: &E, n: &Self) -> Self;

    fn commit(b: &[&Self], e: &[&E], n: &Self) -> Self;
}

impl Mod<BigInt> for BigUint {
    fn mod_exp(&self, e: &BigInt, n: &Self) -> Self {
        if e.is_negative() {
            self.invm(n).unwrap().powm(e.magnitude(), n)
        } else {
            self.powm(e.magnitude(), n)
        }
    }

    fn commit(b: &[&Self], e: &[&BigInt], n: &Self) -> Self {
        let mut c = Self::one();
        for i in 0..b.len() {
            c = c * b[i].mod_exp(e[i], n) % n;
        }
        c
    }
}

impl Mod<BigUint> for BigUint {
    fn mod_exp(&self, e: &BigUint, n: &Self) -> Self {
        self.powm(e, n)
    }

    fn commit(b: &[&Self], e: &[&BigUint], n: &Self) -> Self {
        let mut c = Self::one();
        for i in 0..b.len() {
            c = c * b[i].mod_exp(e[i], n) % n;
        }
        c
    }
}

// pub trait ToHex {
//     fn to_hex(&self) -> String;
// }

// pub trait ToTransaction {
//     fn to_tx(&self) -> String;
// }

// impl<P: ToTransaction> ToTransaction for [P] {
//     fn to_tx(&self) -> String {
//         format!("[{}]", self.iter().map(|i| i.to_tx()).collect::<Vec<_>>().join(","))
//     }
// }

// pub trait ToSolidity {
//     fn to_sol_expr(&self) -> String;
//     fn to_sol_assignment(&self, name: &str) -> String {
//         format!("{} = {};", name, self.to_sol_expr())
//     }
// }

// impl<P: ToSolidity> ToSolidity for [P] {
//     fn to_sol_expr(&self) -> String {
//         format!("[{}]", self.iter().map(|i| i.to_sol_expr()).collect::<Vec<_>>().join(","))
//     }
// }

// impl<P: FpConfig<256>> ToSolidity for Fp256<P> {
//     fn to_sol_expr(&self) -> String {
//         format!("0x{}", BigUint::from(self.0))
//     }
// }

// impl ToHex for BigInt {
//     fn to_hex(&self) -> String {
//         let hex = self.abs().to_str_radix(16);
//         format!("hex\"{:0>width$}\"", hex, width = hex.len().div_ceil(64) * 64)
//     }
// }

// impl ToTransaction for BigInt {
//     fn to_tx(&self) -> String {
//         let sign = match self.sign() {
//             Sign::Minus => "true",
//             _ => "false",
//         };
//         let hex = self.abs().to_str_radix(16);
//         format!("\"0x{:0>width$}\",\"{}\"", hex, sign, width = hex.len().div_ceil(64) * 64)
//     }
// }

// impl ToHex for BigUint {
//     fn to_hex(&self) -> String {
//         let hex = self.to_str_radix(16);
//         format!("hex\"{:0>width$}\"", hex, width = hex.len().div_ceil(64) * 64)
//     }
// }

// impl ToTransaction for BigUint {
//     fn to_tx(&self) -> String {
//         let hex = self.to_str_radix(16);
//         format!("\"0x{:0>width$}\"", hex, width = hex.len().div_ceil(64) * 64)
//     }
// }

// impl<P: FpConfig<256>> ToHex for Fp256<P> {
//     fn to_hex(&self) -> String {
//         format!("hex\"{}\"", self.into_bigint())
//     }
// }

// impl<P: FpConfig<256>> ToTransaction for Fp256<P> {
//     fn to_tx(&self) -> String {
//         format!("\"0x{}\"", self.into_bigint())
//     }
// }

// impl<P: Fp2Config> ToSolidity for Fp2<P> {
//     fn to_sol_expr(&self) -> String {
//         format!("[0x{},0x{}]", self.c1.into_bigint(), self.c0.into_bigint())
//     }
// }

// impl<P: Fp2Config> ToTransaction for Fp2<P> {
//     fn to_tx(&self) -> String {
//         format!("[\"0x{}\",\"0x{}\"]", self.c1.into_bigint(), self.c0.into_bigint())
//     }
// }

// impl<P: SWModelParameters> ToSolidity for AffineRepr<P>
// where
//     P::BaseField: ToSolidity,
// {
//     fn to_sol_expr(&self) -> String {
//         format!("[{},{}]", self.x.to_sol_expr(), self.y.to_sol_expr())
//     }
// }

// impl<P: SWModelParameters> ToTransaction for AffineRepr<P>
// where
//     P::BaseField: ToTransaction,
// {
//     fn to_tx(&self) -> String {
//         format!("[{},{}]", self.x.to_tx(), self.y.to_tx())
//     }
// }

pub struct SerdeAs;

impl<T> serde_with::SerializeAs<T> for SerdeAs
where
    T: CanonicalSerialize,
{
    fn serialize_as<S>(val: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut bytes = vec![];
        val.serialize_uncompressed(&mut bytes).map_err(serde::ser::Error::custom)?;

        serde_with::Bytes::serialize_as(&bytes, serializer)
    }
}

impl<'de, T> serde_with::DeserializeAs<'de, T> for SerdeAs
where
    T: CanonicalDeserialize,
{
    fn deserialize_as<D>(deserializer: D) -> Result<T, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let bytes: Vec<u8> = serde_with::Bytes::deserialize_as(deserializer)?;
        T::deserialize_uncompressed_unchecked(&mut &bytes[..]).map_err(serde::de::Error::custom)
    }
}
