use ark_ec::{
    pairing::Pairing,
    short_weierstrass::{Affine, SWCurveConfig},
    AffineRepr, CurveGroup,
};
use ark_ff::{Fp, Fp2, Fp2Config, FpConfig, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use num::{BigInt, BigUint, Integer, One, Signed};
use num_modular::ModularUnaryOps;

use crate::lego::{link::VK, VerifyingKey, VerifyingKeyWithLink};

pub trait Mod<E: Clone + Integer> {
    fn mod_exp(&self, e: &E, n: &Self) -> Self;

    fn commit(b: &[&Self], e: &[&E], n: &Self) -> Self;
}

impl Mod<BigInt> for BigUint {
    fn mod_exp(&self, e: &BigInt, n: &Self) -> Self {
        if e.is_negative() {
            self.invm(n).unwrap().modpow(e.magnitude(), n)
        } else {
            self.modpow(e.magnitude(), n)
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
        self.modpow(e, n)
    }

    fn commit(b: &[&Self], e: &[&BigUint], n: &Self) -> Self {
        let mut c = Self::one();
        for i in 0..b.len() {
            c = c * b[i].mod_exp(e[i], n) % n;
        }
        c
    }
}

pub trait OnChainVerifiable {
    fn to_on_chain_verifier(&self, name: &str) -> String;
}

impl<E: Pairing> OnChainVerifiable for VerifyingKeyWithLink<E>
where
    E::G1Affine: ToSolidity,
    E::G2Affine: ToSolidity,
{
    fn to_on_chain_verifier(&self, name: &str) -> String {
        let VerifyingKeyWithLink { groth16_vk, link_vk, .. } = self;
        let VerifyingKey {
            alpha_g1,
            beta_g2,
            gamma_g2,
            delta_g2,
            gamma_abc_g1,
            commit_witness_count,
            ..
        } = groth16_vk;
        let VK { c, a } = link_vk;

        let ic = gamma_abc_g1.to_sol_expr();
        let ic_len = gamma_abc_g1.len();
        let alpha_1 = alpha_g1.to_sol_expr();
        let beta_2 = beta_g2.to_sol_expr();
        let gamma_2 = gamma_g2.to_sol_expr();
        let delta_2 = delta_g2.to_sol_expr();
        let link = {
            let mut link = c.clone();
            link.push((-a.into_group()).into_affine());
            link.to_sol_expr()
        };
        let link_len = c.len() + 1;

        let pairing = "
            require(p1.length == p2.length, \"pairing-lengths-failed\");
            uint256 inputSize = p1.length * 6;
            uint256[] memory input = new uint256[](inputSize);
            for (uint256 i = 0; i < p1.length; i++) {
                input[i * 6 + 0] = p1[i][0];
                input[i * 6 + 1] = p1[i][1];
                input[i * 6 + 2] = p2[i][0][0];
                input[i * 6 + 3] = p2[i][0][1];
                input[i * 6 + 4] = p2[i][1][0];
                input[i * 6 + 5] = p2[i][1][1];
            }
            uint256[1] memory out;
            bool success;
            assembly {
                success := staticcall(
                    sub(gas(), 2000),
                    8,
                    add(input, 0x20),
                    mul(inputSize, 0x20),
                    out,
                    0x20
                )
                // Use \"invalid\" to make gas estimation work
                switch success
                case 0 {
                    invalid()
                }
            }
            require(success, \"pairing-opcode-failed\");
            return out[0];
        ";

        let mut s = String::new();
        s.push_str(&format!("
        pragma solidity ^0.8;

        import \"./pairing.sol\";
        
        contract {name}Verifier {{
            using Pairing for *;

            function verify_groth16(
                uint256[2] memory a,
                uint256[2][2] memory b,
                uint256[2] memory c,
                uint256[2] memory d,
                uint256[] memory input
            ) internal view returns (uint256 r) {{
                uint256[2][{ic_len}] memory IC = {ic};
                uint256[2] memory vk_x = Pairing.addition(d, IC[0]);
                for (uint256 i = 0; i < input.length; i++) {{
                    vk_x = Pairing.addition(
                        vk_x,
                        Pairing.scalar_mul(IC[i + 1], input[i])
                    );
                }}
        
                uint256[2][] memory p1 = new uint256[2][](4);
                uint256[2][2][] memory p2 = new uint256[2][2][](4);
                p1[0] = Pairing.negate(a);
                p1[1] = {alpha_1};

                p1[2] = vk_x;
                p1[3] = c;
                p2[0] = b;
                p2[1] = {beta_2};
                p2[2] = {gamma_2};
                p2[3] = {delta_2};
        
                {pairing}
            }}
        
            function verify_link(
                uint256[2][] memory p1
            ) internal view returns (uint256 r) {{
                uint256[2][2][{link_len}] memory p2 = {link};
                {pairing}
            }}

            function verify(
                uint256[2] memory a,
                uint256[2][2] memory b,
                uint256[2] memory c,
                uint256[2][] memory link,
                uint256[] memory input
            ) public view returns (uint256 r) {{                
                return verify_groth16(a, b, c, link[{commit_witness_count}], input) & verify_link(link);
            }}

        }}
        
        "));
        s
    }
}

pub trait ToTransaction {
    fn to_tx(&self) -> String;
}

impl<P: ToTransaction> ToTransaction for [P] {
    fn to_tx(&self) -> String {
        format!("[{}]", self.iter().map(|i| i.to_tx()).collect::<Vec<_>>().join(","))
    }
}

pub trait ToSolidity {
    fn to_sol_expr(&self) -> String;
    fn to_sol_assignment(&self, name: &str) -> String {
        format!("{} = {};", name, self.to_sol_expr())
    }
}

impl<P: ToSolidity> ToSolidity for [P] {
    fn to_sol_expr(&self) -> String {
        format!("[{}]", self.iter().map(|i| i.to_sol_expr()).collect::<Vec<_>>().join(","))
    }
}

impl ToTransaction for BigInt {
    fn to_tx(&self) -> String {
        format!("[{},{}]", self.magnitude().to_tx(), self.is_negative())
    }
}

impl ToTransaction for BigUint {
    fn to_tx(&self) -> String {
        format!(
            "\"0x{:0>width$x}\"",
            self,
            width = (self.bits().next_multiple_of(&256) as usize) >> 2
        )
    }
}

impl<const N: usize, P: FpConfig<N>> ToSolidity for Fp<P, N> {
    fn to_sol_expr(&self) -> String {
        format!("{}", self.into_bigint())
    }
}

impl<const N: usize, P: FpConfig<N>> ToTransaction for Fp<P, N> {
    fn to_tx(&self) -> String {
        let v: BigUint = self.into_bigint().into();
        format!("\"{:#x}\"", v)
    }
}

impl<P: Fp2Config> ToSolidity for Fp2<P> {
    fn to_sol_expr(&self) -> String {
        format!("[{},{}]", self.c1.into_bigint(), self.c0.into_bigint())
    }
}

impl<P: Fp2Config> ToTransaction for Fp2<P> {
    fn to_tx(&self) -> String {
        let c1: BigUint = self.c1.into_bigint().into();
        let c0: BigUint = self.c0.into_bigint().into();
        format!("[\"{:#x}\",\"{:#x}\"]", c1, c0)
    }
}

impl<P: SWCurveConfig> ToSolidity for Affine<P>
where
    P::BaseField: ToSolidity,
{
    fn to_sol_expr(&self) -> String {
        format!("[{},{}]", self.x.to_sol_expr(), self.y.to_sol_expr())
    }
}

impl<P: SWCurveConfig> ToTransaction for Affine<P>
where
    P::BaseField: ToTransaction,
{
    fn to_tx(&self) -> String {
        format!("[{},{}]", self.x.to_tx(), self.y.to_tx())
    }
}

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
