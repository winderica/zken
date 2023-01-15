use std::borrow::Borrow;

use ark_ff::{PrimeField, BigInteger};
use ark_r1cs_std::{
    prelude::{AllocVar, AllocationMode, Boolean, EqGadget},
    select::CondSelectGadget,
    R1CSVar, fields::fp::FpVar, ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use num::{BigUint, One, Zero, Integer};
use num_modular::{ModularCoreOps, ModularUnaryOps};
use secp256k1::SecretKey;

use crate::primitives::{bn::BigUintVar, poseidon::{PoseidonParameters, constraints::CRHGadget}};

pub fn parse_pk(pk: &[u8]) -> (BigUint, BigUint) {
    match pk.len() {
        33 => {
            let x = BigUint::from_bytes_be(&pk[1..33]);

            let m = (BigUint::one() << 256u32) - BigUint::from(4294968273u128);
            let y = {
                let yy = (&x * &x * &x + BigUint::from(7u8)) % &m;
                let y = yy.modpow(&((&m + BigUint::one()) >> 2u8), &m);
                if y.is_even() != pk[0].is_even() {
                    m - y
                } else {
                    y
                }
            };
            (x, y)
        }
        65 => {
            let x = BigUint::from_bytes_be(&pk[1..33]);
            let y = BigUint::from_bytes_be(&pk[33..]);
            (x, y)
        }
        _ => panic!("invalid public key length"),
    }
}

#[derive(Clone)]
pub struct PointVar<C: PrimeField, const W: usize>(
    pub BigUintVar<C, W>,
    pub BigUintVar<C, W>,
    pub Boolean<C>,
);

impl<F: PrimeField, const W: usize> EqGadget<F> for PointVar<F, W> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        self.0.is_eq(&other.0)?.and(&self.1.is_eq(&other.1)?)?.and(&self.2.is_eq(&other.2)?)
    }
}

impl<F: PrimeField, const W: usize> R1CSVar<F> for PointVar<F, W> {
    type Value = (BigUint, BigUint);

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.0.cs().or(self.1.cs()).or(self.2.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok((self.0.value()?, self.1.value()?))
    }
}

impl<F: PrimeField, const W: usize> CondSelectGadget<F> for PointVar<F, W> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        Ok(Self(
            cond.select(&true_value.0, &false_value.0)?,
            cond.select(&true_value.1, &false_value.1)?,
            cond.select(&true_value.2, &false_value.2)?,
        ))
    }
}

impl<F: PrimeField, const W: usize> AllocVar<Vec<u8>, F> for PointVar<F, W> {
    fn new_variable<T: Borrow<Vec<u8>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let r = f().map(|g| g.borrow().clone())?;

        let (x, y) = parse_pk(&r);

        let x = BigUintVar::new_variable(cs.clone(), || Ok((x, 256)), mode)?;
        let y = BigUintVar::new_variable(cs, || Ok((y, 256)), mode)?;

        Ok(Self(x, y, Boolean::FALSE))
    }
}

impl<F: PrimeField, const W: usize> PointVar<F, W> {
    pub fn inputize(pk: &[u8]) -> Vec<F> {
        let (x, y) = parse_pk(pk);
        let x = BigUintVar::<F, W>::inputize(&x, 256);
        let y = BigUintVar::<F, W>::inputize(&y, 256);
        [x, y].concat()
    }

    fn inf() -> Self {
        PointVar(
            BigUintVar::constant(BigUint::zero(), 256).unwrap(),
            BigUintVar::constant(BigUint::zero(), 256).unwrap(),
            Boolean::TRUE,
        )
    }

    pub fn add(&self, other: &Self) -> Result<Self, SynthesisError> {
        let cs = self.cs().or(other.cs());
        let PointVar(x1, y1, i1) = self;
        let PointVar(x2, y2, i2) = other;

        let m =
            BigUintVar::constant((BigUint::one() << 256u32) - BigUint::from(4294968273u128), 256)?;

        let (s, x, y) = {
            let bound = m.ubound().bits() as usize;
            let (s, x, y) = if cs.is_in_setup_mode() {
                (BigUint::zero(), BigUint::zero(), BigUint::zero())
            } else {
                let m = m.value().unwrap_or_default();
                let x1 = x1.value().unwrap_or_default();
                let x2 = x2.value().unwrap_or_default();
                let y1 = y1.value().unwrap_or_default();
                let y2 = y2.value().unwrap_or_default();
                let s = (&m + &y1 - &y2).mulm(&(&m + &x1 - &x2).invm(&m).unwrap_or_default(), &m);
                let x = (&s * &s + &m + &m - &x1 - &x2) % &m;
                let y = (&m - &y1 + &s * (&m + &x1 - &x)) % &m;

                (s, x, y)
            };
            if cs.is_none() {
                (
                    BigUintVar::constant(s, bound)?,
                    BigUintVar::constant(x, bound)?,
                    BigUintVar::constant(y, bound)?,
                )
            } else {
                (
                    BigUintVar::new_witness(cs.clone(), || Ok((s, bound)))?,
                    BigUintVar::new_witness(cs.clone(), || Ok((x, bound)))?,
                    BigUintVar::new_witness(cs, || Ok((y, bound)))?,
                )
            }
        };
        let sx1 = x1.mul_no_carry(&s)?;
        sx1.add_no_carry(y2)
            .enforce_congruent_const(&x2.mul_no_carry(&s)?.add_no_carry(y1), &m)?;
        s.mul_no_carry(&s)?.enforce_congruent_const(&x.add_no_carry(x1).add_no_carry(x2), &m)?;
        s.mul_no_carry(&x)?.add_no_carry(y1).add_no_carry(&y).enforce_congruent_const(&sx1, &m)?;

        i1.select(other, &i2.select(self, &Self(x, y, Boolean::FALSE))?)
    }

    pub fn double(&self) -> Result<Self, SynthesisError> {
        let PointVar(x, y, i) = self;

        let m =
            BigUintVar::constant((BigUint::one() << 256u32) - BigUint::from(4294968273u128), 256)?;
        let three = BigUintVar::constant(BigUint::from(3u8), 2)?;

        let (s, xx, yy) = {
            let cs = self.cs();
            let bound = m.ubound().bits() as usize;
            let (s, xx, yy) = if cs.is_in_setup_mode() {
                (BigUint::zero(), BigUint::zero(), BigUint::zero())
            } else {
                let m = m.value().unwrap_or_default();
                let x = x.value().unwrap_or_default();
                let y = y.value().unwrap_or_default();
                let s = (&x * &x * BigUint::from(3u8))
                    .mulm(&(&y + &y).invm(&m).unwrap_or_default(), &m);
                let xx = (&s * &s + &m + &m - &x - &x) % &m;
                let yy = (&m - &y + &s * (&m + &x - &xx)) % &m;

                (s, xx, yy)
            };
            if cs.is_none() {
                (
                    BigUintVar::constant(s, bound)?,
                    BigUintVar::constant(xx, bound)?,
                    BigUintVar::constant(yy, bound)?,
                )
            } else {
                (
                    BigUintVar::new_witness(cs.clone(), || Ok((s, bound)))?,
                    BigUintVar::new_witness(cs.clone(), || Ok((xx, bound)))?,
                    BigUintVar::new_witness(cs, || Ok((yy, bound)))?,
                )
            }
        };
        s.add_no_carry(&s)
            .mul_no_carry(y)?
            .enforce_congruent_const(&three.mul_no_carry(x)?.mul_no_carry(x)?, &m)?;
        s.mul_no_carry(&s)?.enforce_congruent_const(&xx.add_no_carry(x).add_no_carry(x), &m)?;
        s.mul_no_carry(&xx)?
            .add_no_carry(y)
            .add_no_carry(&yy)
            .enforce_congruent_const(&s.mul_no_carry(x)?, &m)?;

        i.select(self, &Self(xx, yy, Boolean::FALSE))
    }

    fn scalar_mul(&self, s: &[Boolean<F>]) -> Result<Self, SynthesisError> {
        let m =
            BigUintVar::constant((BigUint::one() << 256u32) - BigUint::from(4294968273u128), 256)?;
        let k = 4;
        let mut base_powers = vec![Self::inf(), self.clone(), self.double()?];
        for _ in 3..(1 << k) {
            base_powers.push(base_powers.last().unwrap().add(self)?);
        }
        let mut r = Self::inf();

        for (i, chunk) in s.rchunks(k).enumerate() {
            let k = chunk.len();
            if i != 0 {
                for _ in 0..k {
                    r = r.double()?;
                }
            }
            let base_power = {
                let mut inputs = base_powers[..(1 << k)].to_vec();
                for b in chunk {
                    inputs = inputs
                        .chunks(2)
                        .map(|v| b.select(&v[1], &v[0]))
                        .collect::<Result<_, _>>()?;
                }
                inputs.pop().unwrap()
            };
            if i != 0 {
                r = r.add(&base_power)?;
            } else {
                r = base_power;
            }
        }
        r.0.enforce_lt(&m)?;
        r.1.enforce_lt(&m)?;
        Ok(r)
    }

    pub fn hash(&self, pp: &PoseidonParameters<F>) -> Result<FpVar<F>, SynthesisError> {
        let x_bits = self.0.to_bits_le()?;
        let y_bits = self.1.to_bits_le()?;
        let x_chunks = x_bits.split_at(128);
        let x0 = Boolean::le_bits_to_fp_var(x_chunks.0)?;
        let x1 = Boolean::le_bits_to_fp_var(x_chunks.1)?;
        let y_chunks = y_bits.split_at(128);
        let y0 = Boolean::le_bits_to_fp_var(y_chunks.0)?;
        let y1 = Boolean::le_bits_to_fp_var(y_chunks.1)?;
        CRHGadget::hash(pp, x0, x1, y0, y1)
    }
}

#[derive(Clone, Debug)]
pub struct SecretKeyVar<F: PrimeField>(pub Vec<Boolean<F>>);

impl<F: PrimeField> R1CSVar<F> for SecretKeyVar<F> {
    type Value = SecretKey;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.0.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(SecretKey::from_slice(&F::BigInt::from_bits_le(&self.0.value()?).to_bytes_be()).unwrap())
    }
}

impl<F: PrimeField> AllocVar<Vec<u8>, F> for SecretKeyVar<F> {
    fn new_variable<T: Borrow<Vec<u8>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let b = f()?;
        let b = b.borrow();

        Ok(Self(match F::BigInt::try_from(BigUint::from_bytes_be(b)) {
            Ok(v) => v
                .to_bits_le()
                .into_iter()
                .map(|i| Boolean::new_variable(cs.clone(), || Ok(i), mode).unwrap())
                .collect(),
            Err(_) => panic!(),
        }))
    }
}

pub struct Secp256k1Gadget {}

impl Secp256k1Gadget {
    pub fn pk_gen<F: PrimeField, const W: usize>(
        sk: &SecretKeyVar<F>,
    ) -> Result<PointVar<F, W>, SynthesisError> {
        const L: usize = 6;
        let mut bases = include_bytes!("./precomputed")
            .chunks(64 * (1 << L))
            .map(|chunk| {
                let mut r = chunk
                    .chunks(64)
                    .map(|s| {
                        PointVar(
                            BigUintVar::constant(BigUint::from_bytes_le(&s[..32]), 256).unwrap(),
                            BigUintVar::constant(BigUint::from_bytes_le(&s[32..]), 256).unwrap(),
                            Boolean::FALSE,
                        )
                    })
                    .collect::<Vec<_>>();
                r[0].2 = Boolean::TRUE;
                r
            })
            .collect::<Vec<_>>();
        let m =
            BigUintVar::constant((BigUint::one() << 256u32) - BigUint::from(4294968273u128), 256)?;
        let mut pk = PointVar::inf();

        for (i, s) in sk.0.chunks(L).enumerate() {
            for j in 0..L {
                bases[i] = bases[i]
                    .chunks(2)
                    .map(|v| s.get(j).unwrap_or(&Boolean::FALSE).select(&v[1], &v[0]))
                    .collect::<Result<_, _>>()?;
            }

            let v = bases[i].pop().unwrap();
            pk = if i == 0 { v } else { pk.add(&v)? }
        }
        pk.0.enforce_lt(&m)?;
        pk.1.enforce_lt(&m)?;
        Ok(pk)
    }

    pub fn key_exchange<F: PrimeField, const W: usize>(
        sk: &SecretKeyVar<F>,
        pk: &PointVar<F, W>,
    ) -> Result<PointVar<F, W>, SynthesisError> {
        pk.scalar_mul(&sk.0)
    }
}

#[cfg(test)]
mod tests {
    use std::{error::Error, time::Instant};

    use ark_bn254::{Bn254, Fr};
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    use num::Num;
    use rand::{thread_rng, RngCore};
    use secp256k1::{PublicKey, SECP256K1};

    use super::*;

    const W: usize = 43;

    #[test]
    fn correctness() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let (sk, pk) = secp256k1::Secp256k1::new().generate_keypair(&mut thread_rng());
        let pk = parse_pk(&pk.serialize_uncompressed());

        let sk_var = SecretKeyVar::new_witness(cs.clone(), || Ok(sk.secret_bytes().to_vec()))?;
        let pk_var = Secp256k1Gadget::pk_gen::<Fr, W>(&sk_var)?;

        assert_eq!(pk_var.0.value()?, pk.0);
        assert_eq!(pk_var.1.value()?, pk.1);
        assert!(cs.is_satisfied()?);
        println!("{}", cs.num_constraints());
        Ok(())
    }

    // #[test]
    // fn find() -> Result<(), Box<dyn Error>> {
    //     let rng = &mut thread_rng();

    //     seq_macro::seq!(W in 10..100 {
    //         {
    //             let cs = ConstraintSystem::<Fr>::new_ref();
    //             let (sk, pk) = secp256k1::Secp256k1::new().generate_keypair(rng);
    //             let pk = parse_pk(&pk.serialize_uncompressed());
        
    //             let sk_var = SecretKeyVar::new_witness(cs.clone(), || Ok(sk.secret_bytes().to_vec()))?;
    //             let pk_var = Secp256k1Gadget::pk_gen::<Fr, W>(&sk_var)?;
        
    //             assert!(cs.is_satisfied()?);
    //             println!("{}: {}", W, cs.num_constraints());
    //         }
    //     });

    //     Ok(())
    // }

    #[test]
    fn correctness2() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut sk_buf = vec![0u8; 32];
        thread_rng().fill_bytes(&mut sk_buf);
        let sk = SecretKey::from_slice(&sk_buf)?;
        let pk = sk.public_key(SECP256K1);
        let pk = parse_pk(&pk.serialize_uncompressed());

        let sk_var = SecretKeyVar::new_witness(cs.clone(), || Ok(sk_buf))?;
        let pk_var = PointVar::<Fr, W>(
            BigUintVar::new_witness(cs.clone(), || {
                Ok((
                    BigUint::from_str_radix(
                        "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
                        16,
                    )
                    .unwrap(),
                    256,
                ))
            })
            .unwrap(),
            BigUintVar::new_witness(cs.clone(), || {
                Ok((
                    BigUint::from_str_radix(
                        "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8",
                        16,
                    )
                    .unwrap(),
                    256,
                ))
            })
            .unwrap(),
            Boolean::FALSE,
        )
        .scalar_mul(&sk_var.0)?;

        assert_eq!(pk_var.0.value()?, pk.0);
        assert_eq!(pk_var.1.value()?, pk.1);
        assert!(cs.is_satisfied()?);
        println!("{}", cs.num_constraints());
        Ok(())
    }

    // #[test]
    // fn find2() -> Result<(), Box<dyn Error>> {
    //     let rng = &mut thread_rng();

    //     seq_macro::seq!(W in 10..100 {
    //         {
    //             let cs = ConstraintSystem::<Fr>::new_ref();
    //             let mut sk_buf = vec![0u8; 32];
    //             rng.fill_bytes(&mut sk_buf);
    //             let sk = SecretKey::from_slice(&sk_buf)?;
    //             let pk = sk.public_key(SECP256K1);
    //             let pk = parse_pk(&pk.serialize_uncompressed());
        
    //             let sk_var = SecretKeyVar::new_witness(cs.clone(), || Ok(sk_buf))?;
    //             let pk_var = PointVar::<Fr, W>(
    //                 BigUintVar::new_witness(cs.clone(), || {
    //                     Ok((
    //                         BigUint::from_str_radix(
    //                             "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
    //                             16,
    //                         )
    //                         .unwrap(),
    //                         256,
    //                     ))
    //                 })
    //                 .unwrap(),
    //                 BigUintVar::new_witness(cs.clone(), || {
    //                     Ok((
    //                         BigUint::from_str_radix(
    //                             "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8",
    //                             16,
    //                         )
    //                         .unwrap(),
    //                         256,
    //                     ))
    //                 })
    //                 .unwrap(),
    //                 Boolean::FALSE,
    //             )
    //             .scalar_mul(&sk_var.0)?;
        
    //             assert!(cs.is_satisfied()?);
    //             println!("{}: {}", W, cs.num_constraints());
    //         }
    //     });

    //     Ok(())
    // }

    struct TestCircuit {
        sk: SecretKey,
        pk: PublicKey,
    }

    impl ConstraintSynthesizer<Fr> for TestCircuit {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<Fr>,
        ) -> ark_relations::r1cs::Result<()> {
            let sk_var =
                SecretKeyVar::new_witness(cs.clone(), || Ok(self.sk.secret_bytes().to_vec()))?;
            let pk_var =
                PointVar::<Fr, W>::new_input(cs, || Ok(self.pk.serialize().to_vec()))?;
            Secp256k1Gadget::pk_gen(&sk_var)?.enforce_equal(&pk_var)?;
            Ok(())
        }
    }

    #[test]
    fn test() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();
        let (sk, pk) = secp256k1::Secp256k1::new().generate_keypair(rng);

        let params = generate_random_parameters::<Bn254, _, _>(
            TestCircuit {
                sk: SecretKey::new(rng),
                pk: secp256k1::Secp256k1::new().generate_keypair(rng).1,
            },
            rng,
        )
        .unwrap();

        let pvk = prepare_verifying_key(&params.vk);
        let now = Instant::now();
        let proof = create_random_proof(TestCircuit { sk, pk }, &params, rng).unwrap();
        println!("proof time: {:?}", now.elapsed());

        assert!(verify_proof(&pvk, &proof, &PointVar::<Fr, W>::inputize(&pk.serialize())).unwrap());
        Ok(())
    }
}
