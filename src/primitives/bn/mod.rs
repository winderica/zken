use std::{
    borrow::Borrow,
    cmp::{max, min},
};

use ark_ff::{BigInteger, One, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    prelude::EqGadget,
    select::CondSelectGadget,
    R1CSVar, ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use num::{integer::ExtendedGcd, BigInt, BigUint, Integer, Signed, Zero};

#[derive(Clone)]
pub struct BitsVar<F: PrimeField, const W: usize>(pub FpVar<F>, pub BigUint);

impl<F: PrimeField, const W: usize> From<&[Boolean<F>]> for BitsVar<F, W> {
    fn from(bits: &[Boolean<F>]) -> Self {
        Self(
            Boolean::le_bits_to_fp_var(bits).unwrap(),
            (BigUint::one() << bits.len()) - BigUint::one(),
        )
    }
}

impl<F: PrimeField, const W: usize> Default for BitsVar<F, W> {
    fn default() -> Self {
        Self(FpVar::zero(), BigUint::zero())
    }
}

impl<F: PrimeField, const W: usize> R1CSVar<F> for BitsVar<F, W> {
    type Value = F;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.0.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        self.0.value()
    }
}

impl<F: PrimeField, const W: usize> EqGadget<F> for BitsVar<F, W> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        assert_eq!(self.1, other.1);
        self.0.is_eq(&other.0)
    }

    fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        assert_eq!(self.1, other.1);
        self.0.enforce_equal(&other.0)
    }
}

impl<F: PrimeField, const W: usize> CondSelectGadget<F> for BitsVar<F, W> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(true_value.1, false_value.1);
        Ok(Self(cond.select(&true_value.0, &false_value.0)?, true_value.1.clone()))
    }
}

impl<F: PrimeField, const W: usize> BitsVar<F, W> {
    pub fn to_bit_array(&self, width: Option<usize>) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = self.cs();

        let width = width.unwrap_or(self.1.bits() as usize);
        let bits = {
            let bits = &self.0.value().unwrap_or_default().into_bigint().to_bits_le()[..width];
            if cs.is_none() {
                Vec::new_constant(cs, bits)?
            } else {
                Vec::new_witness(cs, || Ok(bits))?
            }
        };

        Boolean::le_bits_to_fp_var(&bits)?.enforce_equal(&self.0)?;

        Ok(bits)
    }

    fn add(&self, other: &Self) -> Option<Self> {
        let ubound = &self.1 + &other.1;
        if ubound < F::MODULUS_MINUS_ONE_DIV_TWO.into() {
            Some(Self(&self.0 + &other.0, ubound))
        } else {
            None
        }
    }

    fn mul(&self, other: &Self) -> Option<Self> {
        let ubound = &self.1 * &other.1;
        if ubound < F::MODULUS_MINUS_ONE_DIV_TWO.into() {
            Some(Self(&self.0 * &other.0, ubound))
        } else {
            None
        }
    }

    fn zero() -> Self {
        Self::default()
    }
}

#[derive(Clone)]
pub struct BigUintVar<F: PrimeField, const W: usize>(pub Vec<BitsVar<F, W>>);

impl<F: PrimeField, const W: usize> AllocVar<(BigUint, usize), F> for BigUintVar<F, W> {
    fn new_variable<T: Borrow<(BigUint, usize)>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let (x, l) = v.borrow();

        let mut limbs = vec![];
        for chunk in (0..*l).map(|i| x.bit(i as u64)).collect::<Vec<_>>().chunks(W) {
            let limb = F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap();
            let limb = FpVar::new_variable(cs.clone(), || Ok(limb), mode)?;
            Self::to_bit_array(&limb, chunk.len())?;
            limbs.push(BitsVar(limb, (BigUint::one() << chunk.len()) - BigUint::one()));
        }

        Ok(Self(limbs))
    }
}

impl<F: PrimeField, const W: usize> BigUintVar<F, W> {
    pub fn inputize(x: &BigUint, l: usize) -> Vec<F> {
        (0..l)
            .map(|i| x.bit(i as u64))
            .collect::<Vec<_>>()
            .chunks(W)
            .map(|chunk| F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap())
            .collect()
    }
}

impl<F: PrimeField, const W: usize> R1CSVar<F> for BigUintVar<F, W> {
    type Value = BigUint;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.0.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let mut r = BigUint::zero();

        for limb in self.0.value()?.into_iter().rev() {
            r <<= W;
            r += Into::<BigUint>::into(limb);
        }

        Ok(r)
    }
}

impl<F: PrimeField, const W: usize> EqGadget<F> for BigUintVar<F, W> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        let n = min(self.0.len(), other.0.len());
        let mut r = Boolean::TRUE;
        for i in 0..n {
            r = r.and(&self.0[i].is_eq(&other.0[i])?)?;
        }
        for i in n..self.0.len() {
            r = r.and(&self.0[i].0.is_zero()?)?;
        }
        for i in n..other.0.len() {
            r = r.and(&other.0[i].0.is_zero()?)?;
        }
        Ok(r)
    }

    fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        assert_eq!(self.value().unwrap_or_default(), other.value().unwrap_or_default());
        let n = min(self.0.len(), other.0.len());
        for i in 0..n {
            self.0[i].enforce_equal(&other.0[i])?;
        }
        for i in n..self.0.len() {
            self.0[i].0.enforce_equal(&FpVar::zero())?;
        }
        for i in n..other.0.len() {
            other.0[i].0.enforce_equal(&FpVar::zero())?;
        }
        Ok(())
    }
}

impl<F: PrimeField, const W: usize> BigUintVar<F, W> {
    pub fn enforce_lt(&self, other: &Self) -> Result<(), SynthesisError> {
        let len = max(self.0.len(), other.0.len());
        let zero = BitsVar::zero();

        let mut delta = vec![];
        for i in 0..len {
            delta.push(&other.0.get(i).unwrap_or(&zero).0 - &self.0.get(i).unwrap_or(&zero).0);
        }

        let helper = {
            let cs = self.cs().or(other.cs());
            let mut helper = vec![false; len];
            for i in (0..len).rev() {
                let x = self.0.get(i).unwrap_or(&zero).value().unwrap_or_default();
                let y = other.0.get(i).unwrap_or(&zero).value().unwrap_or_default();
                if y > x {
                    helper[i] = true;
                    break;
                }
            }
            if cs.is_none() {
                Vec::<Boolean<F>>::new_constant(cs, helper)?
            } else {
                Vec::new_witness(cs, || Ok(helper))?
            }
        };

        let mut c = FpVar::<F>::zero();
        let mut r = FpVar::zero();
        for (b, d) in helper.into_iter().zip(delta) {
            c += b.select(&d, &FpVar::zero())?;
            (&r * &d).enforce_equal(&FpVar::zero())?;
            r += FpVar::from(b);
        }
        Self::to_bit_array(&(c - FpVar::one()), W)?;
        r.enforce_equal(&FpVar::one())?;

        Ok(())
    }

    pub fn enforce_equal_unaligned(&self, other: &Self) -> Result<(), SynthesisError> {
        let cs = self.cs().or(other.cs());
        let len = min(self.0.len(), other.0.len());

        let (steps, xxs, yys, rest) = {
            let mut steps = vec![];
            let mut x_grouped = vec![];
            let mut y_grouped = vec![];
            let mut i = 0;
            while i < len {
                let mut j = i;
                let mut xx = BitsVar::zero();
                let mut yy = BitsVar::zero();
                while j < len {
                    let delta = BigUint::one() << (W * (j - i));
                    let delta = BitsVar(FpVar::Constant(F::from(delta.clone())), delta);
                    match (
                        self.0[j].mul(&delta).and_then(|x| xx.add(&x)),
                        other.0[j].mul(&delta).and_then(|y| yy.add(&y)),
                    ) {
                        (Some(x), Some(y)) => (xx, yy) = (x, y),
                        _ => break,
                    }
                    j += 1;
                }
                steps.push((j - i) * W);
                x_grouped.push(xx);
                y_grouped.push(yy);
                i = j;
            }
            let mut vv = BitsVar::zero();
            for v in &(if i < self.0.len() { self } else { other }).0[i..] {
                vv = vv.add(v).unwrap();
            }
            (steps, x_grouped, y_grouped, vv.0)
        };
        let n = steps.len();
        let mut acc = BigUint::zero();
        let mut c = FpVar::<F>::zero();
        for i in 0..n {
            let step = steps[i];
            let max_ubound = max(xxs[i].1.clone(), yys[i].1.clone());
            acc += &max_ubound;
            let carry_width =
                (max_ubound.bits() as usize + 1).checked_sub(step).unwrap_or_default();
            let z = &xxs[i].0 + F::from(max_ubound) - &yys[i].0;
            let c_prev = c.clone();
            c = {
                let c: BigUint = (&z + c).value().unwrap_or_default().into();
                if cs.is_none() {
                    FpVar::constant(F::from(c >> step))
                } else {
                    FpVar::new_witness(cs.clone(), || Ok(F::from(c >> step)))?
                }
            };
            let (q, r) = acc.div_rem(&(BigUint::one() << step));
            if i == n - 1 {
                (&c - &rest).enforce_equal(&FpVar::constant(F::from(q.clone())))?;
            } else {
                Self::to_bit_array(&c, carry_width)?;
            }

            (z + c_prev).enforce_equal(&(&c * F::from(BigUint::one() << step) + F::from(r)))?;
            acc = q;
        }

        Ok(())
    }
}

impl<F: PrimeField, const W: usize> ToBitsGadget<F> for BigUintVar<F, W> {
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        Ok(self
            .0
            .iter()
            .map(|limb| limb.to_bit_array(None))
            .collect::<Result<Vec<_>, _>>()?
            .concat())
    }
}

impl<F: PrimeField, const W: usize> CondSelectGadget<F> for BigUintVar<F, W> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(true_value.0.len(), false_value.0.len());
        let mut v = vec![];
        for i in 0..true_value.0.len() {
            v.push(cond.select(&true_value.0[i], &false_value.0[i])?);
        }
        Ok(Self(v))
    }
}

impl<F: PrimeField, const W: usize> BigUintVar<F, W> {
    pub fn constant(v: BigUint, w: usize) -> Result<Self, SynthesisError> {
        Self::new_constant(ConstraintSystemRef::None, (v, w))
    }

    pub fn ubound(&self) -> BigUint {
        let mut r = BigUint::zero();

        for i in self.0.iter().rev() {
            r <<= W;
            r += &i.1;
        }

        r
    }

    fn to_bit_array(x: &FpVar<F>, length: usize) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = x.cs();

        let bits = &x.value().unwrap_or_default().into_bigint().to_bits_le()[..length];
        let bits = if cs.is_none() {
            Vec::new_constant(cs, bits)?
        } else {
            Vec::new_witness(cs, || Ok(bits))?
        };

        Boolean::le_bits_to_fp_var(&bits)?.enforce_equal(x)?;

        Ok(bits)
    }

    pub fn align(&self) -> Result<Self, SynthesisError> {
        let mut z = vec![];
        let mut c = BitsVar::zero();
        for i in &self.0 {
            let v = i.add(&c).unwrap();
            let v_bits = v.to_bit_array(None)?;
            let p = min(W, v_bits.len());
            let (l, r) = v_bits.split_at(p);
            c = BitsVar(Boolean::le_bits_to_fp_var(r)?, v.1 >> p);
            z.push(BitsVar::from(l));
        }
        z.push(c);
        Ok(Self(z))
    }

    pub fn add_no_carry(&self, other: &Self) -> Self {
        let mut z = vec![BitsVar::zero(); max(self.0.len(), other.0.len())];
        for i in 0..self.0.len() {
            z[i] = z[i].add(&self.0[i]).unwrap();
        }
        for i in 0..other.0.len() {
            z[i] = z[i].add(&other.0[i]).unwrap();
        }
        Self(z)
    }

    pub fn mul_no_carry(&self, other: &Self) -> Result<Self, SynthesisError> {
        let len = self.0.len() + other.0.len() - 1;
        if self.is_constant() || other.is_constant() {
            let mut z = vec![BitsVar::zero(); len];
            for i in 0..self.0.len() {
                for j in 0..other.0.len() {
                    z[i + j] = z[i + j].add(&self.0[i].mul(&other.0[j]).unwrap()).unwrap();
                }
            }
            return Ok(Self(z));
        }
        let cs = self.cs().or(other.cs());

        let z = {
            let mut z = vec![(F::zero(), BigUint::zero()); len];
            for i in 0..self.0.len() {
                for j in 0..other.0.len() {
                    z[i + j].0 += self.0[i].value().unwrap_or_default()
                        * other.0[j].value().unwrap_or_default();
                    z[i + j].1 += &self.0[i].1 * &other.0[j].1;
                }
            }
            z.into_iter()
                .map(|(f, u)| {
                    Ok(BitsVar(
                        if cs.is_none() {
                            FpVar::constant(f)
                        } else {
                            FpVar::new_witness(cs.clone(), || Ok(f))?
                        },
                        u,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?
        };
        for c in 1..=len {
            let mut l = FpVar::<F>::zero();
            let mut r = FpVar::<F>::zero();
            let mut o = FpVar::<F>::zero();
            let mut t = F::one();
            for i in 0..len {
                if i < self.0.len() {
                    l += &self.0[i].0 * t;
                }
                if i < other.0.len() {
                    r += &other.0[i].0 * t;
                }
                o += &z[i].0 * t;
                t *= F::from(c as u64);
            }
            l.mul_equals(&r, &o)?;
        }

        Ok(Self(z))
    }

    pub fn enforce_congruent_const(&self, other: &Self, m: &Self) -> Result<(), SynthesisError> {
        assert!(m.is_constant());
        let cs = self.cs().or(m.cs());
        let bits = (max(self.ubound(), other.ubound()) / m.value()?).bits() as usize;
        let (d, b) = {
            let x = self.value().unwrap_or_default();
            let y = other.value().unwrap_or_default();
            let m = m.value()?;
            let (d, b) = if x > y { ((x - y) / m, true) } else { ((y - x) / m, false) };
            if cs.is_none() {
                (Self::constant(d, bits)?, Boolean::constant(b))
            } else {
                (
                    Self::new_witness(cs.clone(), || Ok((d, bits)))?,
                    Boolean::new_witness(cs.clone(), || Ok(b))?,
                )
            }
        };
        let l = self.add_no_carry(
            &b.select(&Self::constant(BigUint::zero(), bits)?, &d)?.mul_no_carry(&m)?,
        );
        let r = other.add_no_carry(
            &b.select(&d, &Self::constant(BigUint::zero(), bits)?)?.mul_no_carry(&m)?,
        );
        l.enforce_equal_unaligned(&r)
    }

    fn rem(&self, m: &Self, m_lbound: &BigUint) -> Result<Self, SynthesisError> {
        let cs = self.cs().or(m.cs());
        let (q, r) = {
            let (q, r) =
                self.value().unwrap_or_default().div_rem(&m.value().unwrap_or(BigUint::one()));
            let q_ubound = self.ubound().div_ceil(m_lbound);
            let r_ubound = m.ubound();
            if cs.is_none() {
                (
                    Self::constant(q, q_ubound.bits() as usize)?,
                    Self::constant(r, r_ubound.bits() as usize)?,
                )
            } else {
                (
                    Self::new_witness(cs.clone(), || Ok((q, q_ubound.bits() as usize)))?,
                    Self::new_witness(cs.clone(), || Ok((r, r_ubound.bits() as usize)))?,
                )
            }
        };

        q.mul_no_carry(&m)?.add_no_carry(&r).enforce_equal_unaligned(&self)?;

        Ok(r)
    }

    pub fn powm(
        self,
        e: &[Boolean<F>],
        m: &Self,
        m_lbound: &BigUint,
    ) -> Result<Self, SynthesisError> {
        let mut k = 1;
        while (e.len() - 1) * ((1 << (k + 1)) - k - 2) >= (k * (k + 1) << (2 * k)) {
            k += 1;
        }
        let mut base_powers =
            vec![Self::constant(BigUint::one(), m.ubound().bits() as usize)?, self.clone()];
        for _ in 2..(1 << k) {
            base_powers.push(base_powers.last().unwrap().mul_no_carry(&self)?.rem(m, m_lbound)?);
        }
        let mut r = Self::constant(BigUint::one(), m.ubound().bits() as usize)?;

        for (i, chunk) in e.rchunks(k).enumerate() {
            let k = chunk.len();
            if i != 0 {
                for _ in 0..k {
                    r = r.mul_no_carry(&r)?.rem(m, m_lbound)?;
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
                r = r.mul_no_carry(&base_power)?.rem(m, m_lbound)?;
            } else {
                r = base_power;
            }
        }

        r.enforce_lt(&m)?;
        Ok(r)
    }

    pub fn powm_const(self, e: &[Boolean<F>], m: &Self) -> Result<Self, SynthesisError> {
        assert!(m.is_constant());
        self.powm(e, m, &m.value()?)
    }

    pub fn sub_one_enforce_coprime(&self, other: &Self) -> Result<(), SynthesisError> {
        let cs = self.cs().or(other.cs());
        let (x, y) = {
            let x_bound = other.ubound();
            let y_bound = self.ubound();
            let a: BigInt = self.value().unwrap_or_default().into();
            let a = a - BigInt::one();
            let b: BigInt = other.value().unwrap_or(BigUint::one()).into();
            let ExtendedGcd { mut x, mut y, .. } = a.extended_gcd(&b);
            if x.is_negative() {
                let k = x.abs().div_ceil(&b);
                (x, y) = (&x + &b * &k, &y - &a * &k);
            }
            let x = x.to_biguint().unwrap();
            let y = y.abs().to_biguint().unwrap();
            if cs.is_none() {
                (
                    Self::constant(x, x_bound.bits() as usize)?,
                    Self::constant(y, y_bound.bits() as usize)?,
                )
            } else {
                (
                    Self::new_witness(cs.clone(), || Ok((x, x_bound.bits() as usize)))?,
                    Self::new_witness(cs.clone(), || Ok((y, y_bound.bits() as usize)))?,
                )
            }
        };
        self.mul_no_carry(&x)?.enforce_equal_unaligned(
            &other
                .mul_no_carry(&y)?
                .add_no_carry(&x)
                .add_no_carry(&BigUintVar::constant(BigUint::one(), 1)?),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use ark_bn254::Fr;
    use ark_relations::r1cs::ConstraintSystem;
    use num::bigint::RandBigInt;
    use rand::thread_rng;

    use super::*;

    const W: usize = 32;

    #[test]
    fn test() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let m = BigUintVar::<Fr, W>::constant(
            rng.gen_biguint_range(
                &(BigUint::one() << 2047),
                &((BigUint::one() << 2048) - BigUint::one()),
            ),
            2048,
        )?;
        let b = BigUintVar::<Fr, W>::new_witness(cs.clone(), || {
            Ok((rng.gen_biguint_below(&m.value()?), 2048))
        })?;
        let e = BigUintVar::<Fr, W>::new_witness(cs.clone(), || Ok((rng.gen_biguint_below(&(BigUint::from(65537u32))), 256)))?;

        println!("{}", cs.num_constraints());
        assert_eq!(
            b.value()?.modpow(&e.value()?, &m.value()?),
            b.powm_const(&e.to_bits_le()?, &m)?.value()?
        );
        assert!(cs.is_satisfied()?);
        println!("{}", cs.num_constraints());
        Ok(())
    }

    #[test]
    fn test2() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let m = BigUintVar::<Fr, W>::constant(
            rng.gen_biguint_range(
                &(BigUint::one() << 2047),
                &((BigUint::one() << 2048) - BigUint::one()),
            ),
            2048,
        )?;
        let b = BigUintVar::<Fr, W>::new_witness(cs.clone(), || {
            Ok((rng.gen_biguint_below(&m.value()?), 2048))
        })?;

        println!("{}", cs.num_constraints());
        let mut r = b.clone();
        for _ in 0..16 {
            r = r.mul_no_carry(&r)?.rem(&m, &m.value()?)?;
        }
        r = r.mul_no_carry(&b)?.rem(&m, &m.value()?)?;
        r.enforce_lt(&m)?;
        assert_eq!(b.value()?.modpow(&BigUint::from(65537u32), &m.value()?), r.value()?);
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
    //             let m = BigUintVar::<Fr, W>::constant(rng.gen_biguint_range(&(BigUint::one() << 2047), &((BigUint::one() << 2048) - BigUint::one())), 2048)?;
    //             let b = BigUintVar::<Fr, W>::new_witness(cs.clone(), || Ok((rng.gen_biguint_below(&m.value()?), 2048)))?;
        
    //             let mut r = b.clone();
    //             for _ in 0..16 {
    //                 r = r.mul_no_carry(&r)?.rem(&m, &m.value()?)?;
    //             }
    //             r = r.mul_no_carry(&b)?.rem(&m, &m.value()?)?;
    //             r.enforce_lt(&m)?;
    //             assert!(cs.is_satisfied()?);
    //             println!("{}: {}", W, cs.num_constraints());
    //         }
    //     });

    //     Ok(())
    // }
}
