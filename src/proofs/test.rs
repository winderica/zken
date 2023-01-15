
#[cfg(test)]
mod tests {
    use std::{
        error::Error,
        fs::{self, File},
        time::Instant,
    };

    use ark_bn254::{Bn254, Fr};
    use ark_ff::{One, PrimeField, UniformRand};
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
        Proof, ProvingKey,
    };
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use indoc::indoc;
    use num::{
        bigint::{RandBigInt, Sign},
        BigInt, BigUint, Integer,
    };
    use rand::thread_rng;

    use crate::{
        constants::{ALPHA, R_F, R_P, WIDTH, W},
        primitives::{
            commitment::{self, Pedersen},
            elgamal::{self, ElGamal},
            poseidon::PoseidonParameters,
            secp256k1::{self},
        },
        proofs::{access, root, mint, mod_eq, nft::{self, generate_e, generate_nft, keygen}},
        utils::{Mod, ToHex, ToSolidity, ToTransaction},
    };

    #[test]
    fn setup() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();

        serde_json::to_writer(File::create("./data/rsa.pp")?, &root::Parameters::new(rng))?;
        ElGamal::<Fr>::setup(rng).serialize_unchecked(File::create("./data/encryption.pp")?)?;
        Pedersen::<Fr>::setup(rng).serialize_unchecked(File::create("./data/commitment.pp")?)?;

        let now = Instant::now();
        let crs_nft = generate_random_parameters::<Bn254, _, _>(nft::NFTCircuit::fake(), rng)?;
        println!("setup/nft: {:.2?}", now.elapsed());
        println!("{}", crs_nft.uncompressed_size());
        crs_nft.serialize_unchecked(File::create("./data/nft.crs")?)?;

        let now = Instant::now();
        let crs_access =
            generate_random_parameters::<Bn254, _, _>(access::RangeCircuit::fake(), rng)?;
        println!("setup/access: {:.2?}", now.elapsed());
        println!("{}", crs_access.uncompressed_size());
        crs_access.serialize_unchecked(File::create("./data/access.crs")?)?;

        let now = Instant::now();
        let crs_mint = generate_random_parameters::<Bn254, _, _>(mint::MintCircuit::fake(), rng)?;
        println!("setup/mint: {:.2?}", now.elapsed());
        println!("{}", crs_mint.uncompressed_size());
        crs_mint.serialize_unchecked(File::create("./data/mint.crs")?)?;

        for (name, crs) in [("NFT", crs_nft), ("Access", crs_access), ("Mint", crs_mint)] {
            fs::write(
                format!("./contracts/{}.sol", name.to_lowercase()),
                format!(
                    indoc! { r#"
                pragma solidity ^0.8;

                import "./pairing.sol";

                contract {}Verifier {{
                    using Pairing for *;
                    struct VerifyingKey {{
                        uint256[2] alpha_1;
                        uint256[2][2] beta_2;
                        uint256[2][2] gamma_2;
                        uint256[2][2] delta_2;
                        uint256[2][{}] IC;
                    }}

                    function getVK() internal pure returns (VerifyingKey memory vk) {{
                        {}
                        {}
                        {}
                        {}
                        {}
                    }}

                    function verify(
                        uint256[2] memory a,
                        uint256[2][2] memory b,
                        uint256[2] memory c,
                        uint256[] memory input
                    ) public view returns (uint256 r) {{
                        VerifyingKey memory vk = getVK();
                        uint256[2] memory vk_x = vk.IC[0];
                        for (uint256 i = 0; i < input.length; i++) {{
                            vk_x = Pairing.addition(
                                vk_x,
                                Pairing.scalar_mul(vk.IC[i + 1], input[i])
                            );
                        }}
                
                        uint256[2][] memory p1 = new uint256[2][](4);
                        uint256[2][2][] memory p2 = new uint256[2][2][](4);
                        p1[0] = Pairing.negate(a);
                        p1[1] = vk.alpha_1;
                        p1[2] = vk_x;
                        p1[3] = c;
                        p2[0] = b;
                        p2[1] = vk.beta_2;
                        p2[2] = vk.gamma_2;
                        p2[3] = vk.delta_2;
                
                        return Pairing.pairing(p1, p2);
                    }}
                }}
                "# },
                    name,
                    crs.vk.gamma_abc_g1.len(),
                    crs.vk.alpha_g1.to_sol_assignment("vk.alpha_1"),
                    crs.vk.beta_g2.to_sol_assignment("vk.beta_2"),
                    crs.vk.gamma_g2.to_sol_assignment("vk.gamma_2"),
                    crs.vk.delta_g2.to_sol_assignment("vk.delta_2"),
                    crs.vk.gamma_abc_g1.to_sol_assignment("vk.IC"),
                ),
            )?;
        }

        Ok(())
    }

    #[test]
    fn prove() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();

        let pp_rsa: root::Parameters = serde_json::from_reader(File::open("./data/rsa.pp")?)?;
        let pp_enc =
            elgamal::Parameters::<Fr>::deserialize_unchecked(File::open("./data/encryption.pp")?)?;
        let pp_comm = commitment::Parameters::<Fr>::deserialize_unchecked(File::open(
            "./data/commitment.pp",
        )?)?;
        let pp_hash = PoseidonParameters::gen(R_F, R_P, ALPHA, WIDTH);

        let k = Fr::from(61_67_65u64);
        let v = Fr::from(7u64);

        let l_k = k;
        let u_k = k;
        let l_v = Fr::from(1u64);
        let u_v = Fr::from(18u64);

        let (sk, pk) = secp256k1::Secp256k1::new().generate_keypair(rng);
        let (new_sk, new_pk) = secp256k1::Secp256k1::new().generate_keypair(rng);

        let (_, new_ek) = keygen(&new_sk.secret_bytes(), &pp_enc, &pp_hash);

        let r1 = Fr::rand(rng);
        let r2 = Fr::rand(rng);
        let extra = {
            let (q, r) =
                BigUint::from_bytes_be(&sk.secret_bytes()).div_rem(&(BigUint::one() << 128u8));
            (
                ElGamal::encrypt(
                    &pp_enc,
                    &new_ek,
                    &Fr::from_bigint(r.try_into().unwrap()).unwrap(),
                    &r1,
                ),
                ElGamal::encrypt(
                    &pp_enc,
                    &new_ek,
                    &Fr::from_bigint(q.try_into().unwrap()).unwrap(),
                    &r2,
                ),
            )
        };

        let (kk, vv, r_k, r_v) = generate_nft(&pp_comm, &k, &v);
        let (new_kk, new_vv, new_r_k, new_r_v) = generate_nft(&pp_comm, &k, &v);

        let (aux, e_q) = generate_e(&pp_hash, &pk.serialize()[1..], &kk, &vv)?;

        let (o_e, c_e_q) = Pedersen::commit(&pp_comm, &e_q, rng);
        let (o_k, c_k) = Pedersen::commit(&pp_comm, &k, rng);
        let (o_v, c_v) = Pedersen::commit(&pp_comm, &v, rng);

        let e_n: BigUint = e_q.into();
        let e_n: BigInt = e_n.into();

        let r_n: BigInt = rng.gen_biguint_below(&pp_rsa.n).into();
        let w = rng.gen_biguint_below(&pp_rsa.n);
        let a = w.mod_exp(&e_n, &pp_rsa.n);

        let c_e_n =
            pp_rsa.g.mod_exp(&e_n, &pp_rsa.n) * pp_rsa.h.mod_exp(&r_n, &pp_rsa.n) % &pp_rsa.n;

        {
            let s_rsa = root::Statement { c_e: c_e_n.clone(), a };

            serde_json::to_writer(File::create("./data/root.input")?, &s_rsa)?;
            let now = Instant::now();
            let proof =
                root::prove(&pp_rsa, &s_rsa, &root::Witness { w, r: r_n.clone(), e: e_n.clone() });
            println!("prove/root: {:.2?}", now.elapsed());
            serde_json::to_writer(File::create("./data/root.proof")?, &proof)?;
        }
        {
            let s_mod_eq = mod_eq::Statement { c_e_n, c_e_q: c_e_q.into() };

            serde_json::to_writer(File::create("./data/mod_eq.input")?, &s_mod_eq)?;
            let now = Instant::now();
            let proof = mod_eq::prove(
                &mod_eq::Parameters { pp_pedersen: pp_comm.clone(), pp_rsa: pp_rsa.clone() },
                &s_mod_eq,
                &mod_eq::Witness { r_n, e: e_n, r_q: Into::<BigUint>::into(o_e).into() },
            );
            println!("prove/mod_eq: {:.2?}", now.elapsed());
            serde_json::to_writer(File::create("./data/mod_eq.proof")?, &proof)?;
        }
        {
            let crs_nft =
                ProvingKey::<Bn254>::deserialize_unchecked(File::open("./data/nft.crs")?)?;
            let s_nft = nft::Statement { c_e: c_e_q, c_k, c_v };

            s_nft.serialize_unchecked(File::create("./data/nft.input")?)?;
            let now = Instant::now();
            let proof = create_random_proof(
                nft::NFTCircuit {
                    pp: nft::Parameters { pp_hash: pp_hash.clone(), pp_comm: pp_comm.clone() },
                    s: s_nft,
                    w: nft::Witness {
                        aux,
                        sk: sk.secret_bytes().to_vec(),
                        k,
                        v,
                        r_k,
                        r_v,
                        o_e,
                        o_k,
                        o_v,
                    },
                },
                &crs_nft,
                rng,
            )?;
            println!("prove/nft: {:.2?}", now.elapsed());
            proof.serialize_unchecked(File::create("./data/nft.proof")?)?;
        }
        {
            let crs_access =
                ProvingKey::<Bn254>::deserialize_unchecked(File::open("./data/access.crs")?)?;
            let s_access = access::Statement { l_k, u_k, l_v, u_v, c_k, c_v };

            s_access.serialize_unchecked(File::create("./data/access.input")?)?;
            let now = Instant::now();
            let proof = create_random_proof(
                access::RangeCircuit {
                    pp: access::Parameters { pp_comm: pp_comm.clone() },
                    s: s_access,
                    w: access::Witness { k, v, o_k, o_v },
                },
                &crs_access,
                rng,
            )?;
            println!("prove/access: {:.2?}", now.elapsed());
            proof.serialize_unchecked(File::create("./data/access.proof")?)?;
        }
        {
            let crs_mint =
                ProvingKey::<Bn254>::deserialize_unchecked(File::open("./data/mint.crs")?)?;
            let s_mint = mint::Statement {
                c_e: c_e_q,
                extra,
                new_pk: new_pk.serialize().to_vec(),
                new_kk,
                new_vv,
            };

            s_mint.serialize_unchecked(File::create("./data/mint.input")?)?;
            let now = Instant::now();
            let proof = create_random_proof(
                mint::MintCircuit {
                    pp: mint::Parameters {
                        pp_enc: pp_enc.clone(),
                        pp_hash: pp_hash.clone(),
                        pp_comm: pp_comm.clone(),
                    },
                    s: s_mint,
                    w: mint::Witness {
                        aux,
                        sk: sk.secret_bytes().to_vec(),
                        new_sk: new_sk.secret_bytes().to_vec(),
                        k,
                        v,
                        r_k,
                        r_v,
                        new_r_k,
                        new_r_v,
                        r_extra: (r1, r2),
                        o_e,
                    },
                },
                &crs_mint,
                rng,
            )?;
            println!("prove/mint: {:.2?}", now.elapsed());
            proof.serialize_unchecked(File::create("./data/mint.proof")?)?;
        }
        Ok(())
    }

    #[test]
    fn verify() -> Result<(), Box<dyn Error>> {
        let pp_rsa: root::Parameters = serde_json::from_reader(File::open("./data/rsa.pp")?)?;
        let pp_enc =
            elgamal::Parameters::deserialize_unchecked(File::open("./data/encryption.pp")?)?;
        let pp_comm =
            commitment::Parameters::deserialize_unchecked(File::open("./data/commitment.pp")?)?;

        let crs_nft = ProvingKey::<Bn254>::deserialize_unchecked(File::open("./data/nft.crs")?)?;
        let crs_access =
            ProvingKey::<Bn254>::deserialize_unchecked(File::open("./data/access.crs")?)?;
        let crs_mint = ProvingKey::<Bn254>::deserialize_unchecked(File::open("./data/mint.crs")?)?;

        let vk_nft = prepare_verifying_key(&crs_nft.vk);
        let vk_access = prepare_verifying_key(&crs_access.vk);
        let vk_mint = prepare_verifying_key(&crs_mint.vk);

        let π_rsa = serde_json::from_reader(File::open("./data/root.proof")?)?;
        let π_mod_eq = serde_json::from_reader(File::open("./data/mod_eq.proof")?)?;
        let π_nft = Proof::deserialize_unchecked(File::open("./data/nft.proof")?)?;
        let π_access = Proof::deserialize_unchecked(File::open("./data/access.proof")?)?;

        let s_rsa = serde_json::from_reader(File::open("./data/root.input")?)?;
        let s_mod_eq = serde_json::from_reader(File::open("./data/mod_eq.input")?)?;
        let s_nft = nft::Statement::deserialize_unchecked(File::open("./data/nft.input")?)?;
        let s_access =
            access::Statement::deserialize_unchecked(File::open("./data/access.input")?)?;

        let now = Instant::now();
        assert!(root::verify(&pp_rsa, &s_rsa, &π_rsa));
        println!("verify/root: {:.2?}", now.elapsed());

        let now = Instant::now();
        assert!(mod_eq::verify(
            &mod_eq::Parameters { pp_pedersen: pp_comm.clone(), pp_rsa: pp_rsa.clone() },
            &s_mod_eq,
            &π_mod_eq
        ));
        println!("verify/mod_eq: {:.2?}", now.elapsed());

        let now = Instant::now();
        assert!(verify_proof(
            &vk_nft,
            &π_nft,
            &[pp_comm.g, pp_comm.h, s_nft.c_e, s_nft.c_k, s_nft.c_v]
        )?);
        println!("verify/nft: {:.2?}", now.elapsed());

        let now = Instant::now();
        assert!(verify_proof(
            &vk_access,
            &π_access,
            &[
                pp_comm.g,
                pp_comm.h,
                s_access.l_k,
                s_access.u_k,
                s_access.l_v,
                s_access.u_v,
                s_access.c_k,
                s_access.c_v
            ]
        )?);
        println!("verify/access: {:.2?}", now.elapsed());

        let π_mint = Proof::deserialize_unchecked(File::open("./data/mint.proof")?)?;
        let s_mint = mint::Statement::deserialize_unchecked(File::open("./data/mint.input")?)?;

        let now = Instant::now();
        assert!(verify_proof(
            &vk_mint,
            &π_mint,
            &[
                vec![pp_enc.g, pp_comm.g, pp_comm.h],
                secp256k1::constraints::PointVar::<Fr, W>::inputize(&s_mint.new_pk),
                vec![s_mint.new_kk, s_mint.new_vv],
                vec![s_mint.extra.0 .0, s_mint.extra.0 .1, s_mint.extra.1 .0, s_mint.extra.1 .1],
                vec![s_mint.c_e],
            ]
            .concat()
        )?);
        println!("verify/mint: {:.2?}", now.elapsed());

        Ok(())
    }

    #[test]
    fn print_transactions() -> Result<(), Box<dyn Error>> {
        let pp_rsa: root::Parameters = serde_json::from_reader(File::open("./data/rsa.pp")?)?;
        let pp_enc =
            elgamal::Parameters::<Fr>::deserialize_unchecked(File::open("./data/encryption.pp")?)?;
        let pp_comm = commitment::Parameters::<Fr>::deserialize_unchecked(File::open(
            "./data/commitment.pp",
        )?)?;

        let s_rsa: root::Statement = serde_json::from_reader(File::open("./data/root.input")?)?;
        let s_mod_eq: mod_eq::Statement =
            serde_json::from_reader(File::open("./data/mod_eq.input")?)?;
        let s_nft = nft::Statement::<Fr>::deserialize_unchecked(File::open("./data/nft.input")?)?;
        let s_access =
            access::Statement::<Fr>::deserialize_unchecked(File::open("./data/access.input")?)?;

        let π_rsa: root::Proof = serde_json::from_reader(File::open("./data/root.proof")?)?;
        let π_mod_eq: mod_eq::Proof = serde_json::from_reader(File::open("./data/mod_eq.proof")?)?;
        let π_nft = Proof::<Bn254>::deserialize_unchecked(File::open("./data/nft.proof")?)?;
        let π_access = Proof::<Bn254>::deserialize_unchecked(File::open("./data/access.proof")?)?;

        println!(
            "RootVerifier.challenge:\n{},{},{},{},{},{}\n",
            s_rsa.c_e.to_tx(),
            s_rsa.a.to_tx(),
            π_rsa.α_1.to_tx(),
            π_rsa.α_2.to_tx(),
            π_rsa.α_3.to_tx(),
            π_rsa.α_4.to_tx()
        );
        println!(
            "RootVerifier.verify_1:\n{},{},{},{},{},{},{}\n",
            s_rsa.c_e.to_tx(),
            pp_rsa.g.to_tx(),
            pp_rsa.h.to_tx(),
            "\"PLACEHOLDER\"",
            π_rsa.s_e.to_tx(),
            π_rsa.s_r.to_tx(),
            π_rsa.α_1.to_tx()
        );
        println!(
            "RootVerifier.verify_2:\n{},{},{},{},{},{},{}\n",
            π_rsa.c_r.to_tx(),
            pp_rsa.g.to_tx(),
            pp_rsa.h.to_tx(),
            "\"PLACEHOLDER\"",
            π_rsa.s_r_2.to_tx(),
            π_rsa.s_r_3.to_tx(),
            π_rsa.α_2.to_tx()
        );
        println!(
            "RootVerifier.verify_3:\n{},{},{},{},{},{},{}\n",
            s_rsa.a.to_tx(),
            π_rsa.c_w.to_tx(),
            pp_rsa.h.to_tx(),
            "\"PLACEHOLDER\"",
            π_rsa.s_e.to_tx(),
            π_rsa.s_β.to_tx(),
            π_rsa.α_3.to_tx()
        );
        println!(
            "RootVerifier.verify_4:\n{},{},{},{},{},{},{}\n",
            π_rsa.c_r.to_tx(),
            pp_rsa.g.to_tx(),
            pp_rsa.h.to_tx(),
            π_rsa.s_e.to_tx(),
            π_rsa.s_β.to_tx(),
            π_rsa.s_δ.to_tx(),
            π_rsa.α_4.to_tx()
        );
        println!("RootVerifier.verify_range:\n{}\n", π_rsa.s_e.to_tx());

        println!(
            "ModEqVerifier.challenge:\n{},{},{},{}\n",
            s_mod_eq.c_e_n.to_tx(),
            s_mod_eq.c_e_q.to_tx(),
            π_mod_eq.α_1.to_tx(),
            π_mod_eq.α_2.to_tx()
        );
        println!(
            "ModEqVerifier.verify_1:\n{},{},{},{},{},{},{}\n",
            s_mod_eq.c_e_n.to_tx(),
            pp_rsa.g.to_tx(),
            pp_rsa.h.to_tx(),
            "\"PLACEHOLDER\"",
            π_mod_eq.s_e.to_tx(),
            π_mod_eq.s_r_n.to_tx(),
            π_mod_eq.α_1.to_tx()
        );
        println!(
            "ModEqVerifier.verify_2:\n{},{},{},{},{},{},{}\n",
            s_mod_eq.c_e_q.to_tx(),
            pp_comm.g.to_tx(),
            pp_comm.h.to_tx(),
            "\"PLACEHOLDER\"",
            π_mod_eq.s_e.to_tx(),
            π_mod_eq.s_r_q.to_tx(),
            π_mod_eq.α_2.to_tx()
        );

        println!(
            "NFTVerifier.verify:\n{},{},{},{}\n",
            π_nft.a.to_tx(),
            π_nft.b.to_tx(),
            π_nft.c.to_tx(),
            [pp_comm.g, pp_comm.h, s_nft.c_e, s_nft.c_k, s_nft.c_v].to_tx()
        );

        println!(
            "AccessVerifier.verify:\n{},{},{},{}\n",
            π_access.a.to_tx(),
            π_access.b.to_tx(),
            π_access.c.to_tx(),
            [
                pp_comm.g,
                pp_comm.h,
                s_access.l_k,
                s_access.u_k,
                s_access.l_v,
                s_access.u_v,
                s_access.c_k,
                s_access.c_v
            ]
            .to_tx()
        );

        let s_mint =
            mint::Statement::<Fr>::deserialize_unchecked(File::open("./data/mint.input")?)?;
        let π_mint = Proof::<Bn254>::deserialize_unchecked(File::open("./data/mint.proof")?)?;

        println!(
            "MintVerifier.verify:\n{},{},{},{}\n",
            π_mint.a.to_tx(),
            π_mint.b.to_tx(),
            π_mint.c.to_tx(),
            [
                vec![pp_enc.g, pp_comm.g, pp_comm.h],
                secp256k1::constraints::PointVar::<Fr, W>::inputize(&s_mint.new_pk),
                vec![s_mint.new_kk, s_mint.new_vv],
                vec![s_mint.extra.0 .0, s_mint.extra.0 .1, s_mint.extra.1 .0, s_mint.extra.1 .1],
                vec![s_mint.c_e],
            ]
            .concat()
            .to_tx()
        );

        Ok(())
    }

    #[test]
    fn print_tests() -> Result<(), Box<dyn Error>> {
        let pp_rsa: root::Parameters = serde_json::from_reader(File::open("./data/rsa.pp")?)?;
        let pp_enc =
            elgamal::Parameters::<Fr>::deserialize_unchecked(File::open("./data/encryption.pp")?)?;
        let pp_comm = commitment::Parameters::<Fr>::deserialize_unchecked(File::open(
            "./data/commitment.pp",
        )?)?;

        let s_rsa: root::Statement = serde_json::from_reader(File::open("./data/root.input")?)?;
        let s_mod_eq: mod_eq::Statement =
            serde_json::from_reader(File::open("./data/mod_eq.input")?)?;
        let s_nft = nft::Statement::<Fr>::deserialize_unchecked(File::open("./data/nft.input")?)?;
        let s_access =
            access::Statement::<Fr>::deserialize_unchecked(File::open("./data/access.input")?)?;

        let π_rsa: root::Proof = serde_json::from_reader(File::open("./data/root.proof")?)?;
        let π_mod_eq: mod_eq::Proof = serde_json::from_reader(File::open("./data/mod_eq.proof")?)?;
        let π_nft = Proof::<Bn254>::deserialize_unchecked(File::open("./data/nft.proof")?)?;
        let π_access = Proof::<Bn254>::deserialize_unchecked(File::open("./data/access.proof")?)?;

        println!(
            indoc! {
                r#"
                contract TestRootVerifier {{
                    bytes c_e = {};
                    bytes a = {};
                    bytes alpha_1 = {};
                    bytes alpha_2 = {};
                    bytes alpha_3 = {};
                    bytes alpha_4 = {};
                    bytes g = {};
                    bytes h = {};
                    bytes c_r = {};
                    bytes c_w = {};
                    bytes s_e = {};
                    bool neg_s_e = {};
                    bytes s_r = {};
                    bool neg_s_r = {};
                    bytes s_r_2 = {};
                    bool neg_s_r_2 = {};
                    bytes s_r_3 = {};
                    bool neg_s_r_3 = {};
                    bytes s_beta = {};
                    bool neg_s_beta = {};
                    bytes s_delta = {};
                    bool neg_s_delta = {};
                
                    function test_verify(address addr) public {{
                        RootVerifier v = RootVerifier(addr);
                        bytes memory c = bytes.concat(
                            v.challenge(c_e, a, alpha_1, alpha_2, alpha_3, alpha_4)
                        );
                        assert(v.verify_1(c_e, g, h, c, s_e, neg_s_e, s_r, neg_s_r, alpha_1));
                        assert(v.verify_2(c_r, g, h, c, s_r_2, neg_s_r_2, s_r_3, neg_s_r_3, alpha_2));
                        assert(v.verify_3(a, c_w, h, c, s_e, neg_s_e, s_beta, neg_s_beta, alpha_3));
                        assert(v.verify_4(c_r, g, h, s_e, neg_s_e, s_beta, neg_s_beta, s_delta, neg_s_delta, alpha_4));
                        assert(v.verify_range(s_e));
                    }}
                }}
                "#
            },
            s_rsa.c_e.to_hex(),
            s_rsa.a.to_hex(),
            π_rsa.α_1.to_hex(),
            π_rsa.α_2.to_hex(),
            π_rsa.α_3.to_hex(),
            π_rsa.α_4.to_hex(),
            pp_rsa.g.to_hex(),
            pp_rsa.h.to_hex(),
            π_rsa.c_r.to_hex(),
            π_rsa.c_w.to_hex(),
            π_rsa.s_e.to_hex(),
            match π_rsa.s_e.sign() {
                Sign::Minus => "true",
                _ => "false",
            },
            π_rsa.s_r.to_hex(),
            match π_rsa.s_r.sign() {
                Sign::Minus => "true",
                _ => "false",
            },
            π_rsa.s_r_2.to_hex(),
            match π_rsa.s_r_2.sign() {
                Sign::Minus => "true",
                _ => "false",
            },
            π_rsa.s_r_3.to_hex(),
            match π_rsa.s_r_3.sign() {
                Sign::Minus => "true",
                _ => "false",
            },
            π_rsa.s_β.to_hex(),
            match π_rsa.s_β.sign() {
                Sign::Minus => "true",
                _ => "false",
            },
            π_rsa.s_δ.to_hex(),
            match π_rsa.s_δ.sign() {
                Sign::Minus => "true",
                _ => "false",
            },
        );

        println!(
            indoc! {r#"
                contract TestModEqVerifier {{
                    bytes c_e_n = {};
                    bytes c_e_q = {};
                    bytes g = {};
                    bytes h = {};
                    bytes gg = {};
                    bytes hh = {};
                    bytes alpha_1 = {};
                    bytes alpha_2 = {};
                    bytes s_e = {};
                    bool neg_s_e = {};
                    bytes s_r_n = {};
                    bool neg_s_r_n = {};
                    bytes s_r_q = {};
                    bool neg_s_r_q = {};

                    function test_verify(address addr) public {{
                        ModEqVerifier v = ModEqVerifier(addr);
                        bytes memory c = bytes.concat(
                            v.challenge(c_e_n, c_e_q, alpha_1, alpha_2)
                        );
                        assert(v.verify_1(c_e_n, g, h, c, s_e, neg_s_e, s_r_n, neg_s_r_n, alpha_1));
                        assert(v.verify_2(c_e_q, gg, hh, c, s_e, neg_s_e, s_r_q, neg_s_r_q, alpha_2));
                    }}
                }}
                "#},
            s_mod_eq.c_e_n.to_hex(),
            s_mod_eq.c_e_q.to_hex(),
            pp_rsa.g.to_hex(),
            pp_rsa.h.to_hex(),
            pp_comm.g.to_hex(),
            pp_comm.h.to_hex(),
            π_mod_eq.α_1.to_hex(),
            π_mod_eq.α_2.to_hex(),
            π_mod_eq.s_e.to_hex(),
            match π_mod_eq.s_e.sign() {
                Sign::Minus => "true",
                _ => "false",
            },
            π_mod_eq.s_r_n.to_hex(),
            match π_mod_eq.s_r_n.sign() {
                Sign::Minus => "true",
                _ => "false",
            },
            π_mod_eq.s_r_q.to_hex(),
            match π_mod_eq.s_r_q.sign() {
                Sign::Minus => "true",
                _ => "false",
            },
        );

        println!(
            indoc! { r#"
                contract TestNFTVerifier {{
                    uint256[2] a = {};
                    uint256[2][2] b = {};
                    uint256[2] c = {};
                    uint256[] input = {};
                    function test_verify(address addr) public {{
                        NFTVerifier v = NFTVerifier(addr);
                        assert(v.verify(a, b, c, input) == 1);
                    }}
                }}
                "# },
            π_nft.a.to_sol_expr(),
            π_nft.b.to_sol_expr(),
            π_nft.c.to_sol_expr(),
            [pp_comm.g, pp_comm.h, s_nft.c_e, s_nft.c_k, s_nft.c_v].to_sol_expr()
        );

        println!(
            indoc! { r#"
                contract TestAccessVerifier {{
                    uint256[2] a = {};
                    uint256[2][2] b = {};
                    uint256[2] c = {};
                    uint256[] input = {};
                    function test_verify(address addr) public {{
                        AccessVerifier v = AccessVerifier(addr);
                        assert(v.verify(a, b, c, input) == 1);
                    }}
                }}
                "# },
            π_access.a.to_sol_expr(),
            π_access.b.to_sol_expr(),
            π_access.c.to_sol_expr(),
            [
                pp_comm.g,
                pp_comm.h,
                s_access.l_k,
                s_access.u_k,
                s_access.l_v,
                s_access.u_v,
                s_access.c_k,
                s_access.c_v
            ]
            .to_sol_expr()
        );

        let s_mint =
            mint::Statement::<Fr>::deserialize_unchecked(File::open("./data/mint.input")?)?;
        let π_mint = Proof::<Bn254>::deserialize_unchecked(File::open("./data/mint.proof")?)?;

        println!(
            indoc! {r#"
            contract TestMintVerifier {{
                uint256[2] a = {};
                uint256[2][2] b = {};
                uint256[2] c = {};
                uint256[] input = {};
                function test_verify(address addr) public {{
                    MintVerifier v = MintVerifier(addr);
                    assert(v.verify(a, b, c, input) == 1);
                }}
            }}
            "# },
            π_mint.a.to_sol_expr(),
            π_mint.b.to_sol_expr(),
            π_mint.c.to_sol_expr(),
            [
                vec![pp_enc.g, pp_comm.g, pp_comm.h],
                secp256k1::constraints::PointVar::<Fr, W>::inputize(&s_mint.new_pk),
                vec![s_mint.new_kk, s_mint.new_vv],
                vec![s_mint.extra.0 .0, s_mint.extra.0 .1, s_mint.extra.1 .0, s_mint.extra.1 .1],
                vec![s_mint.c_e],
            ]
            .concat()
            .to_sol_expr()
        );

        Ok(())
    }
}
