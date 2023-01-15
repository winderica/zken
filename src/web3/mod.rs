#[cfg(test)]
mod tests {
    use std::{
        error::Error,
        fs::{self, File},
        io::{Read, Write},
        sync::Arc,
    };

    use ark_bn254::{Bn254, Fr};
    use ark_ff::{BigInteger, Fp256, Fp256Parameters, One, PrimeField, UniformRand};
    use ark_groth16::{create_random_proof, generate_random_parameters, ProvingKey};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
    use ethers::{
        abi::{Abi, Token, Tokenize},
        contract::Contract,
        prelude::{ContractFactory, SignerMiddleware, *},
        providers::{Http, Middleware, Provider},
        signers::{LocalWallet, Signer},
        solc::{Artifact, Project, ProjectPathsConfig},
        types::Bytes,
    };
    use indoc::indoc;
    use num::{bigint::RandBigInt, BigInt, BigUint, Integer, Signed};
    use num_modular::ModularPow;
    use rand::thread_rng;
    use serde::{Deserialize, Serialize};

    use crate::{
        constants::{ALPHA, R_F, R_P, WIDTH, λ_z, λ_s, μ},
        primitives::{
            commitment::{self, Pedersen},
            poseidon::PoseidonParameters,
            secp256k1::constraints::parse_pk,
        },
        utils::{Mod, ToSolidity}, protocols::{Params, CRS},
    };

    trait ToToken {
        fn to_token(&self) -> Token;
    }

    impl ToToken for Token {
        fn to_token(&self) -> Token {
            self.clone()
        }
    }

    impl ToToken for bool {
        fn to_token(&self) -> Token {
            Token::Bool(*self)
        }
    }

    impl ToToken for BigUint {
        fn to_token(&self) -> Token {
            let mut x = self.to_radix_le(256);
            x.resize(x.len().next_multiple_of(32), 0);
            x.reverse();
            Token::Bytes(x)
        }
    }

    impl ToToken for BigInt {
        fn to_token(&self) -> Token {
            Token::Tuple(vec![
                self.abs().to_biguint().unwrap().to_token(),
                self.is_negative().to_token(),
            ])
        }
    }

    impl<F: Fp256Parameters> ToToken for Fp256<F> {
        fn to_token(&self) -> Token {
            Token::Uint(U256::from_big_endian(&self.into_bigint().to_bytes_be()))
        }
    }

    impl<T: ToToken, const W: usize> ToToken for [T; W] {
        fn to_token(&self) -> Token {
            Token::FixedArray(self.iter().map(|i| i.to_token()).collect())
        }
    }

    impl<T: ToToken> ToToken for Vec<T> {
        fn to_token(&self) -> Token {
            Token::Array(self.iter().map(|i| i.to_token()).collect())
        }
    }

    async fn deploy_contract<T: Tokenize, M: Middleware>(
        output: &ProjectCompileOutput,
        client: &Arc<M>,
        name: &str,
        args: T,
    ) -> Result<Contract<M>, ContractError<M>> {
        let (abi, bytecode, _) = output.find_first(name).unwrap().clone().into_parts();
        ContractFactory::new(abi.unwrap(), bytecode.unwrap(), client.clone())
            .deploy(args)?
            .send()
            .await
    }

    #[derive(Serialize, Deserialize, Debug)]
    struct DeployedContract {
        address: Address,
        abi: Abi,
    }

    impl<M: Middleware> From<Contract<M>> for DeployedContract {
        fn from(contract: Contract<M>) -> Self {
            Self { address: contract.address(), abi: contract.abi().clone() }
        }
    }

    #[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
    struct NFT<F: PrimeField>(F, F, F, F);

    #[tokio::test]
    async fn test_setup() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();

        let pp = Params::<Fr>::default();

        serde_json::to_writer(File::create("./data/pp.bin")?, &pp)?;

        let crs = CRS::<Bn254>::setup(&pp, rng)?;
        crs.serialize_unchecked(File::create("./data/crs.bin")?)?;

        for (name, crs) in [("Form", crs.form), ("Recv", crs.recv), ("BindId", crs.bind_id), ("Range", crs.range)] {
            fs::write(
                format!("./contracts/{}.sol", name.to_lowercase()),
                format!(
                    indoc! { r#"
                pragma solidity ^0.8;

                import "./pairing.sol";

                contract {}Verifier {{
                    using Pairing for *;

                    function verify(
                        uint256[2] memory a,
                        uint256[2][2] memory b,
                        uint256[2] memory c,
                        uint256[] memory input
                    ) public view returns (uint256 r) {{
                        uint256[2][{}] memory IC = {};
                        uint256[2] memory vk_x = IC[0];
                        for (uint256 i = 0; i < input.length; i++) {{
                            vk_x = Pairing.addition(
                                vk_x,
                                Pairing.scalar_mul(IC[i + 1], input[i])
                            );
                        }}
                
                        uint256[2][] memory p1 = new uint256[2][](4);
                        uint256[2][2][] memory p2 = new uint256[2][2][](4);
                        p1[0] = Pairing.negate(a);
                        {}
                        p1[2] = vk_x;
                        p1[3] = c;
                        p2[0] = b;
                        {}
                        {}
                        {}
                
                        return Pairing.pairing(p1, p2);
                    }}
                }}
                "# },
                    name,
                    crs.vk.gamma_abc_g1.len(),
                    crs.vk.gamma_abc_g1.to_sol_expr(),
                    crs.vk.alpha_g1.to_sol_assignment("p1[1]"),
                    crs.vk.beta_g2.to_sol_assignment("p2[1]"),
                    crs.vk.gamma_g2.to_sol_assignment("p2[2]"),
                    crs.vk.delta_g2.to_sol_assignment("p2[3]"),
                ),
            )?;
        }

        let keystore = fs::read_dir("./geth/keystore")?.collect::<Result<Vec<_>, _>>()?;
        let wallet: LocalWallet = LocalWallet::decrypt_keystore(keystore[0].path(), "")?;

        let provider = Provider::<Http>::try_from("http://127.0.0.1:8545")?;

        let client =
            SignerMiddleware::new(provider.clone(), wallet.clone().with_chain_id(12345u64));
        let client = Arc::new(client);

        let project = Project::builder()
            .paths(
                ProjectPathsConfig::builder().root("./contracts").sources("./contracts").build()?,
            )
            .ephemeral()
            .no_artifacts()
            .build()?;
        let output = project.compile()?;

        let accumulator = deploy_contract(
            &output,
            &client,
            "Accumulator",
            rng.gen_biguint_below(&pp.r.n).to_token(),
        )
        .await?;
        let root_verifier =
            deploy_contract(&output, &client, "RootVerifier", Token::Uint(U256::from(λ_z + λ_s + μ + 1))).await?;
        let mod_eq_verifier = deploy_contract(&output, &client, "ModEqVerifier", ()).await?;
        let form_verifier = deploy_contract(&output, &client, "FormVerifier", ()).await?;
        let recv_verifier = deploy_contract(&output, &client, "RecvVerifier", ()).await?;
        let bind_id_verifier = deploy_contract(&output, &client, "BindIdVerifier", ()).await?;
        let range_verifier = deploy_contract(&output, &client, "RangeVerifier", ()).await?;

        let poseidon = deploy_contract(&output, &client, "PoseidonHash", ()).await?;
        let manager = deploy_contract(
            &output,
            &client,
            "TokenManager",
            (
                poseidon.address(),
                accumulator.address(),
                root_verifier.address(),
                mod_eq_verifier.address(),
                mint_verifier.address(),
                (
                    pp_enc.g.to_token(),
                    pp_comm.g.to_token(),
                    pp_comm.h.to_token(),
                    pp_rsa.g.to_token(),
                    pp_rsa.h.to_token(),
                ),
            ),
        )
        .await?;
        let (l_k, u_k, l_v, u_v) =
            (Fr::from(61_67_65u64), Fr::from(61_67_65u64), Fr::from(1u64), Fr::from(18u64));
        let app = deploy_contract(
            &output,
            &client,
            "App",
            (
                accumulator.address(),
                root_verifier.address(),
                mod_eq_verifier.address(),
                nft_verifier.address(),
                access_verifier.address(),
                (
                    pp_enc.g.to_token(),
                    pp_comm.g.to_token(),
                    pp_comm.h.to_token(),
                    pp_rsa.g.to_token(),
                    pp_rsa.h.to_token(),
                ),
                (l_k.to_token(), u_k.to_token(), l_v.to_token(), u_v.to_token()),
            ),
        )
        .await?;

        // Issue random NFTs in advance
        for _ in 0..10 {
            let wallet = LocalWallet::new(rng);
            let sk = wallet.signer();
            let pk = parse_pk(&sk.verifying_key().to_bytes());
            let pk_x = U256::from_big_endian(&pk.0.to_bytes_be());
            let pk_y = U256::from_big_endian(&pk.1.to_bytes_be());

            let kk = Fr::rand(rng);
            let vv = Fr::rand(rng);
            let (aux, _) = generate_e(&pp_hash, &sk.verifying_key().to_bytes()[1..], &kk, &vv)?;
            manager
                .method::<_, U256>(
                    "issue",
                    ([pk_x, pk_y], kk.to_token(), vv.to_token(), aux.to_token()),
                )?
                .send()
                .await?
                .await?
                .unwrap();
        }

        serde_json::to_writer(
            File::create("./data/contracts.json")?,
            &vec![
                accumulator,
                root_verifier,
                mod_eq_verifier,
                nft_verifier,
                access_verifier,
                mint_verifier,
                manager,
                app,
            ]
            .into_iter()
            .map(DeployedContract::from)
            .collect::<Vec<_>>(),
        )?;

        Ok(())
    }

    // #[tokio::test]
    // async fn test_issue() -> Result<(), Box<dyn Error>> {
    //     let pp_comm = commitment::Parameters::<Fr>::deserialize_unchecked(File::open(
    //         "./data/commitment.pp",
    //     )?)?;
    //     let pp_hash = PoseidonParameters::gen(R_F, R_P, ALPHA, WIDTH);

    //     let keystore = fs::read_dir("./geth/keystore")?.collect::<Result<Vec<_>, _>>()?;
    //     let wallet: LocalWallet = LocalWallet::decrypt_keystore(keystore[0].path(), "")?;

    //     let provider = Provider::<Http>::try_from("http://127.0.0.1:8545")?;

    //     let client =
    //         SignerMiddleware::new(provider.clone(), wallet.clone().with_chain_id(12345u64));

    //     let contracts: Vec<DeployedContract> =
    //         serde_json::from_reader(File::open("./data/contracts.json")?)?;
    //     let contracts = contracts
    //         .iter()
    //         .map(|i| Contract::new(i.address, i.abi.clone(), client.clone()))
    //         .collect::<Vec<_>>();
    //     let manager = &contracts[6];

    //     let (k, v) = (Fr::from(61_67_65u64), Fr::from(7u64));

    //     let sk = wallet.signer();
    //     let pk = parse_pk(&sk.verifying_key().to_bytes());
    //     let pk_x = U256::from_big_endian(&pk.0.to_bytes_be());
    //     let pk_y = U256::from_big_endian(&pk.1.to_bytes_be());

    //     let (kk, vv, r_k, r_v) = generate_nft(&pp_comm, &k, &v);
    //     let (aux, _) = generate_e(&pp_hash, &sk.verifying_key().to_bytes()[1..], &kk, &vv)?;

    //     manager
    //         .method::<_, U256>(
    //             "issue",
    //             ([pk_x, pk_y], kk.to_token(), vv.to_token(), aux.to_token()),
    //         )?
    //         .send()
    //         .await?
    //         .await?
    //         .unwrap();

    //     NFT(kk, vv, r_k, r_v).serialize_unchecked(File::create("./data/nft")?)?;
    //     Ok(())
    // }

    // #[tokio::test]
    // async fn test_authenticate() -> Result<(), Box<dyn Error>> {
    //     let rng = &mut thread_rng();

    //     let pp_rsa: root::Parameters = serde_json::from_reader(File::open("./data/rsa.pp")?)?;
    //     let pp_comm = commitment::Parameters::<Fr>::deserialize_unchecked(File::open(
    //         "./data/commitment.pp",
    //     )?)?;
    //     let pp_hash = PoseidonParameters::gen(R_F, R_P, ALPHA, WIDTH);

    //     let keystore = fs::read_dir("./geth/keystore")?.collect::<Result<Vec<_>, _>>()?;
    //     let wallet: LocalWallet = LocalWallet::decrypt_keystore(keystore[0].path(), "")?;

    //     let provider = Provider::<Http>::try_from("http://127.0.0.1:8545")?;

    //     let client =
    //         SignerMiddleware::new(provider.clone(), wallet.clone().with_chain_id(12345u64));

    //     let contracts: Vec<DeployedContract> =
    //         serde_json::from_reader(File::open("./data/contracts.json")?)?;
    //     let contracts = contracts
    //         .iter()
    //         .map(|i| Contract::new(i.address, i.abi.clone(), client.clone()))
    //         .collect::<Vec<_>>();
    //     let accumulator = &contracts[0];
    //     // let root_verifier = &contracts[1];
    //     // let mod_eq_verifier = &contracts[2];
    //     // let nft_verifier = &contracts[3];
    //     // let access_verifier = &contracts[4];
    //     let app = &contracts[7];

    //     let (k, v) = (Fr::from(61_67_65u64), Fr::from(7u64));

    //     let sk = wallet.signer();

    //     let NFT(kk, vv, r_k, r_v) = NFT::<Fr>::deserialize_unchecked(File::open("./data/nft")?)?;
    //     let (aux, e_q) = generate_e(&pp_hash, &sk.verifying_key().to_bytes()[1..], &kk, &vv)?;

    //     let e_n: BigUint = e_q.into();

    //     let mut w = BigUint::from_radix_be(
    //         &accumulator.method::<_, Bytes>("get_base", ())?.call().await?,
    //         256,
    //     )
    //     .unwrap();

    //     for e in accumulator.method::<_, Vec<Bytes>>("get_all", ())?.call().await? {
    //         let e = BigUint::from_radix_be(&e, 256).unwrap();
    //         if e != e_n {
    //             w = w.powm(&e, &pp_rsa.n);
    //         }
    //     }

    //     let a = BigUint::from_radix_be(
    //         &accumulator.method::<_, Bytes>("get_current", ())?.call().await?,
    //         256,
    //     )
    //     .unwrap();

    //     let (l_k, u_k, l_v, u_v) = (k, k, Fr::from(1u64), Fr::from(18u64));

    //     let (o_e, c_e_q) = Pedersen::commit(&pp_comm, &e_q, rng);
    //     let (o_k, c_k) = Pedersen::commit(&pp_comm, &k, rng);
    //     let (o_v, c_v) = Pedersen::commit(&pp_comm, &v, rng);

    //     let r_n: BigInt = rng.gen_biguint_below(&pp_rsa.n).into();

    //     let e_n: BigInt = e_n.into();
    //     let c_e_n =
    //         pp_rsa.g.mod_exp(&e_n, &pp_rsa.n) * pp_rsa.h.mod_exp(&r_n, &pp_rsa.n) % &pp_rsa.n;

    //     let s_rsa = root::Statement { c_e: c_e_n.clone(), a: a.clone() };

    //     let pi_root =
    //         root::prove(&pp_rsa, &s_rsa, &root::Witness { w, r: r_n.clone(), e: e_n.clone() });

    //     // assert!(
    //     //     root_verifier
    //     //         .method::<_, bool>(
    //     //             "verify",
    //     //             (
    //     //                 [pp_rsa.g.clone(), pp_rsa.h.clone()].to_token(),
    //     //                 a.to_token(),
    //     //                 c_e_n.to_token(),
    //     //                 pi_root.c_r.to_token(),
    //     //                 pi_root.c_w.to_token(),
    //     //                 pi_root.s_e.to_token(),
    //     //                 [pi_root.s_r, pi_root.s_r_2, pi_root.s_r_3].to_token(),
    //     //                 pi_root.s_β.to_token(),
    //     //                 pi_root.s_δ.to_token(),
    //     //                 [pi_root.α_1, pi_root.α_2, pi_root.α_3, pi_root.α_4].to_token(),
    //     //             ),
    //     //         )?
    //     //         .call()
    //     //         .await?
    //     // );

    //     let s_mod_eq = mod_eq::Statement { c_e_n: c_e_n.clone(), c_e_q: c_e_q.into() };

    //     let pi_mod_eq = mod_eq::prove(
    //         &mod_eq::Parameters { pp_pedersen: pp_comm.clone(), pp_rsa: pp_rsa.clone() },
    //         &s_mod_eq,
    //         &mod_eq::Witness { r_n, e: e_n, r_q: Into::<BigUint>::into(o_e).into() },
    //     );

    //     // assert!(
    //     //     mod_eq_verifier
    //     //         .method::<_, bool>(
    //     //             "verify",
    //     //             (
    //     //                 [pp_rsa.g, pp_rsa.h, pp_comm.g.into(), pp_comm.h.into()].to_token(),
    //     //                 [c_e_n.clone(), c_e_q.into()].to_token(),
    //     //                 pi_mod_eq.s_e.to_token(),
    //     //                 pi_mod_eq.s_r_n.to_token(),
    //     //                 pi_mod_eq.s_r_q.to_token(),
    //     //                 [pi_mod_eq.α_1, pi_mod_eq.α_2].to_token(),
    //     //             ),
    //     //         )?
    //     //         .call()
    //     //         .await?
    //     // );

    //     let crs_nft = ProvingKey::<Bn254>::deserialize_unchecked(File::open("./data/nft.crs")?)?;
    //     let s_nft = nft::Statement { c_e: c_e_q, c_k, c_v };

    //     let pi_nft = create_random_proof(
    //         nft::NFTCircuit {
    //             pp: nft::Parameters { pp_hash: pp_hash.clone(), pp_comm: pp_comm.clone() },
    //             s: s_nft,
    //             w: nft::Witness { aux, sk: sk.to_bytes().to_vec(), k, v, r_k, r_v, o_e, o_k, o_v },
    //         },
    //         &crs_nft,
    //         rng,
    //     )?;
    //     // assert_eq!(
    //     //     nft_verifier
    //     //         .method::<_, U256>(
    //     //             "verify",
    //     //             (
    //     //                 [pi_nft.a.x, pi_nft.a.y].to_token(),
    //     //                 [
    //     //                     [pi_nft.b.x.c1, pi_nft.b.x.c0],
    //     //                     [pi_nft.b.y.c1, pi_nft.b.y.c0]
    //     //                 ]
    //     //                 .to_token(),
    //     //                 [pi_nft.c.x, pi_nft.c.y].to_token(),
    //     //                 vec![pp_comm.g, pp_comm.h, c_e_q, c_k, c_v].to_token(),
    //     //             ),
    //     //         )?
    //     //         .call()
    //     //         .await?,
    //     //     U256::from(1)
    //     // );

    //     let crs_access =
    //         ProvingKey::<Bn254>::deserialize_unchecked(File::open("./data/access.crs")?)?;
    //     let s_access = access::Statement { l_k, u_k, l_v, u_v, c_k, c_v };

    //     let pi_access = create_random_proof(
    //         access::RangeCircuit {
    //             pp: access::Parameters { pp_comm: pp_comm.clone() },
    //             s: s_access,
    //             w: access::Witness { k, v, o_k, o_v },
    //         },
    //         &crs_access,
    //         rng,
    //     )?;
    //     // assert_eq!(
    //     //     access_verifier
    //     //         .method::<_, U256>(
    //     //             "verify",
    //     //             (
    //     //                 [pi_access.a.x, pi_access.a.y].to_token(),
    //     //                 [
    //     //                     [pi_access.b.x.c1, pi_access.b.x.c0],
    //     //                     [pi_access.b.y.c1, pi_access.b.y.c0]
    //     //                 ]
    //     //                 .to_token(),
    //     //                 [pi_access.c.x, pi_access.c.y].to_token(),
    //     //                 vec![pp_comm.g, pp_comm.h, l_k, u_k, l_v, u_v, c_k, c_v].to_token(),
    //     //             ),
    //     //         )?
    //     //         .call()
    //     //         .await?,
    //     //     U256::from(1)
    //     // );

    //     assert_eq!(
    //         app.method::<_, I256>(
    //             "auth",
    //             (
    //                 c_k.to_token(),
    //                 c_v.to_token(),
    //                 c_e_n.to_token(),
    //                 c_e_q.to_token(),
    //                 (
    //                     (
    //                         pi_root.c_r.to_token(),
    //                         pi_root.c_w.to_token(),
    //                         pi_root.s_e.to_token(),
    //                         [pi_root.s_r, pi_root.s_r_2, pi_root.s_r_3].to_token(),
    //                         pi_root.s_β.to_token(),
    //                         pi_root.s_δ.to_token(),
    //                         [pi_root.α_1, pi_root.α_2, pi_root.α_3, pi_root.α_4].to_token(),
    //                     ),
    //                     (
    //                         pi_mod_eq.s_e.to_token(),
    //                         pi_mod_eq.s_r_n.to_token(),
    //                         pi_mod_eq.s_r_q.to_token(),
    //                         [pi_mod_eq.α_1, pi_mod_eq.α_2].to_token(),
    //                     ),
    //                     (
    //                         [pi_nft.a.x, pi_nft.a.y].to_token(),
    //                         [[pi_nft.b.x.c1, pi_nft.b.x.c0], [pi_nft.b.y.c1, pi_nft.b.y.c0],]
    //                             .to_token(),
    //                         [pi_nft.c.x, pi_nft.c.y].to_token(),
    //                     ),
    //                     (
    //                         [pi_access.a.x, pi_access.a.y].to_token(),
    //                         [
    //                             [pi_access.b.x.c1, pi_access.b.x.c0],
    //                             [pi_access.b.y.c1, pi_access.b.y.c0]
    //                         ]
    //                         .to_token(),
    //                         [pi_access.c.x, pi_access.c.y].to_token(),
    //                     ),
    //                 ),
    //             ),
    //         )?
    //         .call()
    //         .await?,
    //         I256::from(0)
    //     );

    //     Ok(())
    // }

    // #[tokio::test]
    // async fn test_mint() -> Result<(), Box<dyn Error>> {
    //     let rng = &mut thread_rng();

    //     let pp_rsa: root::Parameters = serde_json::from_reader(File::open("./data/rsa.pp")?)?;
    //     let pp_enc =
    //         elgamal::Parameters::<Fr>::deserialize_unchecked(File::open("./data/encryption.pp")?)?;
    //     let pp_comm = commitment::Parameters::<Fr>::deserialize_unchecked(File::open(
    //         "./data/commitment.pp",
    //     )?)?;
    //     let pp_hash = PoseidonParameters::gen(R_F, R_P, ALPHA, WIDTH);

    //     let keystore = fs::read_dir("./geth/keystore")?.collect::<Result<Vec<_>, _>>()?;
    //     let wallet: LocalWallet = LocalWallet::decrypt_keystore(keystore[0].path(), "")?;
    //     let new_wallet: LocalWallet = LocalWallet::new(rng);

    //     let provider = Provider::<Http>::try_from("http://127.0.0.1:8545")?;

    //     let client =
    //         SignerMiddleware::new(provider.clone(), wallet.clone().with_chain_id(12345u64));

    //     let contracts: Vec<DeployedContract> =
    //         serde_json::from_reader(File::open("./data/contracts.json")?)?;
    //     let contracts = contracts
    //         .iter()
    //         .map(|i| Contract::new(i.address, i.abi.clone(), client.clone()))
    //         .collect::<Vec<_>>();
    //     let accumulator = &contracts[0];
    //     // let root_verifier = &contracts[1];
    //     // let mod_eq_verifier = &contracts[2];
    //     // let mint_verifier = &contracts[5];
    //     let manager = &contracts[6];

    //     let (k, v) = (Fr::from(61_67_65u64), Fr::from(7u64));

    //     let sk = wallet.signer();
    //     let new_sk = new_wallet.signer();
    //     let (_, new_ek) = keygen(&new_sk.to_bytes(), &pp_enc, &pp_hash);

    //     let r1 = Fr::rand(rng);
    //     let r2 = Fr::rand(rng);
    //     let extra = {
    //         let (q, r) = BigUint::from_bytes_be(&sk.to_bytes()).div_rem(&(BigUint::one() << 128u8));
    //         (
    //             ElGamal::encrypt(
    //                 &pp_enc,
    //                 &new_ek,
    //                 &Fr::from_bigint(r.try_into().unwrap()).unwrap(),
    //                 &r1,
    //             ),
    //             ElGamal::encrypt(
    //                 &pp_enc,
    //                 &new_ek,
    //                 &Fr::from_bigint(q.try_into().unwrap()).unwrap(),
    //                 &r2,
    //             ),
    //         )
    //     };

    //     let NFT(kk, vv, r_k, r_v) = NFT::deserialize_unchecked(File::open("./data/nft")?)?;
    //     let (new_kk, new_vv, new_r_k, new_r_v) = generate_nft(&pp_comm, &k, &v);

    //     let (aux, e_q) = generate_e(&pp_hash, &sk.verifying_key().to_bytes()[1..], &kk, &vv)?;
    //     let (new_aux, _) =
    //         generate_e(&pp_hash, &new_sk.verifying_key().to_bytes()[1..], &new_kk, &new_vv)?;

    //     let e_n: BigUint = e_q.into();

    //     let mut w = BigUint::from_radix_be(
    //         &accumulator.method::<_, Bytes>("get_base", ())?.call().await?,
    //         256,
    //     )
    //     .unwrap();

    //     for e in accumulator.method::<_, Vec<Bytes>>("get_all", ())?.call().await? {
    //         let e = BigUint::from_radix_be(&e, 256).unwrap();
    //         if e != e_n {
    //             w = w.powm(&e, &pp_rsa.n);
    //         }
    //     }

    //     let a = BigUint::from_radix_be(
    //         &accumulator.method::<_, Bytes>("get_current", ())?.call().await?,
    //         256,
    //     )
    //     .unwrap();

    //     let (o_e, c_e_q) = Pedersen::commit(&pp_comm, &e_q, rng);

    //     let r_n: BigInt = rng.gen_biguint_below(&pp_rsa.n).into();

    //     let e_n: BigInt = e_n.into();
    //     let c_e_n =
    //         pp_rsa.g.mod_exp(&e_n, &pp_rsa.n) * pp_rsa.h.mod_exp(&r_n, &pp_rsa.n) % &pp_rsa.n;

    //     let s_rsa = root::Statement { c_e: c_e_n.clone(), a: a.clone() };

    //     let pi_root =
    //         root::prove(&pp_rsa, &s_rsa, &root::Witness { w, r: r_n.clone(), e: e_n.clone() });

    //     // assert!(
    //     //     root_verifier
    //     //         .method::<_, bool>(
    //     //             "verify",
    //     //             (
    //     //                 [pp_rsa.g.clone(), pp_rsa.h.clone()].to_token(),
    //     //                 a.to_token(),
    //     //                 c_e_n.to_token(),
    //     //                 pi_root.c_r.to_token(),
    //     //                 pi_root.c_w.to_token(),
    //     //                 pi_root.s_e.to_token(),
    //     //                 [pi_root.s_r, pi_root.s_r_2, pi_root.s_r_3].to_token(),
    //     //                 pi_root.s_β.to_token(),
    //     //                 pi_root.s_δ.to_token(),
    //     //                 [pi_root.α_1, pi_root.α_2, pi_root.α_3, pi_root.α_4].to_token(),
    //     //             ),
    //     //         )?
    //     //         .call()
    //     //         .await?
    //     // );

    //     let s_mod_eq = mod_eq::Statement { c_e_n: c_e_n.clone(), c_e_q: c_e_q.into() };

    //     let pi_mod_eq = mod_eq::prove(
    //         &mod_eq::Parameters { pp_pedersen: pp_comm.clone(), pp_rsa: pp_rsa.clone() },
    //         &s_mod_eq,
    //         &mod_eq::Witness { r_n, e: e_n, r_q: Into::<BigUint>::into(o_e).into() },
    //     );

    //     // assert!(
    //     //     mod_eq_verifier
    //     //         .method::<_, bool>(
    //     //             "verify",
    //     //             (
    //     //                 [pp_rsa.g, pp_rsa.h, pp_comm.g.into(), pp_comm.h.into()].to_token(),
    //     //                 [c_e_n.clone(), c_e_q.into()].to_token(),
    //     //                 pi_mod_eq.s_e.to_token(),
    //     //                 pi_mod_eq.s_r_n.to_token(),
    //     //                 pi_mod_eq.s_r_q.to_token(),
    //     //                 [pi_mod_eq.α_1, pi_mod_eq.α_2].to_token(),
    //     //             ),
    //     //         )?
    //     //         .call()
    //     //         .await?
    //     // );

    //     let crs_mint = ProvingKey::<Bn254>::deserialize_unchecked(File::open("./data/mint.crs")?)?;
    //     let s_mint = mint::Statement {
    //         c_e: c_e_q,
    //         extra,
    //         new_pk: new_sk.verifying_key().to_bytes().to_vec(),
    //         new_kk,
    //         new_vv,
    //     };

    //     let pi_mint = create_random_proof(
    //         mint::MintCircuit {
    //             pp: mint::Parameters {
    //                 pp_enc: pp_enc.clone(),
    //                 pp_hash: pp_hash.clone(),
    //                 pp_comm: pp_comm.clone(),
    //             },
    //             s: s_mint.clone(),
    //             w: mint::Witness {
    //                 aux,
    //                 sk: sk.to_bytes().to_vec(),
    //                 new_sk: new_sk.to_bytes().to_vec(),
    //                 k,
    //                 v,
    //                 r_k,
    //                 r_v,
    //                 new_r_k,
    //                 new_r_v,
    //                 r_extra: (r1, r2),
    //                 o_e,
    //             },
    //         },
    //         &crs_mint,
    //         rng,
    //     )?;
    //     // assert_eq!(
    //     //     mint_verifier
    //     //         .method::<_, U256>(
    //     //             "verify",
    //     //             (
    //     //                 [pi_mint.a.x, pi_mint.a.y].to_token(),
    //     //                 [
    //     //                     [pi_mint.b.x.c1, pi_mint.b.x.c0],
    //     //                     [pi_mint.b.y.c1, pi_mint.b.y.c0]
    //     //                 ]
    //     //                 .to_token(),
    //     //                 [pi_mint.c.x, pi_mint.c.y].to_token(),
    //     //                 [
    //     //                     vec![pp_enc.g, pp_comm.g, pp_comm.h],
    //     //                     secp256k1::constraints::PublicKeyVar::to_input(&s_mint.new_pk),
    //     //                     vec![s_mint.new_kk, s_mint.new_vv],
    //     //                     vec![
    //     //                         s_mint.extra.0 .0,
    //     //                         s_mint.extra.0 .1,
    //     //                         s_mint.extra.1 .0,
    //     //                         s_mint.extra.1 .1
    //     //                     ],
    //     //                     vec![s_mint.c_e],
    //     //                 ]
    //     //                 .concat()
    //     //                 .to_token(),
    //     //             ),
    //     //         )?
    //     //         .call()
    //     //         .await?,
    //     //     U256::from(1)
    //     // );

    //     let new_pk = parse_pk(&new_sk.verifying_key().to_bytes());
    //     let new_pk_x = U256::from_big_endian(&new_pk.0.to_bytes_be());
    //     let new_pk_y = U256::from_big_endian(&new_pk.1.to_bytes_be());

    //     assert_eq!(
    //         manager
    //             .method::<_, I256>(
    //                 "mint",
    //                 (
    //                     [new_pk_x, new_pk_y],
    //                     [new_kk, new_vv].to_token(),
    //                     new_aux.to_token(),
    //                     [
    //                         s_mint.extra.0 .0,
    //                         s_mint.extra.0 .1,
    //                         s_mint.extra.1 .0,
    //                         s_mint.extra.1 .1,
    //                     ]
    //                     .to_token(),
    //                     c_e_n.to_token(),
    //                     c_e_q.to_token(),
    //                     (
    //                         (
    //                             pi_root.c_r.to_token(),
    //                             pi_root.c_w.to_token(),
    //                             pi_root.s_e.to_token(),
    //                             [pi_root.s_r, pi_root.s_r_2, pi_root.s_r_3].to_token(),
    //                             pi_root.s_β.to_token(),
    //                             pi_root.s_δ.to_token(),
    //                             [pi_root.α_1, pi_root.α_2, pi_root.α_3, pi_root.α_4].to_token(),
    //                         ),
    //                         (
    //                             pi_mod_eq.s_e.to_token(),
    //                             pi_mod_eq.s_r_n.to_token(),
    //                             pi_mod_eq.s_r_q.to_token(),
    //                             [pi_mod_eq.α_1, pi_mod_eq.α_2].to_token(),
    //                         ),
    //                         (
    //                             [pi_mint.a.x, pi_mint.a.y].to_token(),
    //                             [
    //                                 [pi_mint.b.x.c1, pi_mint.b.x.c0],
    //                                 [pi_mint.b.y.c1, pi_mint.b.y.c0],
    //                             ]
    //                             .to_token(),
    //                             [pi_mint.c.x, pi_mint.c.y].to_token(),
    //                         ),
    //                     ),
    //                 ),
    //             )?
    //             .call()
    //             .await?,
    //         I256::from(0)
    //     );

    //     Ok(())
    // }
}
