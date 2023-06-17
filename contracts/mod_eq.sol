pragma solidity ^0.8;

import "./bn.sol";
import "./pairing.sol";

contract ModEqVerifier {
    using BigNumber for *;
    using Pairing for *;

    uint256 lambda_s;
    BigNumber.instance n;
    BigNumber.instance q;
    BigNumber.instance g;
    BigNumber.instance h;
    uint256[2] gg;
    uint256[2] hh;

    struct Int {
        bytes value;
        bool is_neg;
    }

    constructor(
        bytes memory _n,
        bytes memory _g,
        bytes memory _h,
        uint256[2] memory _gg,
        uint256[2] memory _hh,
        uint256 _lambda_s
    ) {
        lambda_s = _lambda_s;
        n = BigNumber.u(_n);
        q = BigNumber.u(
            hex"30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"
        );
        g = BigNumber.u(_g);
        h = BigNumber.u(_h);
        gg = _gg;
        hh = _hh;
    }

    function challenge(
        bytes memory c_e_n,
        uint256[2] memory c_e_q,
        bytes memory alpha_1,
        uint256[2] memory alpha_2
    ) public view returns (uint256) {
        return
            uint256(
                sha256(
                    bytes.concat(
                        c_e_n,
                        abi.encodePacked(c_e_q[0]),
                        abi.encodePacked(c_e_q[1]),
                        alpha_1,
                        abi.encodePacked(alpha_2[0]),
                        abi.encodePacked(alpha_2[1])
                    )
                )
            ) & ((1 << lambda_s) - 1);
    }

    function verify_1(
        bytes memory c_e_n,
        bytes memory c,
        bytes memory s_e,
        bool neg_s_e,
        bytes memory s_r_n,
        bool neg_s_r_n,
        bytes memory alpha_1
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.u(alpha_1);
        BigNumber.instance memory right = BigNumber.prepare_modexp(
            BigNumber.u(c_e_n),
            BigNumber.u(c),
            n
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            g,
            BigNumber.u(s_e),
            n
        );
        if (neg_s_e) {
            left = BigNumber.modmul(left, x, n);
        } else {
            right = BigNumber.modmul(right, x, n);
        }

        BigNumber.instance memory y = BigNumber.prepare_modexp(
            h,
            BigNumber.u(s_r_n),
            n
        );
        if (neg_s_r_n) {
            left = BigNumber.modmul(left, y, n);
        } else {
            right = BigNumber.modmul(right, y, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_2(
        uint256[2] memory c_e_q,
        uint256 c,
        uint256 s_e,
        uint256 s_r_q,
        uint256[2] memory alpha_2
    ) public view returns (bool) {
        uint256[2] memory r = Pairing.addition(
            Pairing.addition(
                Pairing.scalar_mul(c_e_q, c),
                Pairing.scalar_mul(gg, s_e)
            ),
            Pairing.scalar_mul(hh, s_r_q)
        );

        return r[0] == alpha_2[0] && r[1] == alpha_2[1];
    }

    function verify(
        bytes memory c_e_n,
        uint256[2] memory c_e_q,
        Int memory s_e,
        Int memory s_r_n,
        uint256 s_r_q,
        bytes memory alpha_1,
        uint256[2] memory alpha_2
    ) public view returns (bool) {
        uint256 c = challenge(c_e_n, c_e_q, alpha_1, alpha_2);
        BigNumber.instance memory s_e_q = BigNumber.prepare_modexp(
            BigNumber.u(s_e.value),
            BigNumber.u(
                hex"0000000000000000000000000000000000000000000000000000000000000001"
            ),
            q
        );
        if (s_e.is_neg) {
            s_e_q = BigNumber.prepare_sub(q, s_e_q);
        }
        return
            verify_1(
                c_e_n,
                abi.encodePacked(c),
                s_e.value,
                s_e.is_neg,
                s_r_n.value,
                s_r_n.is_neg,
                alpha_1
            ) &&
            verify_2(c_e_q, c, uint256(bytes32(s_e_q.val)), s_r_q, alpha_2);
    }
}
