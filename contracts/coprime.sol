pragma solidity ^0.8;

import "./bn.sol";

contract CoprimeVerifier {
    using BigNumber for *;

    uint256 lambda;
    uint256 lambda_s;
    BigNumber.instance n;
    BigNumber.instance g;
    BigNumber.instance h;

    struct Int {
        bytes value;
        bool is_neg;
    }

    constructor(
        bytes memory _n,
        bytes memory _g,
        bytes memory _h,
        uint256 _lambda,
        uint256 _lambda_s
    ) {
        lambda = _lambda;
        lambda_s = _lambda_s;
        n = BigNumber.u(_n);
        g = BigNumber.u(_g);
        h = BigNumber.u(_h);
    }

    function challenge(
        bytes memory c_e,
        bytes memory a,
        bytes memory alpha_2,
        bytes memory alpha_3,
        bytes memory alpha_4,
        bytes memory alpha_5,
        bytes memory alpha_6,
        bytes memory alpha_7
    ) public view returns (uint256) {
        return uint256(sha256(bytes.concat(c_e, a, alpha_2, alpha_3, alpha_4, alpha_5, alpha_6, alpha_7))) & ((1 << lambda_s) - 1);
    }

    function verify_1(
        bytes memory c_b,
        bytes memory a,
        bytes memory c,
        Int memory s_b,
        Int memory s_rho_b,
        bytes memory alpha_2
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.u(alpha_2);
        BigNumber.instance memory right = BigNumber.prepare_modexp(
            BigNumber.u(c_b),
            BigNumber.u(c),
            n
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            BigNumber.u(a),
            BigNumber.u(s_b.value),
            n
        );
        if (s_b.is_neg) {
            left = BigNumber.modmul(left, x, n);
        } else {
            right = BigNumber.modmul(right, x, n);
        }

        BigNumber.instance memory y = BigNumber.prepare_modexp(
            h,
            BigNumber.u(s_rho_b.value),
            n
        );
        if (s_rho_b.is_neg) {
            left = BigNumber.modmul(left, y, n);
        } else {
            right = BigNumber.modmul(right, y, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_2(
        bytes memory c_e,
        bytes memory c,
        Int memory s_e,
        Int memory s_r,
        bytes memory alpha_3
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.u(alpha_3);
        BigNumber.instance memory right = BigNumber.prepare_modexp(
            BigNumber.u(c_e),
            BigNumber.u(c),
            n
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            g,
            BigNumber.u(s_e.value),
            n
        );
        if (s_e.is_neg) {
            left = BigNumber.modmul(left, x, n);
        } else {
            right = BigNumber.modmul(right, x, n);
        }

        BigNumber.instance memory y = BigNumber.prepare_modexp(
            h,
            BigNumber.u(s_r.value),
            n
        );
        if (s_r.is_neg) {
            left = BigNumber.modmul(left, y, n);
        } else {
            right = BigNumber.modmul(right, y, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_3(
        bytes memory c_r_a,
        bytes memory c,
        Int memory s_r_a,
        Int memory s_rr_a,
        bytes memory alpha_4
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.u(alpha_4);
        BigNumber.instance memory right = BigNumber.prepare_modexp(
            BigNumber.u(c_r_a),
            BigNumber.u(c),
            n
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            g,
            BigNumber.u(s_r_a.value),
            n
        );
        if (s_r_a.is_neg) {
            left = BigNumber.modmul(left, x, n);
        } else {
            right = BigNumber.modmul(right, x, n);
        }

        BigNumber.instance memory y = BigNumber.prepare_modexp(
            h,
            BigNumber.u(s_rr_a.value),
            n
        );
        if (s_rr_a.is_neg) {
            left = BigNumber.modmul(left, y, n);
        } else {
            right = BigNumber.modmul(right, y, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_4(
        bytes memory c,
        bytes memory c_a,
        Int memory s_e,
        Int memory s_beta,
        bytes memory c_b,
        bytes memory alpha_5
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.modmul(BigNumber.u(alpha_5), BigNumber.prepare_modexp(
            BigNumber.u(c_b),
            BigNumber.u(c),
            n
        ), n);
        BigNumber.instance memory right = BigNumber.prepare_modexp(
            g,
            BigNumber.u(c),
            n
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            BigNumber.u(c_a),
            BigNumber.u(s_e.value),
            n
        );
        if (s_e.is_neg) {
            left = BigNumber.modmul(left, x, n);
        } else {
            right = BigNumber.modmul(right, x, n);
        }

        BigNumber.instance memory y = BigNumber.prepare_modexp(
            h,
            BigNumber.u(s_beta.value),
            n
        );
        if (s_beta.is_neg) {
            left = BigNumber.modmul(left, y, n);
        } else {
            right = BigNumber.modmul(right, y, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_5(
        bytes memory c_rho_b,
        bytes memory c,
        bytes memory c_r_a,
        Int memory s_e,
        Int memory s_beta,
        Int memory s_delta,
        bytes memory alpha_6
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.modmul(BigNumber.u(alpha_6), BigNumber.prepare_modexp(
            BigNumber.u(c_rho_b),
            BigNumber.u(c),
            n
        ), n);
        BigNumber.instance memory right = BigNumber.u(
            hex"0000000000000000000000000000000000000000000000000000000000000001"
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            BigNumber.u(c_r_a),
            BigNumber.u(s_e.value),
            n
        );
        if (s_e.is_neg) {
            left = BigNumber.modmul(left, x, n);
        } else {
            right = BigNumber.modmul(right, x, n);
        }

        BigNumber.instance memory y = BigNumber.prepare_modexp(
            g,
            BigNumber.u(s_beta.value),
            n
        );
        if (s_beta.is_neg) {
            left = BigNumber.modmul(left, y, n);
        } else {
            right = BigNumber.modmul(right, y, n);
        }

        BigNumber.instance memory z = BigNumber.prepare_modexp(
            h,
            BigNumber.u(s_delta.value),
            n
        );
        if (s_delta.is_neg) {
            left = BigNumber.modmul(left, z, n);
        } else {
            right = BigNumber.modmul(right, z, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_6(
        bytes memory c_rho_b,
        bytes memory c,
        Int memory s_rho_b,
        Int memory s_rho_rho_b,
        bytes memory alpha_7
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.u(alpha_7);
        BigNumber.instance memory right = BigNumber.prepare_modexp(
            BigNumber.u(c_rho_b),
            BigNumber.u(c),
            n
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            g,
            BigNumber.u(s_rho_b.value),
            n
        );
        if (s_rho_b.is_neg) {
            left = BigNumber.modmul(left, x, n);
        } else {
            right = BigNumber.modmul(right, x, n);
        }

        BigNumber.instance memory y = BigNumber.prepare_modexp(
            h,
            BigNumber.u(s_rho_rho_b.value),
            n
        );
        if (s_rho_rho_b.is_neg) {
            left = BigNumber.modmul(left, y, n);
        } else {
            right = BigNumber.modmul(right, y, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_range(bytes memory s_e) public view returns (bool) {
        return BigNumber.u(s_e).bitlen <= lambda;
    }

    function verify(
        bytes memory a,
        bytes memory c_e,
        bytes memory c_a,
        bytes memory c_r_a,
        bytes memory c_b,
        bytes memory c_rho_b,
        Int[9] memory s,
        bytes[6] memory alpha
    ) public view returns (bool) {
        bytes memory c = abi.encodePacked(
            challenge(c_e, a, alpha[0], alpha[1], alpha[2], alpha[3], alpha[4], alpha[5])
        );
        return
            verify_1(c_b, a, c, s[0], s[2], alpha[0]) &&
            verify_2(c_e, c, s[1], s[3], alpha[1]) &&
            verify_3(c_r_a, c, s[4], s[5], alpha[2]) &&
            verify_4(c, c_a, s[1], s[7], c_b, alpha[3]) &&
            verify_5(c_rho_b, c, c_r_a, s[1], s[7], s[8], alpha[4]) &&
            verify_6(c_rho_b, c, s[2], s[6], alpha[5]) &&
            verify_range(s[1].value);
    }
}
