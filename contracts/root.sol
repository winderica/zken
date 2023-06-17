pragma solidity ^0.8;

import "./bn.sol";

contract RootVerifier {
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
        bytes memory alpha_1,
        bytes memory alpha_2,
        bytes memory alpha_3,
        bytes memory alpha_4
    ) public view returns (uint256) {
        return uint256(sha256(bytes.concat(c_e, a, alpha_1, alpha_2, alpha_3, alpha_4))) & ((1 << lambda_s) - 1);
    }

    function verify_1(
        bytes memory c_e,
        bytes memory c,
        bytes memory s_e,
        bool neg_s_e,
        bytes memory s_r,
        bool neg_s_r,
        bytes memory alpha_1
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.u(alpha_1);
        BigNumber.instance memory right = BigNumber.prepare_modexp(
            BigNumber.u(c_e),
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
            BigNumber.u(s_r),
            n
        );
        if (neg_s_r) {
            left = BigNumber.modmul(left, y, n);
        } else {
            right = BigNumber.modmul(right, y, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_2(
        bytes memory c_r,
        bytes memory c,
        bytes memory s_r_2,
        bool neg_s_r_2,
        bytes memory s_r_3,
        bool neg_s_r_3,
        bytes memory alpha_2
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.u(alpha_2);
        BigNumber.instance memory right = BigNumber.prepare_modexp(
            BigNumber.u(c_r),
            BigNumber.u(c),
            n
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            g,
            BigNumber.u(s_r_2),
            n
        );
        if (neg_s_r_2) {
            left = BigNumber.modmul(left, x, n);
        } else {
            right = BigNumber.modmul(right, x, n);
        }

        BigNumber.instance memory y = BigNumber.prepare_modexp(
            h,
            BigNumber.u(s_r_3),
            n
        );
        if (neg_s_r_3) {
            left = BigNumber.modmul(left, y, n);
        } else {
            right = BigNumber.modmul(right, y, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_3(
        bytes memory a,
        bytes memory c_w,
        bytes memory c,
        bytes memory s_e,
        bool neg_s_e,
        bytes memory s_beta,
        bool neg_s_beta,
        bytes memory alpha_3
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.u(alpha_3);
        BigNumber.instance memory right = BigNumber.prepare_modexp(
            BigNumber.u(a),
            BigNumber.u(c),
            n
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            BigNumber.u(c_w),
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
            BigNumber.u(s_beta),
            n
        );
        if (neg_s_beta) {
            right = BigNumber.modmul(right, y, n);
        } else {
            left = BigNumber.modmul(left, y, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_4(
        bytes memory c_r,
        bytes memory s_e,
        bool neg_s_e,
        bytes memory s_beta,
        bool neg_s_beta,
        bytes memory s_delta,
        bool neg_s_delta,
        bytes memory alpha_4
    ) public view returns (bool) {
        BigNumber.instance memory left = BigNumber.u(alpha_4);
        BigNumber.instance memory right = BigNumber.u(
            hex"0000000000000000000000000000000000000000000000000000000000000001"
        );

        BigNumber.instance memory x = BigNumber.prepare_modexp(
            BigNumber.u(c_r),
            BigNumber.u(s_e),
            n
        );
        if (neg_s_e) {
            left = BigNumber.modmul(left, x, n);
        } else {
            right = BigNumber.modmul(right, x, n);
        }

        BigNumber.instance memory y = BigNumber.prepare_modexp(
            g,
            BigNumber.u(s_beta),
            n
        );
        if (neg_s_beta) {
            right = BigNumber.modmul(right, y, n);
        } else {
            left = BigNumber.modmul(left, y, n);
        }

        BigNumber.instance memory z = BigNumber.prepare_modexp(
            h,
            BigNumber.u(s_delta),
            n
        );
        if (neg_s_delta) {
            right = BigNumber.modmul(right, z, n);
        } else {
            left = BigNumber.modmul(left, z, n);
        }

        return BigNumber.cmp(left, right, false) == 0;
    }

    function verify_range(bytes memory s_e) public view returns (bool) {
        return BigNumber.u(s_e).bitlen <= lambda;
    }

    function verify(
        bytes memory a,
        bytes memory c_e,
        bytes memory c_r,
        bytes memory c_w,
        Int memory s_e,
        Int[3] memory s_r,
        Int memory s_beta,
        Int memory s_delta,
        bytes[4] memory alpha
    ) public view returns (bool) {
        bytes memory c = abi.encodePacked(
            challenge(c_e, a, alpha[0], alpha[1], alpha[2], alpha[3])
        );
        return
            verify_1(
                c_e,
                c,
                s_e.value,
                s_e.is_neg,
                s_r[0].value,
                s_r[0].is_neg,
                alpha[0]
            ) &&
            verify_2(
                c_r,
                c,
                s_r[1].value,
                s_r[1].is_neg,
                s_r[2].value,
                s_r[2].is_neg,
                alpha[1]
            ) &&
            verify_3(
                a,
                c_w,
                c,
                s_e.value,
                s_e.is_neg,
                s_beta.value,
                s_beta.is_neg,
                alpha[2]
            ) &&
            verify_4(
                c_r,
                s_e.value,
                s_e.is_neg,
                s_beta.value,
                s_beta.is_neg,
                s_delta.value,
                s_delta.is_neg,
                alpha[3]
            ) &&
            verify_range(s_e.value);
    }
}
