pragma solidity ^0.8;

library Pairing {
    uint256 constant q =
        21888242871839275222246405745257275088696311157297823662689037894645226208583;

    function negate(uint256[2] memory p)
        internal
        pure
        returns (uint256[2] memory r)
    {
        if (p[0] == 0 && p[1] == 0) return p;
        return [p[0], q - p[1]];
    }

    function addition(uint256[2] memory p1, uint256[2] memory p2)
        internal
        view
        returns (uint256[2] memory r)
    {
        uint256[4] memory input = [p1[0], p1[1], p2[0], p2[1]];
        bool success;
        assembly {
            success := staticcall(sub(gas(), 2000), 6, input, 0xc0, r, 0x60)
            // Use "invalid" to make gas estimation work
            switch success
            case 0 {
                invalid()
            }
        }
        require(success, "pairing-add-failed");
    }

    function scalar_mul(uint256[2] memory p, uint256 s)
        internal
        view
        returns (uint256[2] memory r)
    {
        uint256[3] memory input = [p[0], p[1], s];
        bool success;
        assembly {
            success := staticcall(sub(gas(), 2000), 7, input, 0x80, r, 0x60)
            // Use "invalid" to make gas estimation work
            switch success
            case 0 {
                invalid()
            }
        }
        require(success, "pairing-mul-failed");
    }

    /// @return the result of computing the pairing check
    /// e(p1[0], p2[0]) *  .... * e(p1[n], p2[n]) == 1
    /// For example pairing([P1(), P1().negate()], [P2(), P2()]) should
    /// return true.
    function pairing(uint256[2][] memory p1, uint256[2][2][] memory p2)
        internal
        view
        returns (uint256)
    {
        require(p1.length == p2.length, "pairing-lengths-failed");
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
            // Use "invalid" to make gas estimation work
            switch success
            case 0 {
                invalid()
            }
        }
        require(success, "pairing-opcode-failed");
        return out[0];
    }
}
