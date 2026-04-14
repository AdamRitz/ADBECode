// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

library BLS12381G2 {
    // G1s Section
    function G1Add(bytes calldata p1,bytes calldata p2)public view returns (bytes memory point){
        bytes memory input = abi.encodePacked(p1, p2);
        (bool ok, bytes memory ret) = address(0x0b).staticcall(input);
        return ret;
    }
    function G1Mul(bytes calldata p1,uint256 scalar)public view returns (bytes memory point){
        bytes memory input = abi.encodePacked(p1, scalar);
        (bool ok, bytes memory ret) = address(0x0c).staticcall(input);
        return ret;
    }
    function G1Muls(bytes calldata d)public view returns (bytes memory point){
        (bool ok, bytes memory ret) = address(0x0c).staticcall(d);
        return ret;
    }
    // G2s Section
    function G2Add(bytes calldata p1,bytes calldata p2)public view returns (bytes memory point){
        bytes memory input = abi.encodePacked(p1, p2);
        (bool ok, bytes memory ret) = address(0x0d).staticcall(input);
        return ret;
    }
    function G2Mul(bytes calldata p1,uint256 scalar) public view returns(bytes memory point){
        bytes memory input = abi.encodePacked(p1, scalar);
        (bool ok, bytes memory ret) = address(0x0e).staticcall(input);
        return ret;
    }
    function G2Muls(bytes calldata d)public view returns (bytes memory point){
        (bool ok, bytes memory ret) = address(0x0e).staticcall(d);
        return ret;
    }
    // Pairings Section
    function Pairing(bytes calldata p1,bytes calldata p2,bytes calldata p3,bytes calldata p4)public view returns (bool){
        bytes memory input = abi.encodePacked(p1,p2,p3,p4);
        (bool ok, bytes memory ret) = address(0x0f).staticcall(input);
        return uint256(bytes32(ret)) == 1;
    }

}

