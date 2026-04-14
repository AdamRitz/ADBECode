pragma solidity ^0.8.20;

contract Verify {
    uint256 constant q =
        0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;
    uint256 constant q1 =
        0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000;
    bytes constant g1 =
        hex"0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1";
    bytes constant g2 =
        hex"00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be";
    bytes public lastg=g1;
    
    function Check(
        bytes[] calldata g1s,
        bytes[] calldata g2s,
        bytes calldata gtau
    ) public  returns (bool) {
        uint256 L1 = g1s.length;
        uint256 L2 = g2s.length;
        require(L1 * 2 == L2);
        // Compute 4 Part
        uint256 rho1 = uint256(keccak256(abi.encode(g1s, g2s, 0))) % q;
        uint256 rho2 = uint256(keccak256(abi.encode(g1s, g2s, 1))) % q;
        uint256 temp1 = 1;
        uint256 temp2 = 1;
        uint256 k = 0;
        bytes memory ag1 = new bytes(L1 * 160);
        bytes memory ag2 = new bytes((L2 - 3) * 288);
        bytes memory ag3 = new bytes((L1 - 1) * 160);
        bytes memory ag4 = new bytes((L2 - 2) * 288); //长度还需要再考虑
        //
        // Compute Part 1
        //
        k = 0;
        for (uint256 i = 0; i <= L1 - 1; i++) {
            require(g1s[i].length == 128, "bad G1 len");
            CopyBytes(g1s[i], 0, ag1, k, 128);
            k+=128;
            CopyUint(temp1, ag1, k);
            k+=32;
            temp1 = mulmod(temp1, rho1, q);
        }
        bytes memory part1 = G1Muls(ag1);
        //
        // Compute Part 2
        //
        k = 0;
        temp2 = rho2;
        for (uint256 i = 0; i <= 2 * L1 - 1 - 1; i++) {
            // 实际是数组里面的 L+1 和 L
            if (i == L1 - 1 || i == L1) {
                temp2 = mulmod(temp2, rho2, q);
                continue;
            }
            CopyBytes(g2s[i], 0, ag2, k, 256);
            k+=256;
            CopyUint(temp2, ag2, k);
            k+=32;
            temp2 = mulmod(temp2, rho2, q);
        }
        bytes memory part2 = G2Muls(ag2);
        part2 = G2Add(g2, part2);
        //
        // Compute Part 3
        //
        k = 0;
        temp1 = rho1;
        for (uint256 i = 0; i <= L1 - 1 - 1; i++) {
            CopyBytes(g1s[i],0,ag3,k,128);
            k+=128;
            CopyUint(temp1,ag3 , k);
            k+=32;
            temp1 = mulmod(temp1, rho1, q);
        }
        bytes memory part3 = G1Muls(ag3);
        part3 = G1Add(g1, part3);
        //
        // Compute Part 4
        //

        k = 0;
        temp2 = 1;
        for (uint256 i = 0; i <= 2 * L1 - 1; i++) {
            if (i == L1 || i == L1 + 1) {
                //排除第 L+1  和 L+2
                temp2 = mulmod(temp2, rho2, q);
                continue;
            }
            CopyBytes(g2s[i],0,ag4,k,256);
            k+=256;
            CopyUint(temp2, ag4, k);
            k+=32;
            temp2 = mulmod(temp2, rho2, q);
        }
        bytes memory part4 = G2Muls(ag4);
    require(EqualPairingCheck(g1s[0],g2,lastg , gtau),"Check1 Failed");
    require(EqualPairingCheck(part1, part2, part3, part4),"Check2-1 Failed");
    require(EqualPairingCheck(g1,g2s[L1+1],g1s[1],g2s[L1-1]),"Check2-2 Failed");
    require(ZeroCheck(g1s[0])!=true,"Check3 Failed");
    lastg=g1s[0];
    return true;
    }

    function CheckTest(bytes[] calldata g1s,
        bytes[] calldata g2s,
        bytes calldata pi1,
        uint256 pi2
    ) public  returns (bool) {
        uint256 L1 = g1s.length;
        uint256 L2 = g2s.length;
        require(L1 * 2 == L2);
        // Compute 4 Part
        uint256 rho1 = uint256(keccak256(abi.encode(g1s, g2s, 0))) % q;
        uint256 rho2 = uint256(keccak256(abi.encode(g1s, g2s, 1))) % q;
        uint256 temp1 = 1;
        uint256 temp2 = 1;
        uint256 k = 0;
        bytes memory ag1 = new bytes(L1 * 160);
        bytes memory ag2 = new bytes((L2 - 3) * 288);
        bytes memory ag3 = new bytes((L1 - 1) * 160);
        bytes memory ag4 = new bytes((L2 - 2) * 288); //长度还需要再考虑
        //
        // Compute Part 1
        //
        k = 0;
        for (uint256 i = 0; i <= L1 - 1; i++) {
            require(g1s[i].length == 128, "bad G1 len");
            CopyBytes(g1s[i], 0, ag1, k, 128);
            k+=128;
            CopyUint(temp1, ag1, k);
            k+=32;
            temp1 = mulmod(temp1, rho1, q);
        }
        bytes memory part1 = G1Muls(ag1);
        //
        // Compute Part 2
        //
        k = 0;
        temp2 = rho2;
        for (uint256 i = 0; i <= 2 * L1 - 1 - 1; i++) {
            // 实际是数组里面的 L+1 和 L
            if (i == L1 - 1 || i == L1) {
                temp2 = mulmod(temp2, rho2, q);
                continue;
            }
            CopyBytes(g2s[i], 0, ag2, k, 256);
            k+=256;
            CopyUint(temp2, ag2, k);
            k+=32;
            temp2 = mulmod(temp2, rho2, q);
        }
        bytes memory part2 = G2Muls(ag2);
        part2 = G2Add(g2, part2);
        //
        // Compute Part 3
        //
        k = 0;
        temp1 = rho1;
        for (uint256 i = 0; i <= L1 - 1 - 1; i++) {
            CopyBytes(g1s[i],0,ag3,k,128);
            k+=128;
            CopyUint(temp1,ag3 , k);
            k+=32;
            temp1 = mulmod(temp1, rho1, q);
        }
        bytes memory part3 = G1Muls(ag3);
        part3 = G1Add(g1, part3);
        //
        // Compute Part 4
        //

        k = 0;
        temp2 = 1;
        for (uint256 i = 0; i <= 2 * L1 - 1; i++) {
            if (i == L1 || i == L1 + 1) {
                //排除第 L+1  和 L+2
                temp2 = mulmod(temp2, rho2, q);
                continue;
            }
            CopyBytes(g2s[i],0,ag4,k,256);
            k+=256;
            CopyUint(temp2, ag4, k);
            k+=32;
            temp2 = mulmod(temp2, rho2, q);
        }
        bytes memory part4 = G2Muls(ag4);
    //require(EqualPairingCheck(g1s[0],g2,lastg , gtau),"Check1 Failed");
    require(EqualPairingCheck(part1, part2, part3, part4),"Check2-1 Failed");
    require(EqualPairingCheck(g1,g2s[L1+1],g1s[1],g2s[L1-1]),"Check2-2 Failed");
    require(ZeroCheck(g1s[0])!=true,"Check3 Failed");
    lastg=g1s[0];
    uint256 w=uint256(keccak256(abi.encode(g1s,g2s)))%q;
    bytes memory p1=G1Mul(g1s[0], w);
    bytes memory p2=G1Add(p1, pi1);
        for (uint256 i = 0; i < 128; i++) {
        if (p2[i] != pi1[i]) return false;
    }
    return true;
}
bool public  w=false;
bytes[] public ppg1s;
bytes[] public ppg2s;
// ---- helpers: 只做 copy 和写标量，不改你 precompile 包装函数 ----
function SetPP(bytes[] calldata g1s,bytes[] calldata g2s)public {
    for(uint256 i=0;i<=g1s.length-1;i++){
        ppg1s.push(g1s[i]);
    }
    for(uint256 i=0;i<=g2s.length-1;i++){
        ppg2s.push(g2s[i]);
    }
}
function CheckKey(bytes calldata g1s,bytes[] calldata g2s,uint256 index)public  returns(bool){
        uint256 L = g2s.length;
        uint256 rho = uint256(keccak256(abi.encode(g1s, g2s))) % q;
        bytes memory left = new bytes(288*(L-1));
        bytes memory right = new bytes(288*(L-1));
        uint256 temp1 = rho;
        uint256 temp2 = rho;
        uint256 k = 0;
        // Compute Left Part
        for(uint256 i=0;i<=L-1;i++){
            if(i==L-index){ //原本是    L+1-index，但是索引需要减去 1
                temp1=mulmod(temp1, rho, q);
                continue;
                
            }
            CopyBytes(g2s[i], 0, left, k, 256);
            k+=256;
            CopyUint(temp1, left, k);
            k+=32;
            temp1=mulmod(temp1, rho, q);
        }
        // Compute Right Part
        k=0;
        for(uint256 i=0;i<=L-1;i++){
            if(i==L-index){
                temp2=mulmod(temp2, rho, q);
                continue;
            }
            bytes memory p = ppg2s[i];
            CopyStorageBytes256(ppg2s[i], right, k); 

            k+=256;
            CopyUint(temp2, right, k);
            k+=32;
            temp2=mulmod(temp2, rho, q);
        }
    bytes memory leftAgg  = G2Muls(left);   // 256 bytes
    bytes memory rightAgg = G2Muls(right);  // 256 bytes
    require(EqualPairingCheck(g1, leftAgg, g1s, rightAgg),"CheckKey Fail");
    return true;
}
function CheckKeyDBE(bytes calldata g1s,bytes[] calldata g2s,uint256 index)public  returns (bool){
    uint256 L=g2s.length;
    for (uint256 i=0;i<=L-2;i++){
        if(i==L-index){
            continue;
        }
        require(EqualPairingCheck(ppg1s[L-i-1-1], g2s[i], g1s, ppg2s[L-1]),"KeyCheck1 Failed");
    }
    if(index==1){
        return true;
    }
   require(EqualPairingCheck(g1, g2s[L-1], g1s, ppg2s[L-1]),"KeyCheck2 Failed" );
    return true;
}
function CopyStorageBytes256(bytes storage s, bytes memory to, uint256 toOff) internal view {
    assembly {
        let slot := s.slot
        let v := sload(slot)

        // require long-form + len==256
        if iszero(and(v, 1)) { revert(0, 0) }
        if iszero(eq(shr(1, sub(v, 1)), 256)) { revert(0, 0) }

        mstore(0x00, slot)
        let base := keccak256(0x00, 0x20)
        let dst := add(add(to, 32), toOff)

        // 8 words
        mstore(dst,             sload(base))
        mstore(add(dst, 32),    sload(add(base, 1)))
        mstore(add(dst, 64),    sload(add(base, 2)))
        mstore(add(dst, 96),    sload(add(base, 3)))
        mstore(add(dst, 128),   sload(add(base, 4)))
        mstore(add(dst, 160),   sload(add(base, 5)))
        mstore(add(dst, 192),   sload(add(base, 6)))
        mstore(add(dst, 224),   sload(add(base, 7)))
    }
}
event Message(bytes);
function SendMessage(bytes calldata a)public {
    emit Message(a);
}
function CopyBytes(bytes calldata from,uint256 fromOff,bytes memory to,uint256 toOff,uint256 len) internal pure{
    assembly{
        calldatacopy(add(add(to,32),toOff),add(from.offset,fromOff),len)
    }
}
function CopyUint(uint256 i,bytes memory to,uint256 toOff)internal pure{
    assembly {
        mstore(add(add(to,32),toOff),i)
    }
}
    //
    // Group Operation Section
    //
    function G1Add(
        bytes memory p1,
        bytes memory p2
    ) public view returns (bytes memory point) {
        bytes memory input = abi.encodePacked(p1, p2);
        (bool ok, bytes memory ret) = address(0x0b).staticcall(input);
        return ret;
    }
    function G1Mul(
        bytes memory p1,
        uint256 scalar
    ) public view returns (bytes memory point) {
        bytes memory input = abi.encodePacked(p1, scalar);
        (bool ok, bytes memory ret) = address(0x0c).staticcall(input);
        return ret;
    }
    function G1Muls(bytes memory d) public view returns (bytes memory point) {
        (bool ok, bytes memory ret) = address(0x0c).staticcall(d);
        return ret;
    }
    // G2s Section
    function G2Add(
        bytes memory p1,
        bytes memory p2
    ) public view returns (bytes memory point) {
        bytes memory input = abi.encodePacked(p1, p2);
        (bool ok, bytes memory ret) = address(0x0d).staticcall(input);
        return ret;
    }
    function G2Mul(
        bytes calldata p1,
        uint256 scalar
    ) public view returns (bytes memory point) {
        bytes memory input = abi.encodePacked(p1, scalar);
        (bool ok, bytes memory ret) = address(0x0e).staticcall(input);
        return ret;
    }
    function G2Muls(bytes memory d) public view returns (bytes memory point) {
        (bool ok, bytes memory ret) = address(0x0e).staticcall(d);
        return ret;
    }
    // Pairings Section
    function Pairing(
        bytes memory p1,
        bytes memory p2,
        bytes memory p3,
        bytes memory p4
    ) public view returns (bool) {
        bytes memory input = abi.encodePacked(p1, p2, p3, p4);
        (bool ok, bytes memory ret) = address(0x0f).staticcall(input);
        return uint256(bytes32(ret)) == 1;
    }
    function EqualPairingCheck(
        bytes memory p1,
        bytes memory p2,
        bytes memory p3,
        bytes memory p4
    ) public view returns (bool) {
        bytes memory negP3 = G1Mul(p3, q1);
        bytes memory input = abi.encodePacked(p1, p2, negP3, p4);
        (bool ok, bytes memory ret) = address(0x0f).staticcall(input);
        return uint256(bytes32(ret)) == 1;
    }


    function ZeroCheck(bytes calldata x)public pure returns (bool ok){
        uint256 acc=0;
        assembly{
            let p:=x.offset
            acc:= or(acc,calldataload(p))
            acc:= or(acc,calldataload(add(p,32)))
            acc:= or(acc,calldataload(add(p,64)))
            acc:= or(acc,calldataload(add(p,96)))
        }
        return acc==0;
    }



}
