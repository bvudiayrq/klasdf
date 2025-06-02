// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract LoopExample {
    uint256 private count;
    uint256 private count2;

    // 使用for循环来累加
    // function approve(uint256 _times) public {
    //     for (uint256 i = 0; i < _times; i++) {
    //         count += 1;
    //     }
    // }
    
    function transfer() public {
        while (true) {
            // 死循环，没有退出条件
            count2+=1;
            if (count2 > 10) {
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=1;
                count +=2;
            }
        }
    }
}