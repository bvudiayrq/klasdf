// SPDX-License-Identifier: MIT
// 测试分支
pragma solidity ^0.8.0;

contract TestContract {
    // uint256 private value1;
    // uint256 private value2;
    // uint256 private value3;
    // balance
    mapping(address => uint256) public balances;

    

    constructor() {

        balances[msg.sender] = 1;
        
    }

    function approve(uint8 condition,uint256 v2) public {
        balances[msg.sender] = 2;

        if (condition == 1) {
            balances[msg.sender] = balances[msg.sender];
        } else {
            balances[msg.sender] += v2;
        } 
    }
}