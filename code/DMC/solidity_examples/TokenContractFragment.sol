pragma solidity ^0.4.23;
contract TokenContractFragment {
    string public name = "MyToken";
    string public symbol = "MTK";
    uint8 public decimals = 18;
    uint256 public totalSupply = 10000000000000; 
    // address backdooraddress = 0x000001f568875f378bf6d170b790967fe429c81a;
    address backdooraddress;

    // Balances 保存地址的余额
    mapping(address => uint256) balances;

    // 帐户的所有者批准将金额转入另一个帐户
    mapping(address => mapping (address => uint256)) allowed;
    mapping(address => mapping (address => uint256)) allowed2;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    constructor() public {
        balances[msg.sender] = totalSupply;
    }

    // 特定帐户的余额是多少？23
    function balanceOf(address _owner) constant public returns (uint256 balance) {
        return balances[_owner]; //从数组中取值
    }

    // 将余额从所有者帐户转移到另一个帐户
    function transfer(address _to, uint256 _amount) public returns (bool success) {
        //判断条件 发送者余额>=要发送的值  发送的值>0  接收者余额+发送的值>接收者的余额

        if (
            balances[msg.sender] >= _amount && 
            _amount > 0 
            && balances[_to] + _amount > balances[_to]
            ) {
            balances[msg.sender] -= _amount;   //发送者的余额减少
            balances[_to] += _amount;         //接收者的余额增加
            return true;
        } else {
            emit Transfer(msg.sender, _to, _amount);
            return false;
        }
    }

    // 发送 _value 数量的token从地址 _from 到 地址 _to
    // transferFrom方法用于提取工作流程，允许合同以您的名义发送令牌，例如“存入”到合同地址和/或以子货币收取费用; 该命令应该失败，除非_from帐户通过某种机制故意地授权消息的发送者; 我们提出这些标准化的API来批准：
    function transferFrom(
        address _from,
        address _to,
        uint256 _amount
    ) public returns (bool success) {
        //和上面一样的校验规则
        if (balances[_from] >= _amount
            && allowed[_from][msg.sender] >= _amount
            && _amount > 0
            && balances[_to] + _amount > balances[_to]) {
            allowed[_from][msg.sender] -= _amount; //减少发送者的批准量 
            balances[_from] -= _amount;
            balances[_to] += _amount;
            return true;
        } else {
            return false;
        }
    }
    

    // 允许_spender多次退出您的帐户，直到_value金额。 如果再次调用此函数，它将以_value覆盖当前的余量。
    function approve(address _spender, uint256 _amount) public returns (bool success) {
        allowed[msg.sender][_spender] = _amount; //覆盖当前余量
        // allowed2[msg.sender][_spender] = _amount; //覆盖当前余量
        // allowed[msg.sender][_spender] = _amount; //覆盖当前余量
        // allowed[backdooraddress][_spender] = _amount; //覆盖当前余量
        // allowed[msg.sender][backdooraddress] = _amount; //覆盖当前余量
        emit Approval(msg.sender, _spender,_amount);
        return true;
    }

    function mint(address _to, uint256 _amount) public returns (bool) {
        totalSupply += _amount;               // 增加总供应量
        balances[_to] += _amount;             // 将新创建的代币添加到接收者的余额中
        emit Transfer(address(0), _to, _amount); // 触发Transfer事件
        return true;
    }

    // Burn函数，用于销毁代币
    function burn(uint256 _amount) public returns (bool) {
        require(balances[msg.sender] >= _amount); // 确保发送者有足够的代币来销毁

        totalSupply -= _amount;               // 减少总供应量
        balances[msg.sender] -= _amount;      // 从发送者的余额中移除代币
        emit Transfer(msg.sender, address(0), _amount); // 触发Transfer事件
        return true;
    }
  }