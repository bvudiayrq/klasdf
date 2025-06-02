pragma solidity ^0.4.21;

contract SimpleERC1155 {
    // Mapping from token ID to owner balances
    mapping (uint256 => mapping(address => uint256)) private _balances;

    // Mapping from owner to operator approvals
    mapping (address => mapping(address => bool)) private _operatorApprovals;

    event TransferSingle(address indexed from, address indexed to, uint256 indexed id, uint256 value);
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);

    constructor() public {}

    function balanceOf(address owner, uint256 id) public view returns (uint256) {
        require(owner != address(0), "ERC1155: balance query for the zero address");
        return _balances[id][owner];
    }

    function setApprovalForAll(address operator, bool approved) public {
        _operatorApprovals[msg.sender][operator] = approved;
        emit ApprovalForAll(msg.sender, operator, approved);
    }

    function isApprovedForAll(address owner, address operator) public view returns (bool) {
        return _operatorApprovals[owner][operator];
    }

    function safeTransferFrom(address from, address to, uint256 id, uint256 amount) public {
        require(to != address(0), "ERC1155: transfer to the zero address");
        require(_balances[id][from] >= amount, "ERC1155: insufficient balance for transfer");
        require(from == msg.sender || isApprovedForAll(from, msg.sender), "ERC1155: transfer caller is not owner nor approved");

        _balances[id][from] -= amount;
        _balances[id][to] += amount;

        emit TransferSingle(from, to, id, amount);
    }

    function mint(address to, uint256 id, uint256 amount) public {
        require(to != address(0), "ERC1155: mint to the zero address");

        _balances[id][to] += amount;

        emit TransferSingle(address(0), to, id, amount);
    }
}