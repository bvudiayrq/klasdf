pragma solidity ^0.4.23;

contract CompleteERC721 {

    mapping(address => uint256) private _balances;
    mapping(uint256 => address) private _tokenOwners;
    mapping(uint256 => address) private _tokenApprovals;
    mapping (address => mapping (address => bool)) private _operatorApprovals;

    uint256 private _totalSupply;
    uint256 otherTokenId;

    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);
    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);

    function balanceOf(address owner) public view returns (uint256) {
        require(owner != address(0));
        return _balances[owner];
    }

    function ownerOf(uint256 tokenId) public view returns (address) {
        address owner = _tokenOwners[tokenId];
        require(owner != address(0));
        return owner;
    }

    function approve(address to, uint256 tokenId) public {
        require(to != address(0), "ERC721: approval to the zero address");
        require(ownerOf(tokenId) == msg.sender || isApprovedForAll(ownerOf(tokenId), msg.sender), "ERC721: approve caller is not owner nor approved for all");
        address owner = ownerOf(tokenId);
        require(to != owner);
        _tokenApprovals[tokenId] = to;


        emit Approval(owner, to, tokenId);
    }

    function getApproved(uint256 tokenId) public view returns (address) {
        return _tokenApprovals[tokenId];
    }

    function setApprovalForAll(address operator, bool approved) public {
        require(operator != msg.sender);
        _operatorApprovals[msg.sender][operator] = approved;
        emit ApprovalForAll(msg.sender, operator, approved);
    }

    function transferFrom(address from, address to, uint256 tokenId) public {
        // 检查 'to' 地址是否有效
        require(to != address(0), "ERC721: transfer to the zero address");

        // 检查 'from' 是否是token的所有者，或者调用者是否被 'from' 授权
        require(_tokenOwners[tokenId] == from, "ERC721: transfer of token that is not own");
        require(msg.sender == from || _tokenApprovals[tokenId] == msg.sender, "ERC721: transfer caller is not owner nor approved");

        // 更新token的所有者和各个地址的余额
        _balances[from] -= 1;
        _balances[to] += 1;
        _tokenOwners[tokenId] = to;

        // // 清除授权（如果存在）
        // if (_tokenApprovals[tokenId] != address(0)) {
        //     delete _tokenApprovals[tokenId];
        // }

        // 触发 'Transfer' 事件
        emit Transfer(from, to, tokenId);
    }
    

    function mint(address to, uint256 tokenId) public {
        require(to != address(0), "ERC721: mint to the zero address");
        require(_tokenOwners[tokenId] == address(0), "ERC721: token already minted");
        
        _balances[to] += 1;
        _tokenOwners[tokenId] = to;
        emit Transfer(address(0), to, tokenId);
    }

    function burn(uint256 tokenId) public {
        address owner = ownerOf(tokenId);
        _balances[owner] -= 1;
        delete _tokenOwners[tokenId];
        emit Transfer(owner, address(0), tokenId);
    }

    function isApprovedForAll(address owner, address operator) public view returns (bool) {
        return _operatorApprovals[owner][operator];
    }

}