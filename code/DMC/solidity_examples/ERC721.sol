// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract ERC721 {

  // 存储所有NFT的元数据
  mapping(uint256 => string) private _tokenURIs;

  // 存储每个NFT的所有者
  mapping(uint256 => address) private _owners;

  // 存储每个账户拥有的NFT数量
  mapping(address => uint256) private _balances;

  // 存储所有NFT的总数
  uint256 private _totalSupply;

  // 事件：NFT铸造
  event Mint(address indexed to, uint256 indexed tokenId);

  // 事件：NFT转移
  event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);

  // State variables to store contract name and symbol
  string private _name;
  string private _symbol;

  // 构造函数
  constructor() {
    // 初始化合约名称和符号
    _name = "My NFT";
    _symbol = "NFT";
  }

  // 获取合约名称
  function name() public view returns (string memory) {
    return _name;
  }

  // 获取合约符号
  function symbol() public view returns (string memory) {
    return _symbol;
  }

  // 获取NFT总数
  function totalSupply() public view returns (uint256) {
    return _totalSupply;
  }

  // 获取NFT的URI
  function tokenURI(uint256 tokenId) public view returns (string memory) {
    require(_exists(tokenId), "ERC721: token does not exist");
    return _tokenURIs[tokenId];
  }

  // 获取NFT的所有者
  function ownerOf(uint256 tokenId) public view returns (address) {
    require(_exists(tokenId), "ERC721: token does not exist");
    return _owners[tokenId];
  }

  // 铸造NFT
  function mint(address to, uint256 tokenId) public {
    require(to != address(0), "ERC721: mint to the zero address");

    _totalSupply++;
    _owners[tokenId] = to;
    _balances[to]++;

    emit Mint(to, tokenId);
  }

  // 转移NFT
  function transfer(address from, address to, uint256 tokenId) public {
    require(_exists(tokenId), "ERC721: token does not exist");
    require(from == _owners[tokenId], "ERC721: transfer from incorrect owner");
    require(to != address(0), "ERC721: transfer to the zero address");

    _balances[from] -= 1;
    _balances[to] += 1;
    _owners[tokenId] = to;

    emit Transfer(from, to, tokenId);
  }

  // 判断NFT是否存在
  function _exists(uint256 tokenId) internal view returns (bool) {
    return _owners[tokenId] != address(0);
  }

}