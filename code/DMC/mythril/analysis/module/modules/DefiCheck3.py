"""This module contains the detection code for arbitrary storage write."""

import sys
import argparse
import pickle
import logging
import re
from typing import Dict, List, TYPE_CHECKING
from collections import deque
from mythril.laser.ethereum.state.constraints import Constraints
from enum import Enum
from flags import Flags
import concurrent.futures

import z3


from antlr4 import (
    FileStream,
    CommonTokenStream,
    ParseTreeWalker,
    ConsoleErrorListener,
    RecognitionException,
    Recognizer,
)

# Import ANTLR-generated modules
from duduDSLLexer import duduDSLLexer
from duduDSLParser import duduDSLParser
from duduDSLListener import duduDSLListener
from duduDSLVisitor import duduDSLVisitor



from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.analysis.potential_issues import (
    get_potential_issues_annotation,
)
from mythril.analysis.swc_data import WRITE_TO_ARBITRARY_STORAGE

from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction.symbolic import ACTORS
from mythril.analysis.issue_annotation import IssueAnnotation
from mythril.analysis.report import Issue
from mythril.exceptions import UnsatError
from mythril.analysis import solver
from mythril.laser.smt import (
    BVAddNoOverflow,
    BVSubNoUnderflow,
    BVMulNoOverflow,
    BitVec,
    If,
    symbol_factory,
    Not,
    Expression,
    Bool,
    And,
    Extract,
    simplify,
    Concat,
    UGT,
)
from mythril.analysis.module.module_helpers import is_prehook
from copy import copy
import time
from collections import defaultdict
from mythril.laser.ethereum.call import get_call_data
from mythril.laser.ethereum.state.calldata import ConcreteCalldata, SymbolicCalldata
from mythril.support.model import get_model
import signal
import multiprocessing
from functools import wraps
# from z3 import Model, unsat, unknown

log = logging.getLogger(__name__)

DESCRIPTION = """
Search for any unstandard approve implements;
"""

Post_hooks = ["AND","OR","CALLDATALOAD","SHA3","SLOAD","CALLER","DELEGATECALL","ADD","SUB","CALL","ISZERO","ADDRESS"]#,"PUSH20"#,"PUSH1"

minus_one= "115792089237316195423570985008687907853269984665640564039457584007913129639935"
print_limit = 1000
while_limit = 100
flag_check = True
flag_detailed = True
flag_time = True
flag_ERC = True
flag_airdrop = True
flag_NFT_MB = True
flag_swap = True
# --------------------------------------------------
flag_check = False # 是否检查
flag_detailed = False # 是否打印详细信息
flag_time = False #是否记录具体运行时间
flag_airdrop = False #是否检查空投
flag_ERC = False #是否只检查ERC20和ERC721的approve、transfer和transferFrom
flag_NFT_MB = False #是否检查NFT的mint和burn
flag_swap = False #是否检查swap

# 常见的非空投函数
not_airdrop_list = [
    "transferFrom(address,address,uint256)",
    "safeTransferFrom(address,address,uint256,bytes)",
    "safeTransferFrom(address,address,uint256)",
    "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)",
    "transfer(address,uint256)",
    "approve(address,uint256)",
    "increaseAllowance(address,uint256)",
    "decreaseAllowance(address,uint256)",
    "mint(address,uint256)",
    "burn(uint256)",
    "burnFrom(address,uint256)",
    "setBaseURI(string)",
    "mint(uint256)",
    "totalSupply()",
    "name()",
    "release(address,address)",
    "release(address)",
    "challenge(uint256,uint256)",
    "getPrice(uint256)",
    "tokenURI(uint256)",
    "symbol()",
    "allowance(address,address)",
    "isApprovedForAll(address,address)",
    "tokenOfOwnerByIndex(address,uint256)",
    "0x862bc2c5", #unstakeNFT(uint256)
    "0x3685d419", #includeInReward(address)
    "0x9a7a23d6", #setAutomatedMarketMakerPair(address,bool)
    "0x51f205e4", #forceSwapBack()
    "0x12a3280e", #mintReward(address[])
    "0xc492f046", #excludeMultipleAccountsFromFees(address[],bool)
    "0x9a55fff0", #excludeFromFees(address,bool)
    "withdraw()",
    "account_info_rotate_tine(uint256)",
    "uri(uint256)"
]

# set|get|Enable|Disable|is|can|total|add|remove|pause|number|toggle|flip
not_NFT_MB = [
    "set",
    "get",
    "enable",
    "Disable",
    "is",
    "can",
    "total",
    "add",
    "remove",
    "pause",
    "number",
    "toggle",
    "filp",
    "supportsInterface"
]


# class JumpType(Enum):
#     """An enum to represent the types of possible JUMP scenarios."""

#     CONDITIONAL = 1
#     UNCONDITIONAL = 2
#     CALL = 3
#     RETURN = 4
#     Transaction = 5


# class NodeFlags(Flags):
#     """A collection of flags to denote the type a call graph node can have."""

#     def __or__(self, other) -> "NodeFlags":
#         return super().__or__(other)

#     FUNC_ENTRY = 1
#     CALL_RETURN = 2

class TimeoutException(Exception):
    pass

def timeout(seconds):
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            def target(queue, *args, **kwargs):
                try:
                    result = func(*args, **kwargs)
                    queue.put(result)
                except Exception as e:
                    queue.put(e)

            queue = multiprocessing.Queue()
            process = multiprocessing.Process(target=target, args=(queue, *args), kwargs=kwargs)
            process.start()
            process.join(seconds)
            if process.is_alive():
                process.terminate()
                process.join()  # 确保进程已终止
                return ""  # 超时返回空字符串
            try:
                result = queue.get_nowait()
            except queue.Empty:
                return ""  # 队列为空返回空字符串
            if isinstance(result, Exception):
                raise result
            return result
        return wrapper
    return decorator

# 使用装饰器定义过滤函数
@timeout(1)
def filter_symbol_var(symbol_var):
    try:
        symbol_var_expr = str(symbol_var.raw)
        if symbol_var_expr in ["1461501637330902918203684832716283019655932542975", "1461501637330902918203684832716283019655932542976-1"]:
            return ""
        return symbol_var_expr
    except Exception as e:
        print(f"ERROR: An unexpected error occurred in filter_symbol_var: {e}")
        return ""

def print_limited(name,obj):
    # Helper function to limit string length
    def limit_length(s):
        s = str(s)
        return s if len(s) <= print_limit else s[:print_limit] + '...'

    if isinstance(obj, (list, tuple)):
        limited_obj = type(obj)(limit_length(item) for item in obj)
    elif isinstance(obj, dict):
        limited_obj = {limit_length(key): limit_length(value) for key, value in obj.items()}
    else:
        limited_obj = limit_length(obj)

    print(f"{name}: {limited_obj}")
    
class NodeType(Enum):
    UNKNOWN = "unknown" #未初始化
    ENVIRONMENT_CONTEXT = "Environment Context"
    STATE_VARIABLES = "State Variables"
    DATA_FLOW = "Data Flow"
    CONTROL_FLOW = "Control Flow"
    LOG_INFORMATION = "Log Information"
    ENTRY_OR_EXIT_POINT = "Entry/Exit Point"
    DELETED = "Deleted"

class Role(Enum):
    """An enum to represent the types of possible roles."""
    #msg.sender
    SENDER = r"sender_\d+"
    PARAM1 = r"\d+_calldata\[4:35\]"  # 参数1
    PARAM2 = r"\d+_calldata\[36:67\]" # 2_calldata[36:67]
    PARAM3 = r"\d+_calldata\[68:99\]"
    PARAM = r"\d+_calldata\[\d+(\+\d+_calldata\[\d+:\d+\])*\:\d+(\+\d+_calldata\[\d+:\d+\])*\]" # 参数
    # VALUE?
    HARD_CODE = None

class FunctionType(Enum):
    """An enum to represent the types of possible roles."""
    CONSTRUCTOR = "constructor"
    FALLBACK = "fallback"
    #approve
    ERC20_APPROVE = "ERC20.approve"
    ERC20_PERMIT = "ERC20.permit"
    ERC721_APPROVE = "ERC721.approve"
    ERC721_SETAPPROVALFORALL = "ERC721.setApprovalForAll"
    #transfer
    ERC20_TRANSFER = "ERC20.transfer"
    ERC20_TRANSFERFROM = "ERC20.transferFrom"
    ERC721_TRANSFERFROM = "ERC721.transferFrom"
    ERC1155_TRANSFERFROM = "ERC1155.transferFrom"
    # ERC721_SAFE_TRANSFER_FROM = "ERC721.safeTransferFrom"
    #mint and burn
    # ERC20_MINT = "ERC20.mint"
    # ERC20_BURN = "ERC20.burn"
    ERC721_MINT = "ERC721.mint"
    ERC721_BURN = "ERC721.burn"
    ERC1155_MINT = "ERC1155.mint"
    ERC1155_BURN = "ERC1155.burn"
    # unknown
    NFT_MINT = "NFT.mint"
    NFT_BURN = "NFT.burn"
    
    #ignore
    ERC_IGNORE = "ignore" #不关心的函数:totalSupply(),balanceOf(),ownerOf(),name(),symbol()等
    
    
    UNKNOWN = "unknown"
    
class IdentityType(Enum):
    """An enum to represent the types of possible roles."""
    #ERC20
    ERC20_BALANCE = "mapping(address account => uint256) private _balances"
    ERC20_ALLOWANCE = "mapping(address => mapping(address => uint256))"
    ERC20_TOTALSUPPLY = "uint256"
    # ERC20_NAME = "string"
    # ERC20_SYMBOL = "string"
    #ERC721
    ERC721_OWNER = "mapping(uint256 tokenId => address) private _owners"
    ERC721_BALANCE = " mapping(address owner => uint256) private _balances"
    ERC721_TOKENAPPROVAL = "mapping(uint256 tokenId => address) private _tokenApprovals"
    ERC721_OPERATORAPPROVAL = " mapping(address owner => mapping(address operator => bool)) private _operatorApprovals"
    # ERC721_NAME = "string"
    # ERC721_SYMBOL = "string"
    # ERC1155
    ERC1155_BALANCE = "mapping(address => mapping(uint256 => uint256)) private _balances" # id, account
    # ERC1155_ALLOWANCE = "mapping(address => mapping(address => mapping(uint256 => uint256)))" # id, owner, spender
    
    UNKNOWN = "unknown"
# Top 10 NFT-burn functions: 
# [('burn(uint256)', 11864),  0x42966c68
# ('burn(address,uint256,uint256)', 7012), 0xf5298aca
# ('burnBatch(address,uint256[],uint256[])', 3072), 0x6b20c454
# ('batchBurn(address,uint256[],uint256[])', 1413), 0xf6eb127a
# ('batchBurn(uint256[])', 970), 0xdc8e92ea
# ('soldBurn(address,uint256,uint256)', 858), 0x4b4b5025
# ('burn(address,uint256)', 813), 0x9dc29fac
# ('burn(uint256,uint256)', 802), 0xb390c0ab
# ('burnToMint(address[],uint256[][],uint256)', 581), 
# ('updateBurnTokens(BurnToken[])', 581)]
# dict func_sign:func_type
# Top 15 NFT-mint functions: 
# [('mint(uint256)', 23780), 0xa0712d68
# ('mintForAddress(uint256,address)', 5636), 0xefbd73f4
# ('mint(address,uint256)', 4204), 0x40c10f19
# ('whitelistMint(uint256,bytes32[])', 4158), 0xd2cab056 721
# ('publicMint(uint256)', 2872), 0x2db11544 721
# ('mint()', 2527),  #不易检测，跳过
# ('mint(uint256,uint8,bytes32,bytes32,Fee[],uint256,string)', 2507), 0x3bc08a37 721/1155
# ('mintTo(address)', 2342), #不易检测，跳过
# ('renounceMinter()', 1748), #不易检测，跳过
# ('mint(uint256,uint8,bytes32,bytes32,Fee[],string)', 1699), 0xdc9e32a6
# ('mint(uint)', 1615), 0x72453eae 721
# ('mint(address)', 1539), #不易检测，跳过
# ('mint(address,uint256,uint256,bytes)', 1539), 0x731133e9 1155
# ('mintWithTokenURI(address,uint256,string)', 1473), 0x50bb4e7f 721
# ('multiConfigureMint(address,uint256[],uint256[])', 1381)]  0xae265953 1155
NFT_MB_func_sign_dict = {
    '0x42966c68':FunctionType.ERC721_BURN, #burn(uint256)
    'burn(uint256)':FunctionType.ERC721_BURN,
    '0xf5298aca':FunctionType.ERC1155_BURN, #burn(address,uint256,uint256)
    'burn(address,uint256,uint256)':FunctionType.ERC1155_BURN,
    '0x6b20c454':FunctionType.ERC1155_BURN, #burnBatch(address,uint256[],uint256[])
    'burnBatch(address,uint256[],uint256[])':FunctionType.ERC1155_BURN,
    '0xf6eb127a':FunctionType.ERC1155_BURN, #batchBurn(address,uint256[],uint256[])
    'batchBurn(address,uint256[],uint256[])':FunctionType.ERC1155_BURN,
    '0xdc8e92ea':FunctionType.ERC721_BURN, #batchBurn(uint256[])
    'batchBurn(uint256[])':FunctionType.ERC721_BURN,
    '0x4b4b5025':FunctionType.ERC1155_BURN, #soldBurn(address,uint256,uint256)
    'soldBurn(address,uint256,uint256)':FunctionType.ERC1155_BURN,
    '0x9dc29fac':FunctionType.ERC721_BURN, #burn(address,uint256)
    'burn(address,uint256)':FunctionType.ERC721_BURN,
    '0xb390c0ab':FunctionType.ERC721_BURN, #burn(uint256,uint256)
    'burn(uint256,uint256)':FunctionType.ERC721_BURN,
    '0xa0712d68':FunctionType.NFT_MINT, #mint(uint256)
    'mint(uint256)':FunctionType.NFT_MINT,
    '0xefbd73f4':FunctionType.ERC721_MINT, #mintForAddress(uint256,address)
    'mintForAddress(uint256,address)':FunctionType.ERC721_MINT,
    '0x40c10f19':FunctionType.ERC721_MINT, #mint(address,uint256)
    'mint(address,uint256)':FunctionType.ERC721_MINT,
    '0xd2cab056':FunctionType.ERC721_MINT, #whitelistMint(uint256,bytes32[])
    'whitelistMint(uint256,bytes32[])':FunctionType.ERC721_MINT,
    '0x2db11544':FunctionType.ERC721_MINT, #publicMint(uint256)
    'publicMint(uint256)':FunctionType.ERC721_MINT,
    '0xc6bf3262':FunctionType.NFT_MINT, #mint(uint256,uint8,bytes32,bytes32,Fee[],uint256,string)
    'mint(uint256,uint8,bytes32,bytes32,(address,uint256)[],uint256,string)':FunctionType.NFT_MINT,
    '0x672a9400':FunctionType.NFT_MINT, #mint(uint256,uint8,bytes32,bytes32,Fee[],string)
    'mint(uint256,uint8,bytes32,bytes32,(address,uint256)[],string)':FunctionType.NFT_MINT,
    '0x72453eae':FunctionType.ERC721_MINT, #mint(uint)
    'mint(uint)':FunctionType.ERC721_MINT,
    '0x731133e9':FunctionType.ERC1155_MINT, #mint(address,uint256,uint256,bytes)
    'mint(address,uint256,uint256,bytes)':FunctionType.ERC1155_MINT,
    '0x50bb4e7f':FunctionType.ERC721_MINT, #mintWithTokenURI(address,uint256,string)
    'mintWithTokenURI(address,uint256,string)':FunctionType.ERC721_MINT,
    '0xae265953':FunctionType.ERC1155_MINT, #multiConfigureMint(address,uint256[],uint256[])
    'multiConfigureMint(address,uint256[],uint256[])':FunctionType.ERC1155_MINT,
    '0x1f7fdffa':FunctionType.NFT_MINT, #mintBatch(address,uint256[],uint256[],bytes)
    'mintBatch(address,uint256[],uint256[],bytes)':FunctionType.NFT_MINT,
    '0x759990fb':FunctionType.ERC721_MINT, #presaleMint(bytes32,bytes,uint256,uint256)
    'presaleMint(bytes32,bytes,uint256,uint256)':FunctionType.ERC721_MINT,
    '0x98588a2b':FunctionType.ERC721_MINT, #batchMint(address,uint256,string,uint256,bool)
    'batchMint(address,uint256,string,uint256,bool)':FunctionType.ERC721_MINT,
    '0x4fba84ca':FunctionType.ERC721_MINT, #mintNifty(uint256,uint256)
    'mintNifty(uint256,uint256)':FunctionType.ERC721_MINT,
    '0xb03f4528':FunctionType.ERC1155_MINT, #mintTo(address,uint256,string,uint256)
    'mintTo(address,uint256,string,uint256)':FunctionType.ERC1155_MINT,
    '0xd0def521':FunctionType.ERC721_MINT, #mint(address,string)
    'mint(address,string)':FunctionType.ERC721_MINT,
    '0x156e29f6':FunctionType.ERC1155_MINT, #"mint(address,uint256,uint256)"
    'mint(address,uint256,uint256)':FunctionType.ERC1155_MINT,
    '0xa1448194':FunctionType.ERC721_MINT, #"safeMint(address,uint256)",
    'safeMint(address,uint256)':FunctionType.ERC721_MINT,
    '0x6a627842':FunctionType.NFT_MINT, #"mint(address)",
    'mint(address)':FunctionType.NFT_MINT,
    '0x2928ca58':FunctionType.ERC721_MINT, #"mintExtension(address)",
    'mintExtension(address)':FunctionType.ERC721_MINT,
    '0x1249c58b':FunctionType.ERC721_MINT, #"mint()",
    'mint()':FunctionType.ERC721_MINT,
    '0x20cbf5f9':FunctionType.NFT_MINT, #"mintToken(uint256,uint256)",
    'mintToken(uint256,uint256)':FunctionType.NFT_MINT,
    '0x755edd17':FunctionType.ERC721_MINT, #"mintTo(address)",
    'mintTo(address)':FunctionType.ERC721_MINT,
    '0x82f57d27':FunctionType.ERC1155_MINT, #"mintToken(uint256,uint32)",
    'mintToken(uint256,uint32)':FunctionType.ERC1155_MINT,
    '0xad6ae674':FunctionType.NFT_MINT, #"performMint(uint32)",
    'performMint(uint32)':FunctionType.NFT_MINT,
    '0xc634d032':FunctionType.NFT_MINT, #"mintToken(uint256)",
    'mintToken(uint256)':FunctionType.NFT_MINT,
    '0xefd0cbf9':FunctionType.NFT_MINT, #"mintPublic(uint256)",
    'mintPublic(uint256)':FunctionType.NFT_MINT,
    '0x94bf804d':FunctionType.ERC721_MINT, #"mint(uint256,address)",
    'mint(uint256,address)':FunctionType.ERC721_MINT,
    '0xa71bbebe':FunctionType.ERC721_MINT, #"mint(uint32)",
    'mint(uint32)':FunctionType.ERC721_MINT,
    '0x40d097c3':FunctionType.ERC721_MINT, #"safeMint(address)",
    'safeMint(address)':FunctionType.ERC721_MINT,
    '0xd204c45e':FunctionType.ERC721_MINT, #"safeMint(address,string)",
    'safeMint(address,string)':FunctionType.ERC721_MINT,
    '0x7fbcc639':FunctionType.ERC721_MINT, #"mint(uint256,uint8,bytes32,bytes32,string)",
    'mint(uint256,uint8,bytes32,bytes32,string)':FunctionType.ERC721_MINT,
    '0x6ecd23060':FunctionType.NFT_MINT, #"mint(uint8)",
    'mint(uint8)':FunctionType.NFT_MINT,
    '0xd96a094a':FunctionType.ERC721_MINT, #"buy(uint256)",
    'buy(uint256)':FunctionType.ERC721_MINT,
    '0x40ccc082':FunctionType.ERC721_MINT, #"mintToAdminV2(address,uint256)"
    'mintToAdminV2(address,uint256)':FunctionType.ERC721_MINT,
    '0x23cf0a22':FunctionType.ERC721_MINT, #"mint(uint16)"
    'mint(uint16)':FunctionType.ERC721_MINT
}


    

class Node:
    """The representation of a call graph node."""
    count = 0  # 类变量，用于跟踪Node的实例数量
    cur_pc= 0  # 暂时没有用上
    # find_edge_time = 0
    find_edge_time = {}
    find_start_nodes_time = 0
    equal_is_time = {}
    equal_str_time = {}

    def __init__(
        self,
        nodes,
        contract_name: str,
        state,
        # start_addr=0,
        # constraints=None,
        node_type=NodeType.UNKNOWN,  
        function_name="unknown",
        symbol_vars=None,
        predecessors_list=None,
        ExitNode_uid=-1,
        # slot="",
        # value="",
    ) -> None:
        """

        :param contract_name:
        :param start_addr:
        :param constraints:
        """
        # print(Node.count,"node",state.node.get_cfg_dict()) #查看当前基本块
        # constraints = constraints if constraints else Constraints()
        self.contract_name = contract_name
        # self.start_addr = start_addr
        # self.states: List[GlobalState] = []
        self.state = state 
        # self.constraints = constraints
        self.node_type = node_type
        self.function_name = function_name
        # tx_id
        try:
            # 如果current_transaction包含indentify，就用indentify
            if hasattr(self.state.current_transaction, "indentify"):
                self.tx_id = self.state.current_transaction.indentify
            else:#否则从call_value中提取tx_id
                call_value = self.state.current_transaction.call_value
                match = re.search(r'call_value(\d+)', str(call_value))
                if match:
                    self.tx_id = int(match.group(1))
                else:
                    raise ValueError("Cannot extract tx_id from call_value", call_value)
        except Exception as e:
            if contract_name == "constructor":
                self.tx_id = 1
            else:
                print("#ERROR:tx_id error:", e)
                self.tx_id = -1
        # self.nodes=nodes
        
        self.uid = Node.count # 编号
        if flag_detailed:
            print("new Node.uid: ",self.uid)
        # print("self.uid: ",self.uid)
        Node.count += 1  # 每次创建新的Node实例时，增加count的值
        self.pc = Node.cur_pc #自定义，看看能不能利用mythril的CFG图
        self.offset = self.state.get_current_instruction()["address"] #原本的PC，用于区分分支
        if self.node_type == NodeType.ENTRY_OR_EXIT_POINT:
            self.opcode = ""
        elif self.node_type == NodeType.UNKNOWN:
            self.opcode = self.state.get_current_instruction()["opcode"]
            if self.opcode == "CALLDATALOAD" or self.opcode == "CALLER" or self.opcode == "ADDRESS": #还有msg.value#or self.opcode == "PUSH1"
                self.node_type = NodeType.ENVIRONMENT_CONTEXT
            elif self.opcode == "SLOAD" or self.opcode == "SSTORE":
                self.node_type = NodeType.STATE_VARIABLES
            elif self.opcode.startswith("PUSH") or self.opcode in ["AND","OR","SHA3","ADD","SUB"]:
                self.node_type = NodeType.DATA_FLOW
            # control flow 待补充
            elif self.opcode.startswith("LOG") or self.opcode == "FUNC":
                self.node_type = NodeType.LOG_INFORMATION
            elif self.opcode.startswith("JUMP") or self.opcode in ["STOP","RETURN","REVERT","CALL","DELEGATECALL"]:
                self.node_type = NodeType.CONTROL_FLOW
                
        else:
            self.opcode = self.state.get_current_instruction()["opcode"]
        # self.argument = self.state.get_current_instruction()["argument"]
        # if self.opcode.startswith("PUSH"):
        #     code += " " + "".join(str(self.state.get_current_instruction()["argument"]))
        self.symbol_vars = symbol_vars if symbol_vars is not None else []
        if self.opcode.startswith("LOG"):
            self.log_hash = hex(self.symbol_vars[0].value) if self.symbol_vars[0].value else Node.get_last_bracket_content(PreProcExpr(str(self.symbol_vars[0])))
            self.symbol_vars = self.symbol_vars[1:]
        else:
            self.log_hash =None
        if self.opcode in ["SSTORE","SLOAD"] or (not self.opcode.startswith("JUMP") and not self.opcode in Post_hooks) and flag_detailed: # trick：优化耗时：转换字符串耗时较长的结点在查找前驱结点时才转换
            self.symbol_vars_expr = [Node.get_last_bracket_content(symbol_var_preprocess(var)) for var in self.symbol_vars] 
        else:
            self.symbol_vars_expr = ["" for var in self.symbol_vars] 
            
        #CALL or DELEGATECALL
        if self.opcode in ["CALL","DELEGATECALL"]:
            self.call_func_signature = None
            self.call_params = []
            self.call_params_expr = []
            
            if self.opcode == "CALL":
                memory_input_offset = self.symbol_vars[3]
                memory_input_size = self.symbol_vars[4]
                self.value = Node.get_last_bracket_content(PreProcExpr(str(self.symbol_vars[2])))
            else:
                self.value = "0"
                memory_input_offset = self.symbol_vars[2]
                memory_input_size = self.symbol_vars[3]
            call_data = get_call_data(state, memory_input_offset, memory_input_size)
            if flag_detailed:
                print("call_data",str(call_data._calldata))
            
            
            call_data_list = []
            if isinstance(call_data, ConcreteCalldata):
                call_data_list =  call_data.concrete(None)
                print("ConcreteCalldata size:",len(call_data_list))
            else:
                print("SymbolicCalldata")
                print(f"SymbolicCalldata(size={call_data._size},Array(domain={call_data._calldata.domain}, value={call_data._calldata.range}))")
                try:
                    constraints = self.state.world_state.constraints
                    model = get_model(constraints)
                    call_data_list =  call_data.concrete(model)
                    print("len(call_data_list)",len(call_data_list))
                except UnsatError:
                    model = None
                    print("## UnsatError")
            if call_data_list != []: # 非指定的函数签名
                # print("call_data_list",call_data_list)
                func_signature = check_func_hash(call_data_list)  
                print("# CALL func_signature:",func_signature)
                self.call_func_signature = func_signature # CALL调用的函数签名
                # 获取call_data中的符号变量
                if self.call_func_signature and self.call_func_signature in [FuncHash.TRANSFER,FuncHash.TRANSFER_FROM]:
                    print("len(call_data_list)",len(call_data_list))
                    # print("call_data_list",call_data_list)
                    # 确保 call_data_list 中的元素是位向量对象
                    try:
                        call_params_1 = Concat(call_data_list[4:36])
                        # 如果call_params_1是整数，直接转换为字符串
                        if not isinstance(call_params_1, int):
                            call_params_1 = simplify(call_params_1)
                        print("call_params_1",Node.get_last_bracket_content(PreProcExpr(str(call_params_1))))
                        # print("call_params_1",type(call_params_1[0]))
                        call_params_2 = Concat(call_data_list[36:68])
                        if not isinstance(call_params_2, int):
                            call_params_2 = simplify(call_params_2)
                        print("call_params_2",Node.get_last_bracket_content(PreProcExpr(str(call_params_2))))
                        # print("call_params_2",call_params_2)
                        if self.call_func_signature == FuncHash.TRANSFER:
                            self.call_params = [call_params_1,call_params_2]
                            self.call_params_expr = [Node.get_last_bracket_content(PreProcExpr(str(call_params_1))),Node.get_last_bracket_content(PreProcExpr(str(call_params_2)))]
                        elif self.call_func_signature == FuncHash.TRANSFER_FROM:
                            call_params_3 = Concat(call_data_list[68:100])
                            if not isinstance(call_params_3, int):
                                call_params_3 = simplify(call_params_3)
                            print("call_params_3",Node.get_last_bracket_content(PreProcExpr(str(call_params_3))))
                            self.call_params = [call_params_1,call_params_2,call_params_3]
                            self.call_params_expr = [Node.get_last_bracket_content(PreProcExpr(str(call_params_1))),Node.get_last_bracket_content(PreProcExpr(str(call_params_2))),Node.get_last_bracket_content(PreProcExpr(str(call_params_3)))]
                    except Exception as e:
                        print("#ERROR: call_params error:", e)
                        
                                
        if predecessors_list is None:
            if self.opcode == "SSTORE" or self.opcode == "SLOAD":
                self.predecessors_list = [[],[]] #前驱节点列表
            elif len(self.symbol_vars) == 0:
                self.predecessors_list =[[]]
            elif self.node_type == NodeType.CONTROL_FLOW:
                self.predecessors_list =[[]]
            else:
                self.predecessors_list = [[] for _ in range(len(self.symbol_vars))] #前驱节点列表
        else:
            self.predecessors_list = predecessors_list
        if ExitNode_uid == -1:
            self.successors = []  # 后继指针数组
        else:
            self.successors = [ExitNode_uid]
            nodes[ExitNode_uid].predecessors_list[0].append(self.uid)
        # self.flags = NodeFlags()
        
        # 记录所在基本块开头的JUMPDEST或JUMPI结点，如果是第一个基本块则指向entry结点
        self.cfg_uid_info = []
        if self.node_type in [NodeType.ENVIRONMENT_CONTEXT,NodeType.DATA_FLOW,NodeType.STATE_VARIABLES,NodeType.LOG_INFORMATION] \
            or self.opcode in ["CALL","DELERATECALL"]:
            self.cfg_uid_info.append(self.find_cfg_start_node(nodes,ExitNode_uid))
            nodes[self.cfg_uid_info[0]].cfg_uid_info.append(self.uid)
            
        
        if self.opcode not in ["AND","OR","SHA3","SLOAD","CALL"] \
            and self.node_type not in [NodeType.ENTRY_OR_EXIT_POINT,NodeType.CONTROL_FLOW]: 
            #非起始节点中需要post_hook处理的 #"PUSH20",#
            self.find_edge(nodes,ExitNode_uid)
        self.post_flag = False #需要post_hook处理
        if self.opcode in Post_hooks:
            self.post_flag = True
        # else:
        #     # Node删除Node.nodes
        #     self.remove_nodes()
        
       
        
    
    # 删除nodes属性
    def remove_state(self):
        del self.state

    def get_dict(self) -> Dict:
        """

        :return:
        """
        # code = ""
        # instruction = self.state.get_current_instruction()

        # code += str(instruction["address"]) + " " + instruction["opcode"]
        # if instruction["opcode"].startswith("PUSH"):
        #     code += " " + "".join(str(instruction["argument"]))

        # code += "\\n"
        if self.node_type == NodeType.DELETED:
            return dict(
                uid=self.uid,
                tx_id=self.tx_id,
                opc=self.opcode,
                node_type=NodeType.DELETED.value
            )
        elif self.opcode.startswith("LOG"):
            return dict(
                uid=self.uid,
                tx_id=self.tx_id,
                predecessors_list=self.predecessors_list,
                opcode=self.opcode,
                log_hash=self.log_hash,
                symbol_vars_expr= self.symbol_vars_expr,
                contract=self.contract_name,
            )
        elif self.opcode.startswith("JUMP"):
            return dict(
                uid=self.uid,
                tx_id=self.tx_id,
                predecessors_list=self.predecessors_list,
                opcode=self.opcode,
                # symbol_vars_expr= self.symbol_vars_expr[0], #JUMPI的bool型变量未处理完
                offset=self.offset,
                contract=self.contract_name,
                # symbol_vars=[str(var) for var in self.symbol_vars],
                cfg_uid_info=self.cfg_uid_info,
            )
        elif self.opcode in ["CALL","DELEGATECALL"]:
            return dict(
                uid=self.uid,
                tx_id=self.tx_id,
                predecessors_list=self.predecessors_list,
                opcode=self.opcode,
                func_sign=self.call_func_signature,
                params_expr=self.call_params_expr,
                value=self.value,
                contract=self.contract_name,
                offset=self.offset,
                cfg_uid_info=self.cfg_uid_info,
            )
        else:
            # 如果'Node' object has no attribute 'symbol_vars_expr'
            if hasattr(self, 'symbol_vars_expr'):
                return dict(
                    uid=self.uid,
                    # pc=self.pc,
                    # contract_name=self.contract_name,
                    # # start_addr=self.start_addr,
                    # function_name=self.function_name,
                    # # code=code,
                    # offset=self.offset,
                    # type=self.node_type.value,
                    tx_id=self.tx_id,
                    predecessors_list=self.predecessors_list,
                    # successors = self.successors,
                    opcode=self.opcode,
                    # slot=PreProcExpr(str(self.slot)),
                    # value=PreProcExpr(str(self.value)),
                    # symbol_vars={var: PreProcExpr(str(self.symbol_vars[var])) for var in self.symbol_vars},
                    # slot_expr=Node.get_last_bracket_content(PreProcExpr(str(self.slot))),
                    # value_expr= Node.get_last_bracket_content(PreProcExpr(str(self.value)))
                    # symbol_vars=self.symbol_vars,
                    # symbol_vars=[PreProcExpr(str(var)) for var in self.symbol_vars],
                    symbol_vars_expr = [ 
                        (expr[:print_limit] + '...' if len(expr) > print_limit else expr) if expr is not None else '' 
                        for expr in self.symbol_vars_expr
                    ],
                    contract=self.contract_name,
                    offset=self.offset,
                    cfg_uid_info=self.cfg_uid_info,
                )
            else:
                return dict(
                    uid=self.uid,
                    tx_id=self.tx_id,
                    predecessors_list=self.predecessors_list,
                    opcode=self.opcode,
                    contract=self.contract_name,
                    offset=self.offset,
                )
    
    def get_matching_brackets(s):
        stack = []
        brackets = {}
        for i, char in enumerate(s):
            if char in '([':
                # 将左括号和其位置一起压入栈中
                stack.append((char, i))
            elif char in ')]':
                if stack:
                    # 检查栈顶的左括号是否与当前的右括号匹配
                    left_bracket, left_index = stack[-1]
                    if (left_bracket == '(' and char == ')') or (left_bracket == '[' and char == ']'):
                        # 如果匹配，就将其从栈中弹出，并记录下这对括号的位置
                        stack.pop()
                        brackets[left_index] = i
        return brackets

    def extract_value_from_store(s):
        #利用get_matching_brackets函数
        matching_brackets = Node.get_matching_brackets(s)
        # 利用正则表达找到 第一个Store( 的(对应index
        import re
        store_pattern = r"Store\("
        store_index = re.search(store_pattern, s).start()
        store_end_index = matching_brackets[store_index+5]
        store = s[store_index+6:store_end_index]
        key_index = store_end_index+1
        if key_index < len(s) and s[key_index] in '([':
            key_end_index = matching_brackets[key_index]
            key = key = s[key_index+1:key_end_index] #key存储内容
            if ","+key+"," in store:
                matching_brackets = Node.get_matching_brackets(store)
                # index为key在store中的位置
                key_pattern = r",{},".format(re.escape(key))
                key_index2 = re.search(key_pattern, store).start()+1
                key_end_index2 = key_index2+len(key)
                value_index = key_end_index2+1
                value_end_index = value_index
                while value_end_index < len(store) and value_end_index <= store_end_index and store[value_end_index] != ')' :
                    if store[value_end_index] in '([':#如果遇到括号，跳过括号内的内容
                        value_end_index = matching_brackets[value_end_index]+1
                    else:
                        value_end_index += 1
                        
                value = store[value_index:value_end_index]
                s= s[:store_index]+value+s[key_end_index+1:]
            else:
                s = s[:store_index]+s[key_index:key_end_index+1]+s[key_end_index+1:]
        else:
            if store_index==0 or s[store_index-1] != ",":
                s = s[:store_index]+s[store_end_index+1:]
            else:
                s = s[:store_index-1]+s[store_end_index+1:]
        return s
    
    def get_last_bracket_content(s):#获取最后一个括号内的内容
        if s == "":
            return s
        if "Concat" not in s and "Store" not in s:
            return s
        # 去除Concat
        if "Concat" in s:
            s = Node.remove_concat(s)
        # 简化Store
        if "Store" in s:
            while "Store" in s:
                s = Node.extract_value_from_store(s)
            return s
        else:
            return s
        
        
    def get_last_bracket_content2(s):#获取最后一个括号内的内容
        if s == "":
            return s
        
        # Replace "(0,sender_" or "(0,calldata[" with "(sender_" or "{number}_calldata["
        # s = re.sub(r"\(0,(sender_|(\d+_calldata\[))", r"(\1", s)
        s = re.sub(r"\(0,(sender_|(\d+_calldata\[)|Extract\()", r"(\1", s)
        # s = s.replace("(0,", "(")
        #如果不是以sstore开头的字符串，不进行处理
        if not s.startswith("Concat") and "Store" not in s:
        # if not s.startswith("Concat"):
            return s
        if s.startswith("Concat"):
            stack = []
            last_bracket_index = -1
            last_bracket_end_index = -1

            for i, char in enumerate(s):
                if char in '([{':
                    stack.append((char, i))
                elif char in ')]}':
                    if not stack:
                        continue
                    last_char, last_index = stack.pop()
                    if (char == ')' and last_char != '(') or \
                    (char == ']' and last_char != '[') or \
                    (char == '}' and last_char != '{'):
                        continue
                    last_bracket_index = last_index
                    last_bracket_end_index = i

            if last_bracket_index == -1:
                return ""
    
            # return s[last_bracket_index:last_bracket_end_index+1]
            if s[last_bracket_index] == "(":
                # if len(s) <= last_bracket_end_index+1:
                s = Node.get_last_bracket_content(s[last_bracket_index+1:last_bracket_end_index])
            else:
                s = Node.get_last_bracket_content(s[last_bracket_index:last_bracket_end_index+1])

        if "Store" in s:
            while "Store" in s:
                s = Node.extract_value_from_store(s)
            return s
        else:
            return s
            
    
    def remove_concat(input_str):
        # 寻找字符串中的 Concat(a,b) 模式
        input_str = input_str.replace("(0,", "(")# 删除0,
        input_str = input_str.replace("255", "ff")
        start_index = input_str.find("Concat(")
        while start_index != -1:
            # 找到 Concat(a,b) 的结束括号的位置
            end_index = start_index + 7
            nested = 1
            while nested != 0:
                if input_str[end_index] == "(":
                    nested += 1
                elif input_str[end_index] == ")":
                    nested -= 1
                end_index += 1
            
            # 提取 Concat(a,b) 中的内容
            concat_content = input_str[start_index + 7:end_index - 1]
            
            # 将 Concat(a,b) 替换为 a+b
            input_str = input_str[:start_index] + concat_content + input_str[end_index:]
            
            # 继续寻找下一个 Concat(a,b)
            start_index = input_str.find("Concat(")
        
        return input_str
    
    def symbol_var_equal(self, var1, var2,var1_expr="",var2_expr=""):
        if var1 is var2:
            return True
        else:
            if var1.size() == var2.size() \
                and var1 == var2\
                and var1.raw == var2.raw:
                    return True
            else:
                return False
        # start_time =time.time()
        # if var1 is var2:
        #     return True
        # else:
        #     flag1 = (var1 == var2)
        #     if self.opcode not in Node.equal_is_time:
        #         Node.equal_is_time[self.opcode] = [time.time()-start_time,1]
        #     else:
        #         Node.equal_is_time[self.opcode][0] += time.time()-start_time
        #         Node.equal_is_time[self.opcode][1] += 1
        #     flag2 = (var1.raw == var2.raw)
        #     if self.opcode not in Node.equal_str_time:
        #         Node.equal_str_time[self.opcode] = [time.time()-start_time,1]
        #     else:
        #         Node.equal_str_time[self.opcode][0] += time.time()-start_time
        #         Node.equal_str_time[self.opcode][1] += 1
        #     if  flag1 and flag2:
        #         return True
        #     else:
        #         return False
            
    def symbol_var_equal2(self, var1, var2,var1_expr="",var2_expr=""): #判断符号变量是否相等
        start_time =time.time()
        if var1 is var2:
            return True
        else:
            var1_str = str(var1)
            var2_str = str(var2)
            if self.opcode not in Node.equal_is_time:
                Node.equal_is_time[self.opcode] = [time.time()-start_time,1]
            else:
                Node.equal_is_time[self.opcode][0] += time.time()-start_time
                Node.equal_is_time[self.opcode][1] += 1
            if var1_str == var2_str:
                if self.opcode not in Node.equal_str_time:
                    Node.equal_str_time[self.opcode] = [time.time()-start_time,1]
                else:
                    Node.equal_str_time[self.opcode][0] += time.time()-start_time
                    Node.equal_str_time[self.opcode][1] += 1
                return True
            else:
                if self.opcode not in Node.equal_str_time:
                    Node.equal_str_time[self.opcode] = [time.time()-start_time,1]
                else:
                    Node.equal_str_time[self.opcode][0] += time.time()-start_time
                    Node.equal_str_time[self.opcode][1] += 1 
                return False
            str_time = time.time()
            if var1_expr == "":
                var1_expr = Node.get_last_bracket_content(PreProcExpr(str(var1)))
            if var2_expr == "":
                var2_expr = Node.get_last_bracket_content(PreProcExpr(str(var2)))
            expr_time = time.time()
            # var1_expr = Node.get_last_bracket_content(PreProcExpr(str(var1)))
            if var1_expr == var2_expr:
                constraints = copy(self.state.world_state.constraints)
                constraints += [
                    var1 == var2,
                ]
                try:
                    solver.get_model(constraints)
                    # if var1 is var2:
                    #     return True
                    # else:
                    #     return False
                    return True
                except UnsatError:
                    return False
                # return True
            else:
                return False  

    def remove_outermost_brackets(s, layers=1):
        for _ in range(layers):
            brackets = Node.get_matching_brackets(s)
            if brackets:
                # 获取最外层括号的位置
                outermost_start = min(brackets.keys())
                outermost_end = brackets[outermost_start]
                # 去除最外层的括号
                s = s[outermost_start+1:outermost_end]
        return s
    
    def find_cfg_start_node(
            self,
            nodes,
            ExitNode_uid,
        ): # 查找基本块的起始结点(JUMPI或JUMPDEST，以及第一个基本块的entry结点)
            tx_id = self.tx_id
            instruction = self.state.node.states[0].get_current_instruction()  # 获取基本块第一条指令
            if instruction["opcode"] == "JUMPDEST":
                offset = instruction["address"]
                opcode = "JUMPDEST"
            else: #JUMPI的offset记为另一条分支的起始结点
                offset = instruction["address"]-1
                opcode = "JUMPI"
            # print("##1temp 基本块第一条指令",offset,opcode,"self.offset",self.offset)
            # # trick:特殊情况
            if self.opcode in ["JUMPI"]:# 这种情况找找看前一个cfg结点JUMPDEST
                for node_uid in range(self.uid-1, -1, -1):
                    if nodes[node_uid].function_name != self.function_name:
                        continue
                    if nodes[node_uid].tx_id != tx_id:
                        continue
                    if nodes[node_uid].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                        continue
                    if nodes[node_uid].node_type == NodeType.DELETED:
                        continue
                    if nodes[node_uid].opcode == "JUMPI":
                        break
                    if nodes[node_uid].opcode not in ["JUMPDEST"]:#,"JUMPI"
                        continue
                    if nodes[node_uid].opcode == "JUMPDEST" and nodes[node_uid].offset<self.offset:
                        # print("##temp 基本块第一条指令",offset,opcode)
                        return node_uid
                    else:
                        # print(nodes[node_uid].successors[0],"nodes[nodes[node_uid].successors[0]].node_type",nodes[nodes[node_uid].successors[0]].node_type)
                        break
            # 查找前驱结点
            for node_uid in range(self.uid-1, -1, -1):
                if nodes[node_uid].function_name != self.function_name:
                    continue
                if nodes[node_uid].tx_id != tx_id:
                    continue
                if nodes[node_uid].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                    continue
                if nodes[node_uid].node_type == NodeType.DELETED:
                    continue
                if nodes[node_uid].opcode != opcode :
                    continue
                if self.opcode in ["JUMP","JUMPI"] \
                    and (
                        (nodes[node_uid].opcode == "JUMPI" \
                            and (len(nodes[node_uid].successors) > 1 ) \
                        ) \
                        or (nodes[node_uid].opcode == "JUMPDEST" and nodes[nodes[node_uid].successors[0]].node_type != NodeType.ENTRY_OR_EXIT_POINT)
                        ):
                    # JUMP/JUMPI结点的查找前驱JUMPI应该至多有两后继节点，或JUMPDEST节点应该只有一个后继节点
                    continue
                if nodes[node_uid].offset == offset: 
                    # 且self.offset应该大于node_uid的cfg_uid_info[-1]的offset
                    if len(nodes[node_uid].cfg_uid_info) == 0 or self.offset > nodes[nodes[node_uid].cfg_uid_info[-1]].offset:
                        return node_uid
                    else:
                        continue
            # print("##self.uid",self.uid,"self.offset",self.offset,"opcode",self.opcode,"offset",offset,"opcode",opcode)
            # 无前驱结点说明是第一个基本块，找到第一个结点
            for node_uid in range(0, len(nodes)):
                if nodes[node_uid].function_name != self.function_name:
                    continue
                if nodes[node_uid].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                    # 添加前驱结点
                    # self.predecessors_list[0].append(node_uid)
                    # nodes[node_uid].successors.append(self.uid)
                    return node_uid
                
            
        

    def find_SHA3_edge(self,
                  nodes,
                  ExitNode_uid,
                  ): #处理SHA3节点查找前驱节点
        if len(self.symbol_vars_expr) != 1:
            print("ERROR: SHA3 node",self.uid," symbol_vars_expr.count != 1")
        elif self.symbol_vars_expr[0] == "26894051635933088883208542908936412374951772594250132926352947286596149155043":
            # address(this) 得到的硬编码，查找直接前驱节点为ADD节点：51421440056055728346017419001665401074216449311
            temp_predecessors = []
            # for uid in range(self.uid-1, -1, -1):
            for uid in reversed(self.get_path_nodes(nodes)):
                if nodes[uid].function_name != self.function_name:
                    continue
                # if nodes[uid].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                #     continue
                # if nodes[uid].node_type == NodeType.LOG_INFORMATION:
                #     # 不会做中间节点的node
                #     continue
                # if nodes[uid].node_type == NodeType.DELETED:
                #     continue
                if nodes[uid].opcode == "AND" and nodes[uid].symbol_vars_expr[0] == "51421440056055728346017419001665401074216449311":
                    temp_predecessors.append(uid)
                    if ExitNode_uid in nodes[uid].successors:
                        nodes[uid].successors.remove(ExitNode_uid)
                        nodes[ExitNode_uid].predecessors_list[0].remove(uid)
                    if self.uid not in nodes[uid].successors:
                        nodes[uid].successors.append(self.uid)
                    break
            self.predecessors_list=[temp_predecessors]          
        else:
            temp_var_expr=self.symbol_vars_expr[0]
            temp_var_expr = Node.remove_outermost_brackets(temp_var_expr)
            # 以逗号为分界符，将temp_var_expr分为两部分
            parts = []
            temp_part = []
            parentheses_count = 0
            for char in temp_var_expr:
                if char == '(':
                    parentheses_count += 1
                elif char == ')':
                    parentheses_count -= 1
                if char == ',' and parentheses_count == 0:
                    parts.append(''.join(temp_part))
                    temp_part = []
                else:
                    temp_part.append(char)
            parts.append(''.join(temp_part))  # 添加最后一部分
            # 处理：0,开头的情况
            if len(parts)>2 and parts[0] == "0":
                parts = parts[1:]
            temp_var_expr = parts
            # print("# sha3 slot parts:",parts)
            if len(temp_var_expr) == 2:
                # print(self.uid,"temp_var_expr",temp_var_expr)
                temp_var_expr[0] = temp_var_expr[0].strip()
                temp_var_expr[1] = temp_var_expr[1].strip()
                # key,index:index可能为identity也可能是SHA3之后的结果，前者不需要处理
                if temp_var_expr[1].isdigit() and temp_var_expr[1] != "26894051635933088883208542908936412374951772594250132926352947286596149155043": #如果是正整数，去掉temp_var_expr[1]
                    temp_var_expr = [temp_var_expr[0]]
                temp_predecessors = [[] for _ in range(len(temp_var_expr))]
                for i in range(len(temp_var_expr)):
                    var = temp_var_expr[i]
                    # print("var",var)
                    for uid in reversed(self.get_path_nodes(nodes)): # 从当前节点往前找（uid是从1开始的）
                        if nodes[uid].function_name != self.function_name:
                            continue
                        # print("uid:",uid,"nodes[uid].opcode:",nodes[uid].opcode)
                        if nodes[uid].opcode not in ["SHA3","AND","CALLDATALOAD","CALLER","ADDRESS"]:#,"ADD"
                            continue
                        # print("uid:",uid,"nodes[uid].symbol_vars_expr:",nodes[uid].symbol_vars_expr)
                        if nodes[uid].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                            print("ENTRY_OR_EXIT_POINT")
                            continue
                        # if nodes[uid].node_type == NodeType.LOG_INFORMATION:
                        #     # 不会做中间节点的node
                        #     continue
                        if nodes[uid].node_type == NodeType.DELETED:
                            continue
                        # if nodes[uid].node_type == NodeType.STATE_VARIABLES:
                        #     continue
                        if nodes[uid].opcode in ["AND","OR"]:#TODO
                            if nodes[uid].symbol_vars_expr[0] == "...":
                                nodes[uid].symbol_vars_expr = [Node.get_last_bracket_content(symbol_var_preprocess(var)) for var in nodes[uid].symbol_vars]
                        for j in range(len(nodes[uid].symbol_vars_expr)):
                            # print("uid:",uid,"nodes[uid].symbol_vars_expr[j]:",nodes[uid].symbol_vars_expr[j],"var:",var,nodes[uid].symbol_vars_expr[j]==var)
                            # if nodes[uid].node_type == NodeType.STATE_VARIABLES and j == 0: # 不可能来源于SSTORE或SLOAD节点为slot
                            #     continue
                            # if nodes[uid].opcode == "SHA3" :
                            #     print(f"uid:{uid},nodes[uid].symbol_vars_expr:{nodes[uid].symbol_vars_expr},var:{var}")
                            #     print(f"nodes[uid].symbol_vars_expr[j]==var:{nodes[uid].symbol_vars_expr[j]==var}")
                            if nodes[uid].symbol_vars_expr[j]==var:
                                temp_predecessors[i].append(uid)
                                # print("add temp_predecessors[i]:",i,temp_predecessors[i])
                                if ExitNode_uid in nodes[uid].successors:
                                    nodes[uid].successors.remove(ExitNode_uid)
                                    nodes[ExitNode_uid].predecessors_list[0].remove(uid)
                                if self.uid not in nodes[uid].successors:
                                    nodes[uid].successors.append(self.uid)
                                break
                            # print("sha3 check nodes[uid].symbol_vars_expr[j]:",uid,nodes[uid].symbol_vars_expr[j])
                        if temp_predecessors[i] != []:
                            # print("temp_predecessors[i]:",i,temp_predecessors[i])
                            break
                        
                self.predecessors_list=[[]]
                for i in range(len(temp_predecessors)):
                    self.predecessors_list[0].extend(temp_predecessors[i])
            else:
                print("ERROR: SHA3 node",self.uid," source count != 2")
                print("temp_var_expr:",temp_var_expr,"\nparts",parts)
                print_limited("temp_var_expr",self.symbol_vars_expr[0])
                # print("@@@@symbol_vars",self.symbol_vars)
                return
        return

    # def find_edge2(self,
    #               nodes,
    #               ExitNode_uid,
    #               ):
    #     if not nodes or self.opcode in ["CALLDATALOAD","CALLER"]:#非起始节点,"PUSH1"
    #         return
    #     if self.symbol_vars.count == 0:
    #         print("ERROR: node",self.uid," symbol_vars.count == 0")
    #         return
    #     if self.symbol_vars.count == 1:
    #         temp_var1_expr=self.symbol_vars_expr[0]
    #     else:
    #         temp_var1_expr=self.symbol_vars_expr[0]
    #         temp_vars_expr=self.symbol_vars_expr[1:]
    #         #将temp_vars_expr中元素的If(And(...),0,1)替换为And(...)
    #         temp_vars_expr = [re.sub(r'If\((.*),(0,1|1,0)\)', r'\1', temp_var_expr) for temp_var_expr in temp_vars_expr]
    #         #去除"),0)"的",0",使用identity_sub
    #         # temp_vars_expr = [re.sub(r'\),0\)', ')\)', temp_var_expr) for temp_var_expr in temp_vars_expr]
    #         temp_vars_expr = [identity_sub(temp_var_expr) for temp_var_expr in temp_vars_expr]
    #         if self.opcode == "SSTORE":
    #             if "Concat(Extract" in temp_vars_expr[0]: #If(And(3_calldata[36:67]),0,1)|Concat(Extract(255,8,[keccak256_512(Concat(3_calldata[16:35],keccak256_512(Concat(sender_3,4))))]),0)
    #                 try:
    #                     # temp_vars_expr[0] 去除Concat(Extract(\d+,\d+,...),...),利用Node.get_matching_brackets(s)函数
    #                     matching_brackets = Node.get_matching_brackets(temp_vars_expr[0])
    #                     concat_index = temp_vars_expr[0].find("Concat(Extract")
    #                     temp_vars_expr[0] = temp_vars_expr[0][:concat_index]+temp_vars_expr[0][matching_brackets[concat_index+6]+2:]
    #                 except Exception as e:
    #                     print("#ERROR:",self.function_name,"node",self.uid," Concat(Extract")
    #                     # print("temp_vars_expr[0]:",temp_vars_expr[0])
    #                     print_limited("temp_vars_expr[0]",temp_vars_expr[0])
    #                     return
    #             elif "Extract" in temp_vars_expr[0]:
    #                 # temp_vars_expr[0] 去除Extract(\d+,\d+,...),利用Node.get_matching_brackets(s)函数
    #                 matching_brackets = Node.get_matching_brackets(temp_vars_expr[0]) #匹配括号数组
    #                 # print("matching_brackets:",matching_brackets)
    #                 # print("temp_vars_expr[0]:",temp_vars_expr[0])
    #                 # 找到第一个Extract的位置,去除没有被覆盖的无关部分
    #                 extract_index = temp_vars_expr[0].find("Extract")
    #                 temp_vars_expr[0] = temp_vars_expr[0][:extract_index]+temp_vars_expr[0][matching_brackets[extract_index+7]+1:]
                
    #         # print("temp_vars_expr:",temp_vars_expr)
    #     if self.function_name == "setApprovalForAll(address,bool)" and self.opcode == "SSTORE":
    #         pass
    #         # print("#######bool########")
    #         # print("temp_var1_expr:",temp_var1_expr)
    #         # print("temp_vars_expr:",temp_vars_expr)
    #     # print("temp_var1_expr:",temp_var1_expr)
    #     if re.fullmatch("Extract\(\d+,\d+,(\[keccak256_512\(Concat\(\d+_calldata\[\d+:\d+\],\d+\)\)\])\)",temp_var1_expr):
    #         # 针对Extract(159,0,[keccak256_512(Concat(4_calldata[68:99],2))])的特殊处理
    #         temp_var1_expr = re.fullmatch("Extract\(\d+,\d+,(\[keccak256_512\(Concat\(\d+_calldata\[\d+:\d+\],\d+\)\)\])\)",temp_var1_expr)[1]
    #     else:
    #         temp_var1_expr = re.sub(r'Extract\(\d+,\d+,', '', temp_var1_expr)
    #         #If(And(...),0,1)替换为And(...)
    #         temp_var1_expr = re.sub(r'If\((.*),(0,1|1,0)\)', r'\1', temp_var1_expr)
    #         #去除"),0)"的",0"
    #         # temp_var1_expr = re.sub(r'\),0\)', ')\)', temp_var1_expr)
    #     temp_var1_expr = identity_sub(temp_var1_expr)
    #     # print("temp_var1_expr:",temp_var1_expr)
        
        
    #     for node_uid in range(self.uid-1, -1, -1): # 从当前节点往前找（uid是从1开始的）
    #         if nodes[node_uid].function_name != self.function_name:
    #             continue
    #         if node_uid >= self.uid:
    #             continue
    #         # print("node_uid:",node_uid)
    #         if nodes[node_uid].node_type == NodeType.ENTRY_OR_EXIT_POINT:
    #             continue
    #         if nodes[node_uid].node_type == NodeType.LOG_INFORMATION:
    #             # 不会做中间节点的node
    #             continue
    #         if nodes[node_uid].node_type == NodeType.DELETED: # 被删除的结点
    #             continue
    #         #不会出现的边情况
    #         if self.opcode == "SSTORE" and nodes[node_uid].opcode == "SSTORE":
    #             continue
    #         elif self.opcode == "SSTORE" and nodes[node_uid].opcode == "SLOAD":
    #             continue
    #         if nodes[node_uid].opcode == "SLOAD" or nodes[node_uid].opcode == "SSTORE": 
    #             try:
    #                 var1_expr = Node.get_last_bracket_content(PreProcExpr(str(nodes[node_uid].symbol_vars[1])))
    #             except Exception as e:
    #                 print("#ERROR:",self.function_name,"node",node_uid," symbol_vars[1] is empty")
    #                 continue
    #         else:
    #             try:
    #                 var1_expr = Node.get_last_bracket_content(PreProcExpr(str(nodes[node_uid].symbol_vars[0])))
    #             except Exception as e:
    #                 print("#ERROR:",self.function_name,"node",node_uid," symbol_vars[0] is empty")
    #                 continue
    #         var1_expr = re.sub(r'Extract\(\d+,\d+,', '', var1_expr)
    #         var1_expr = re.sub(r'If\((.*),(0,1|1,0)\)', r'\1', var1_expr)
    #         # var1_expr = re.sub(r'\),0\)', ')\)', var1_expr)
    #         var1_expr = identity_sub(var1_expr)
    #         # print("var1_expr:",var1_expr,"是否相等",var1_expr == temp_var1_expr)
    #         if var1_expr =="": #如果待检查前驱结点var1_expr为空
    #             print("ERROR: node",node_uid," var1_expr = ''")
    #             continue
    #         if self.opcode == "SHA3" and nodes[node_uid].opcode == "SHA3":
    #             if temp_var1_expr == var1_expr:
    #                 continue
    #         # elif ","+var1_expr in temp_var1_expr or "("+var1_expr in temp_var1_expr:
    #         # elif "("+var1_expr+"," in temp_var1_expr and self.opcode not in ["SSTORE"] \
    #         #     or var1_expr in temp_var1_expr and self.opcode == "SSTORE":
    #         elif "("+var1_expr in temp_var1_expr or ","+var1_expr in temp_var1_expr or var1_expr == temp_var1_expr:
    #             # print("type 1 node uid",self.uid)
    #             self.predecessors_list[0].append(node_uid)
    #             if ExitNode_uid in nodes[node_uid].successors:
    #                 nodes[node_uid].successors.remove(ExitNode_uid)
    #                 nodes[ExitNode_uid].predecessors_list[0].remove(node_uid)
    #             if self.uid not in nodes[node_uid].successors:
    #                 nodes[node_uid].successors.append(self.uid)
    #             # print("nodes[node_uid].predecessors_list:",nodes[node_uid].predecessors_list)
    #             # 去除匹配部分的剩余temp_var1_expr部分
    #             # print("temp_var1_expr:",temp_var1_expr)
    #             temp_var1_expr = temp_var1_expr.replace(var1_expr, '', 1)
    #             # print("-->:",temp_var1_expr)
    #             if self.opcode == "SLOAD": #SLOAD node的value来自于slot,同时可能来自前面的SSTORE
    #                 if var1_expr == temp_vars_expr[0] and nodes[node_uid].opcode == "SSTORE":
    #                     self.predecessors_list[1].append(node_uid)
    #                     if ExitNode_uid in nodes[node_uid].successors:
    #                         nodes[node_uid].successors.remove(ExitNode_uid)
    #                         nodes[ExitNode_uid].predecessors_list[0].remove(node_uid)
    #                     if self.uid not in nodes[node_uid].successors:
    #                         nodes[node_uid].successors.append(self.uid)
    #                     temp_vars_expr[0] = temp_vars_expr[0].replace(var1_expr, '', 1)
    #             else:
    #                 for i in range(len(temp_vars_expr)): 
    #                     # if var1_expr in temp_vars_expr[i]:
    #                     if "("+var1_expr in temp_vars_expr[i] or ","+var1_expr in temp_vars_expr[i] or var1_expr == temp_vars_expr[i]:
    #                         self.predecessors_list[i+1].append(node_uid)
    #                         if ExitNode_uid in nodes[node_uid].successors:
    #                             nodes[node_uid].successors.remove(ExitNode_uid)
    #                             nodes[ExitNode_uid].predecessors_list[0].remove(node_uid)
    #                         if self.uid not in nodes[node_uid].successors:
    #                             nodes[node_uid].successors.append(self.uid)
    #                         temp_vars_expr[i] = temp_vars_expr[i].replace(var1_expr, '', 1)
    #         elif self.opcode == "SLOAD":
    #             # slot不同,则sload的value不会来自此node
    #             pass
    #         else:
    #             for i in range(len(temp_vars_expr)):
    #                 # if ","+var1_expr in temp_vars_expr[i] or "("+var1_expr in temp_vars_expr[i]:
    #                 # if "("+var1_expr+"," in temp_vars_expr[i] and self.opcode != "SSTORE" \
    #                 #     or var1_expr in temp_vars_expr[i] and self.opcode == "SSTORE":
    #                 if "("+var1_expr in temp_vars_expr[i] or ","+var1_expr in temp_vars_expr[i] or var1_expr == temp_vars_expr[i]:
    #                     # print("type 2 node uid",self.uid)
    #                     self.predecessors_list[i+1].append(node_uid)
    #                     if ExitNode_uid in nodes[node_uid].successors:
    #                         nodes[node_uid].successors.remove(ExitNode_uid)
    #                         nodes[ExitNode_uid].predecessors_list[0].remove(node_uid)
    #                     if self.uid not in nodes[node_uid].successors:
    #                         nodes[node_uid].successors.append(self.uid)
    #                     temp_vars_expr[i] = temp_vars_expr[i].replace(var1_expr, '', 1)
    #             if temp_var1_expr == '' and all([temp_var_expr == "" for temp_var_expr in temp_vars_expr]):
    #                 break
    #     #调整顺序
    #     for i in range(len(self.predecessors_list)):
    #         if len(self.predecessors_list[i]) > 1:
    #             symbol_var_expr = self.symbol_vars_expr[i] #当前节点的symbol_var_expr
    #             # self.predecessors_list[i]按照其中元素index对应nodes[index].symbol_vars_expr[0]在symbol_var_expr中的顺序排序
    #             # print("predecessors_list[",i,"]:",self.predecessors_list[i])
    #             self.predecessors_list[i] = sorted(self.predecessors_list[i], key=lambda x: symbol_var_expr.find(nodes[x].symbol_vars_expr[0]))
    #             # print("sorted predecessors_list[",i,"]:",self.predecessors_list[i])
    #     return  
    
    # 基于CFG获取本节点所在分支（从start_uid以后）的所有结点，self必须是数据流（含sstore、sload、log）结点
    def get_path_nodes(self, nodes,start_uid=-1): 
        # 获取self对应的cfg_uid_info，查找前驱结点直到小于start_uid或为entry结点
        # print("uid",self.uid,"opcode",self.opcode)
        start_time = time.time()
        basic_block_uid = self.cfg_uid_info[0]
        res_nodes = []
        while nodes[basic_block_uid].node_type != NodeType.ENTRY_OR_EXIT_POINT and basic_block_uid > start_uid:
            res_nodes = nodes[basic_block_uid].cfg_uid_info + res_nodes
            if nodes[basic_block_uid].predecessors_list[0] != []:
                pre_basic_block_uid = nodes[basic_block_uid].predecessors_list[0][0]
            else:
                break
            if nodes[basic_block_uid].opcode == "JUMPDEST" and nodes[pre_basic_block_uid].opcode == "JUMPI": #跳过该JUMPI结点，因为此情况下存储的是另一条分支
                basic_block_uid = nodes[pre_basic_block_uid].predecessors_list[0][0]
            else:
                basic_block_uid = pre_basic_block_uid
        # print("basic_block_uid",basic_block_uid)
        res_nodes = nodes[basic_block_uid].cfg_uid_info + res_nodes #最后加上第一个基本块的结点
        #去除uid大于self.uid的，且交易id相同
        res_nodes = [uid for uid in res_nodes if uid < self.uid and nodes[uid].tx_id == self.tx_id]
        get_path_time = time.time()-start_time
        if get_path_time > 1:
            print("get_path_nodes time:",get_path_time)
        return res_nodes
        

    def find_edge(self,
                  nodes,
                  ExitNode_uid,
                  ):
        # 查找直接前驱结点
        
        if flag_time: # 计时
            # global find_edge_time
            start_time = time.time()
        
        
        if not nodes or \
            self.node_type in [NodeType.ENTRY_OR_EXIT_POINT,NodeType.ENVIRONMENT_CONTEXT,NodeType.DELETED,NodeType.UNKNOWN]:
            # 不需要查找直接前驱结点的情况
            return
        
        if self.node_type == NodeType.CONTROL_FLOW:
            ## 暂时没有处理的情况:CALL和JUMP等
            # 处理JUMPDEST节点：查找前驱结点
            if self.opcode == "JUMPDEST":
                # 查找前驱结点
                for node_uid in range(self.uid-1, -1, -1):
                    if nodes[node_uid].function_name != self.function_name:
                        continue
                    if nodes[node_uid].node_type == NodeType.DELETED:
                        continue
                    if nodes[node_uid].tx_id != self.tx_id:
                        continue
                    if nodes[node_uid].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                        continue
                    if nodes[node_uid].opcode == "JUMPI" and len(nodes[node_uid].successors) < 2 : # 避免两个JUMPDEST的错误情况?and nodes[nodes[node_uid].successors[0]].opcode != "JUMPDEST"
                        # print(self.uid,"###",nodes[node_uid].get_dict(),nodes[node_uid].successors)
                        if self.offset == nodes[node_uid].symbol_vars[0] \
                            or self.offset == nodes[node_uid].offset+1: # offset即JUMP/JUMPI的目标地址counter
                            self.predecessors_list[0].append(node_uid)
                            if ExitNode_uid in nodes[node_uid].successors:
                                nodes[node_uid].successors.remove(ExitNode_uid)
                                nodes[ExitNode_uid].predecessors_list[0].remove(node_uid)
                            if self.uid not in nodes[node_uid].successors:
                                nodes[node_uid].successors.append(self.uid)
                            # print("###2",nodes[node_uid].get_dict(),nodes[node_uid].successors)
                            break
                    elif nodes[node_uid].opcode == "JUMP" and len(nodes[node_uid].successors) == 1 and nodes[nodes[node_uid].successors[0]].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                        if self.offset == nodes[node_uid].symbol_vars[0]:
                            self.predecessors_list[0].append(node_uid)
                            if ExitNode_uid in nodes[node_uid].successors:
                                nodes[node_uid].successors.remove(ExitNode_uid)
                                nodes[ExitNode_uid].predecessors_list[0].remove(node_uid)
                            if self.uid not in nodes[node_uid].successors:
                                nodes[node_uid].successors.append(self.uid)
                            # # 删除JUMP及JUMPDEST节点
                            # Node.remove(self,nodes)
                            # Node.remove(nodes[node_uid],nodes)
                            break
                if self.node_type != NodeType.DELETED and not self.predecessors_list[0]:
                    # # 存在JMPDEST的不是第一个基本块的情况
                    # if self.offset !=self.state.node.states[0].get_current_instruction()['address']:
                    #     print("ERROR: JUMPDEST node",self.uid," has no predecessor1111")
                    #     self.predecessors_list[0].append(Node.find_cfg_start_node(self,nodes,ExitNode_uid)) 
                    # print(f"##ERROR: JUMPDEST node {self.uid} has no predecessor")
                    Node.remove(self,nodes) # 删除JUMPDEST节点:跨函数跳转的情况（如函数选择器）和非跳转顺序执行到JUMPDEST结点
                return
            elif self.opcode in ["JUMP","JUMPI"]:
                # 查询基本块对应的第一个结点(JUMPI或JUMPDEST)
                node_uid = Node.find_cfg_start_node(self,nodes,ExitNode_uid)
                # print("@@node_uid",self.uid,"->",node_uid)
                if nodes[node_uid].node_type == NodeType.ENTRY_OR_EXIT_POINT: #第一个基本块
                    self.predecessors_list[0].append(node_uid)
                    nodes[node_uid].successors.append(self.uid)
                else:
                    self.predecessors_list[0].append(node_uid)
                    if ExitNode_uid in nodes[node_uid].successors:
                        nodes[node_uid].successors.remove(ExitNode_uid)
                        nodes[ExitNode_uid].predecessors_list[0].remove(node_uid)
                    if self.uid not in nodes[node_uid].successors:
                        nodes[node_uid].successors.append(self.uid)
                return
            elif self.opcode in ["CALL","DELEGATECALL"]:
                pass #TODO
            else:
                # 暂时不处理的情况
                return
            return
        
        if self.symbol_vars.count == 0:
            # 该结点无符号变量，无法查找前驱结点
            print("ERROR: node",self.uid," symbol_vars.count == 0")
            return
        
        # 过滤掉掩码
        if flag_time: # 计时
            print("### time ",time.time()-start_time)
        if self.opcode in ["AND","OR"] and len(self.symbol_vars) > 1:
            # self.symbol_vars = [var for var in self.symbol_vars if str(var) not in ["1461501637330902918203684832716283019655932542975","1461501637330902918203684832716283019655932542976-1"]]
            # 增加条件，检查var.raw.size()是否小于等于1024
            # self.symbol_vars = [var for var in self.symbol_vars if str(var.raw) not in ["1461501637330902918203684832716283019655932542975","1461501637330902918203684832716283019655932542976-1"]]
            # def filter_symbol_vars(symbol_vars):
            #     return [var for var in symbol_vars if str(var.raw) not in ["1461501637330902918203684832716283019655932542975", "1461501637330902918203684832716283019655932542976-1"]]
            
            
            self.symbol_vars_expr = []
            for symbol_var in self.symbol_vars:
                try:
                    symbol_var_expr = filter_symbol_var(symbol_var)
                    if symbol_var_expr == "":
                        continue
                    self.symbol_vars_expr.append(symbol_var_expr)
                except TimeoutException:
                    print("Mask filter execution exceeded 0.1 seconds, skipping the statement.")
                except Exception as e:
                    print(f"ERORR：An unexpected error occurred: {e}")
                finally:
                    pass
      
            # try:
            #     self.symbol_vars_expr = filter_symbol_vars(self.symbol_vars)
            #     if isinstance(self.symbol_vars, TimeoutException):
            #         print("Mask filter execution exceeded 0.1 seconds, skipping the statement.")
            # except TimeoutException:
            #     print("Mask filter execution exceeded 0.1 seconds, skipping the statement.")
        if flag_time: # 计时
            print("### time2 ",time.time()-start_time) 
        
        ## 首先使用添加相等约束的方法查找前驱结点（除SHA3结点外）
        if self.node_type == NodeType.STATE_VARIABLES:
            slot_predecessor = -1 # slot的前驱结点
            value_predecessor = -1 # value的前驱结点
            # SLOAD的slot来自于SHA3，value不来自SHA3和control flow、log infomation类结点:
            # SSTORE的slot来自于SHA3，value不来自SHA3和control flow、log infomation类结点
            # print(f"self.uid:{self.uid} path :{self.get_path_nodes(nodes)}")
            # 逆序遍历self.get_path_nodes(nodes)
            for node_uid in reversed(self.get_path_nodes(nodes)):
            # for node_uid in range(self.uid-1, -1, -1):
                if nodes[node_uid].function_name != self.function_name:    
                    continue # 暂时只处理本函数内的结点
                if nodes[node_uid].tx_id != self.tx_id:
                    continue # 暂时只处理同一交易的结点
                if node_uid >= self.uid:# 避免前驱指向自己                        
                    continue
                if nodes[node_uid].node_type == NodeType.DELETED: # 被删除的结点
                    continue
                if nodes[node_uid].node_type in [NodeType.ENTRY_OR_EXIT_POINT,NodeType.LOG_INFORMATION,NodeType.CONTROL_FLOW]: #SSTORE只可能是SLOAD的直接前驱结点
                    continue # 不可能是前驱结点的情况，直接跳过
                if len(nodes[node_uid].symbol_vars) == 0: # 无符号变量的结点（说明未初始化的posthook节点）
                    continue
                
                #slot的前驱结点:可能为SHA3或ADD（结构体）节点
                if slot_predecessor == -1:
                    if nodes[node_uid].opcode == "SHA3": # 一维映射和n维映射
                        # print("node_uid",node_uid)
                        # print("self.symbol_var_equal(self.symbol_vars[0], nodes[node_uid].symbol_vars[0])",self.symbol_var_equal(self.symbol_vars[0], nodes[node_uid].symbol_vars[0]))
                        if self.symbol_var_equal(self.symbol_vars[0], nodes[node_uid].symbol_vars[0]):
                            slot_predecessor = node_uid
                        if slot_predecessor != -1 and value_predecessor != -1:
                                break
                    elif nodes[node_uid].opcode == "ADD": # 结构体
                        if self.symbol_var_equal(self.symbol_vars[0], nodes[node_uid].symbol_vars[0]):
                            slot_predecessor = node_uid
                        if slot_predecessor != -1 and value_predecessor != -1:
                                break
                    elif nodes[node_uid].opcode == "OR": #trick:处理空投时发现部分SSTORE的slot可能来自OR节点
                        if self.symbol_var_equal(self.symbol_vars[0], nodes[node_uid].symbol_vars[0]):
                            slot_predecessor = node_uid
                        if slot_predecessor != -1 and value_predecessor != -1:
                                break
                    elif nodes[node_uid].node_type in [NodeType.ENTRY_OR_EXIT_POINT,NodeType.LOG_INFORMATION,NodeType.CONTROL_FLOW] \
                        or nodes[node_uid].opcode == self.opcode:
                        # 不可能是前驱结点的情况，直接跳过（Entry结点的直接后继不需要使用该函数查找）
                        continue
                #value的前驱结点
                if value_predecessor == -1:
                    if self.opcode == "SLOAD": # SLOAD论文的value直接来自于storage，可能来自之前的SSTORE
                        if nodes[node_uid].opcode == "SSTORE":
                            # 当且仅当slot和value都来自SLOAD时，才认为是value的前驱结点
                            if self.symbol_var_equal(self.symbol_vars[0], nodes[node_uid].symbol_vars[0]) \
                                and self.symbol_var_equal(self.symbol_vars[1], nodes[node_uid].symbol_vars[1]):
                                value_predecessor = node_uid
                        else: #来自storage的符号变量
                            pass 
                    elif self.opcode == "SSTORE":
                        # # 检查如果value为[slot]，则不查找前驱结点
                        # if not hasattr(self, "symbol_vars_expr"): # 检查self是否有self.symbol_vars_expr属性
                        #     self.symbol_vars_expr = [Node.get_last_bracket_content(PreProcExpr(str(var))) for var in self.symbol_vars] 
                        # if self.symbol_vars_expr[1] == "["+self.symbol_vars_expr[0]+"]": # tricke解决硬编码误报：value为[slot],没有发生变化，无value的前驱结点
                        #     print("WARNING:self.symbol_vars_expr[1] == [self.symbol_vars_expr[0]]")
                        #     continue
                        #value的前驱结点
                        if nodes[node_uid].opcode == "SLOAD": #SSTORE的value直接来自于SLOAD
                            if len(nodes[node_uid].symbol_vars) > 1 and self.symbol_var_equal(self.symbol_vars[1], nodes[node_uid].symbol_vars[1]):
                                value_predecessor = node_uid
                        else:
                            # for symbol_var in nodes[node_uid].symbol_vars:
                            if nodes[node_uid].opcode == "SSTORE" and self.symbol_var_equal(self.symbol_vars[0], nodes[node_uid].symbol_vars[0]):
                                pass # SSTORE的value不来自于相同slot的SSTORE
                            else:
                                for i in range(len(nodes[node_uid].symbol_vars)):
                                    if self.symbol_var_equal(self.symbol_vars[1], nodes[node_uid].symbol_vars[i]):
                                        value_predecessor = node_uid
                if slot_predecessor != -1 and value_predecessor != -1:
                    break
            if slot_predecessor != -1:
                self.predecessors_list[0].append(slot_predecessor)
                if ExitNode_uid in nodes[slot_predecessor].successors:
                    nodes[slot_predecessor].successors.remove(ExitNode_uid)
                    nodes[ExitNode_uid].predecessors_list[0].remove(slot_predecessor)
                if self.uid not in nodes[slot_predecessor].successors:
                    nodes[slot_predecessor].successors.append(self.uid)
            if value_predecessor != -1:
                self.predecessors_list[1].append(value_predecessor)
                if ExitNode_uid in nodes[value_predecessor].successors:
                    nodes[value_predecessor].successors.remove(ExitNode_uid)
                    nodes[ExitNode_uid].predecessors_list[0].remove(value_predecessor)
                if self.uid not in nodes[value_predecessor].successors:
                    nodes[value_predecessor].successors.append(self.uid)               
        elif self.node_type in [NodeType.DATA_FLOW,NodeType.LOG_INFORMATION]:
            # 除SHA3外,一个symbol_var的只有一个前驱结点
            if self.opcode == "SHA3":
                # 暂时使用原方法
                # self.find_edge2(nodes,ExitNode_uid)
                self.find_SHA3_edge(nodes,ExitNode_uid) #trick:只处理ADD、SHA3、AND操作码，提取为字符串，以减少耗时
                #TODO 字符串处理
                pass # TODO：同时注意顺序
            else:
                time_count = 0
                
                start_time = time.time()
                # for node_uid in range(self.uid-1, -1, -1):
                for node_uid in reversed(self.get_path_nodes(nodes)):
                    if nodes[node_uid].function_name != self.function_name:
                        continue # 暂时只处理本函数内的结点
                    if nodes[node_uid].tx_id != self.tx_id:
                        continue # 暂时只处理同一交易的结点
                    if node_uid >= self.uid:# 避免前驱指向自己
                        continue
                    if nodes[node_uid].node_type in [NodeType.ENTRY_OR_EXIT_POINT,NodeType.LOG_INFORMATION,NodeType.CONTROL_FLOW]\
                        or nodes[node_uid].opcode == "SSTORE": #SSTORE只可能是SLOAD的直接前驱结点
                        continue # 不可能是前驱结点的情况，直接跳过
                    if nodes[node_uid].node_type == NodeType.DELETED: # 被删除的结点
                        continue
                    # 查找前驱结点
                    for i in range(len(self.symbol_vars)): # 遍历本结点所有的symbol_var
                        if self.predecessors_list[i] != []:
                            continue # 该symbol_var已经找到前驱结点
                        # for symbol_var in nodes[node_uid].symbol_vars: 
                        for j in range(len(nodes[node_uid].symbol_vars)):
                            time_count+=1
                            if self.symbol_var_equal(self.symbol_vars[i], nodes[node_uid].symbol_vars[j]):
                                self.predecessors_list[i].append(node_uid)
                                if ExitNode_uid in nodes[node_uid].successors:
                                    nodes[node_uid].successors.remove(ExitNode_uid)
                                    nodes[ExitNode_uid].predecessors_list[0].remove(node_uid)
                                if self.uid not in nodes[node_uid].successors:
                                    nodes[node_uid].successors.append(self.uid)
                                break # 每个符号变量找到一个前驱结点即可
                if self.opcode in ["AND","OR"]: # 关注的情况是只有一个前驱结点
                    # print("reversed(self.get_path_nodes(nodes))",list(reversed(self.get_path_nodes(nodes))))
                    # 去除为空的list
                    # self.predecessors_list = [predecessor for predecessor in self.predecessors_list if predecessor != []]
                    if self.predecessors_list[0] == [] and self.predecessors_list[1] == []:
                        self.predecessors_list = []
                    elif self.predecessors_list[0] == []:
                        self.predecessors_list = [self.predecessors_list[1]]
                        self.symbol_vars = [self.symbol_vars[1]]
                    elif self.predecessors_list[1] == []:
                        self.predecessors_list = [self.predecessors_list[0]]
                        self.symbol_vars = [self.symbol_vars[0]]
                if flag_time:
                    end_time = time.time()
                    if end_time - start_time > 1:
                        print("find_edge time:",end_time - start_time,"time_count",time_count)       
        else:
            print("ERROR: node",self.uid," unhandle node_type : ",self.node_type)
        
        if flag_time:
            if self.opcode not in Node.find_edge_time:
                Node.find_edge_time[self.opcode] = (time.time() - start_time)
            Node.find_edge_time[self.opcode] += (time.time() - start_time)
            print("##find_edge time:",time.time() - start_time)
                
            # Node.find_edge_time += (time.time() - start_time)
        return
        
            
        
            
    def remove(self, nodes): #移除该节点
        print("remove node:",self.uid,self.opcode)           
        # print("remove",self.uid,self.opcode)
        # Remove this node from its successors' predecessor lists
        for successor_id in self.successors:
            # nodes[successor_id].predecessors.remove(self.uid)
            for i in range(len(nodes[successor_id].predecessors_list)):
                if self.uid in nodes[successor_id].predecessors_list[i]:
                    nodes[successor_id].predecessors_list[i].remove(self.uid)
        
        # Clear this node's predecessor and successor lists
        self.predecessors_list = [] 
        self.successors = []

        # Finally, remove this node from the nodes dictionary
        self.node_type = NodeType.DELETED
        # del nodes[self.uid]
        # Node.count -= 1
        # Node.cur_pc -= 1
    
    # trick解决：该问题导致的误报主要是SSTORE的直接前驱ADD或SUB节点A的前驱节点错误，则如果A的节点值为0，则查找数据源节点前进行修正，更新前驱为与SSTORE节点的slot相同的SLOAD节点的值
    def fix_sstore_prepredecessors(nodes,uid:int,limit:int=2000):
        #因为使用的是队列，所以顺序是由右到左;uids时var i的直接前驱数组
        if nodes[uid].opcode != "SSTORE":
            print("ERROR:fix_sstore_prepredecessors node",uid,"is not SSTORE")
            return
        if len(nodes[uid].predecessors_list) != 2\
            or len(nodes[uid].predecessors_list[0]) != 1\
            or len(nodes[uid].predecessors_list[1]) != 1:
            return
        pre_node = nodes[nodes[uid].predecessors_list[1][0]]
        if pre_node.opcode not in ["ADD","SUB"]:
            return
        # for predecessors in pre_node.predecessors_list: #ADD或SUB节点的前驱结点至多有两个
        #     for prepre_uid in predecessors:
        #         if nodes[prepre_uid].opcode == "SLOAD" \
        #         and nodes[prepre_uid].symbol_vars[0] != nodes[uid].symbol_vars[0]\
        #         and str(nodes[prepre_uid].symbol_vars[1]) == "0":
        for i in range(len(pre_node.predecessors_list)):
            for j in range(len(pre_node.predecessors_list[i])):
                prepre_uid = pre_node.predecessors_list[i][j]
                if nodes[prepre_uid].opcode == "SLOAD" \
                and nodes[prepre_uid].symbol_vars[0] != nodes[uid].symbol_vars[0]\
                and str(nodes[prepre_uid].symbol_vars[1]) == "0":
                    # 删除错误的前驱节点
                    # pre_node.predecessors_list[i].remove(prepre_uid)
                    # 更新前驱节点
                    for k in range(uid-1, -1, -1):
                        if nodes[k].opcode == "SLOAD" and nodes[k].symbol_vars[0] == nodes[uid].symbol_vars[0] and str(nodes[k].symbol_vars[1]) == "0":
                            pre_node.predecessors_list[i][j] = k
                            if uid not in nodes[k].successors:
                                print("WARNING:trick fix_sstore_prepredecessors node",pre_node.uid,"prepre_uid",prepre_uid,"symbol_vars[0]",nodes[prepre_uid].symbol_vars[0])
                                nodes[prepre_uid].successors.remove(pre_node.uid)
                                nodes[k].successors.append(uid)
                            break
                    print("WARNING:trick fix_sstore_prepredecessors node",pre_node.uid,"prepre_uid",prepre_uid,"symbol_vars[0]",nodes[prepre_uid].symbol_vars[0])
                    
        

    def find_start_node_ids(nodes, uids: list[int], limit: int=2000,ret_SHA3_count: bool=False,ret_sload_count: bool=False) -> List[int]:
        if flag_time:
            global find_start_nodes_time
            start_time = time.time()
        #因为使用的是队列，所以顺序是由右到左;uids时var i的直接前驱数组
        if ret_SHA3_count:
            SHA3_node_uids = []
        if ret_sload_count: # 统计遇到的SLOAD结点数量
            sload_count = 0
        start_node_ids = set()
        visited = set()
        queue = deque(uids)
        queue.append(-1) #代表该循环完毕
        count = 0

        while queue:
            count += 1
            if count > limit: #防止死循环
                print("ERROR:Exceeded maximum number of iterations.")
                break
            current_uid = queue.popleft()
            if ret_SHA3_count and current_uid != -1 and nodes[current_uid].opcode == "SHA3":
                if current_uid not in SHA3_node_uids:
                    SHA3_node_uids.append(current_uid)
            if current_uid == -1:
                # 当queue中只剩下start_node_ids时，结束循环
                if set(queue).issubset(start_node_ids):
                    break
                else: #下一轮循环
                    queue.append(-1)
                    continue
            current_node = nodes[current_uid]
            if current_uid in visited:
                if current_uid in start_node_ids:
                    queue.append(current_uid)

                continue

            visited.add(current_uid)

            
            if current_node.node_type in [NodeType.ENTRY_OR_EXIT_POINT,NodeType.LOG_INFORMATION]:
                continue
            if len(current_node.predecessors_list) == 1 and len(current_node.predecessors_list[0]) ==1 and nodes[current_node.predecessors_list[0][0]].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                start_node_ids.add(current_uid)
                queue.append(current_uid)
                if len(start_node_ids) >= limit:
                    print("ERROR:Reached limit of", limit, "start nodes.")
                    break
            # 处理起始结点
            if len(current_node.predecessors_list) == 1 and len(current_node.predecessors_list[0]) == 0:
                start_node_ids.add(current_uid)
                queue.append(current_uid)
                # print("hard code node",current_uid)
                continue
            
            # SLOAD处理
            if current_node.opcode == "SLOAD":
                if ret_sload_count:
                    sload_count += 1
                if len(current_node.predecessors_list) == 2 and current_node.predecessors_list[1] :
                    # value有前驱节点，则将直接前驱SLOAD的value的前驱节点加入queue
                    sstore_node=nodes[current_node.predecessors_list[1][0]]
                    for predecessor_uid in sstore_node.predecessors_list[1]:
                        queue.append(predecessor_uid)
                else:
                    # value没有前驱节点，则将slot的前驱节点加入queue
                    for predecessor_uid in current_node.predecessors_list[0]:
                        queue.append(predecessor_uid)
                pass
            elif current_node.opcode == "AND":
                if len(current_node.predecessors_list) == 1:
                    for predecessor_uid in current_node.predecessors_list[0]:
                        queue.append(predecessor_uid)
                elif len(current_node.predecessors_list) == 2:
                    for predecessor_uid in current_node.predecessors_list[0]:
                        queue.append(predecessor_uid)
                    for predecessor_uid in current_node.predecessors_list[1]:
                        queue.append(predecessor_uid)
            else:#TODO 检测是否存在问题
                # for predecessor_uid in current_node.predecessors_list[0]:
                #     queue.append(predecessor_uid)
                for i in range(len(current_node.predecessors_list)):
                    for predecessor_uid in current_node.predecessors_list[i]:
                        queue.append(predecessor_uid)

        if flag_time:
            Node.find_start_nodes_time += (time.time() - start_time)
        if ret_SHA3_count:
            return list(start_node_ids),SHA3_node_uids
        if ret_sload_count:
            return list(start_node_ids),sload_count
        else:
            return list(queue)

    #检查当前函数，记录相邻的JUMP/JUMPI+JUMPDEST操作码，如果存在offset一致的两组（默认循环次数限制为3次），则视为发生循环
    def detect_loops_test(self,nodes): #TEST：查找从最长分支是否存在循环 #TODO 删除该函数
        start_time = time.time()
        cfg_path_uids = {} # 记录该分支从entry节点开始，经过的所有cfg节点offset:[uids]
        cfg_path_uids2 = {}
        cfg_node = self
        while cfg_node.node_type == NodeType.DELETED:
            cfg_node=nodes[cfg_node.uid-1]
        if cfg_node.node_type != NodeType.CONTROL_FLOW:
            cfg_node = nodes[self.cfg_uid_info[0]]
        pre_cfg_node = nodes[cfg_node.predecessors_list[0][0]]
        # if cfg_node.opcode == "JUMPDEST" and pre_cfg_node.opcode == "JUMPI":
        #     cfg_path_uids[cfg_node.offset] = [cfg_node.uid]
        #     cfg_node = nodes[cfg_node.predecessors_list[0][0]]
        # pre_cfg_node = nodes[cfg_node.predecessors_list[0][0]]
        while cfg_node.node_type != NodeType.ENTRY_OR_EXIT_POINT and pre_cfg_node.node_type != NodeType.ENTRY_OR_EXIT_POINT:
            if cfg_node.opcode == "JUMPDEST" and pre_cfg_node.opcode == "JUMPI":
                cfg_path_uids[cfg_node.offset] = cfg_path_uids.get(cfg_node.offset,[]) + [cfg_node.uid]
                cfg_node = pre_cfg_node
            elif cfg_node.opcode == "JUMPDEST" and pre_cfg_node.opcode == "JUMP":
                cfg_path_uids2[cfg_node.offset] = cfg_path_uids2.get(cfg_node.offset,[]) + [cfg_node.uid]
                cfg_node = pre_cfg_node
            # print(f"cfg_node",cfg_node.uid)
            cfg_node = nodes[cfg_node.predecessors_list[0][0]]
            if cfg_node.node_type == NodeType.ENTRY_OR_EXIT_POINT:
                break # entry结点
            if cfg_node.predecessors_list[0] != []:
                pre_cfg_node = nodes[cfg_node.predecessors_list[0][0]]
            else:
                break
            
        print("cfg_path_uids(JUMPI)",cfg_path_uids)
        print("cfg_path_uids2(JUMP)",cfg_path_uids2)
        print("detect_loops time:",time.time() - start_time)
        
        pass
        #返回循环的起止结点
    
    @staticmethod
    def detect_path_loops(nodes,func_name,cfg_path_uids,ret_loop_cfg_uids=False): # 检测单个函数的单个分支路径中是否存在循环
        cfg_path_uids_offset = {}
        if len(cfg_path_uids) < 2:
            if not ret_loop_cfg_uids:
                print("# detect_path_loops cfg_path_uids length < 2")
                return False
            else:
                print("# cfg_path_uids",cfg_path_uids)
                print("# detect_path_loops cfg_path_uids length < 2")
                return None,None
        # 遍历cfg_path_uids路径，如果存在循环（记录相邻的JUMP/JUMPI+JUMPDEST操作码）则返回True
        for i in range(len(cfg_path_uids)-1):
            pre_cfg_node = nodes[cfg_path_uids[i]]
            cfg_node = nodes[cfg_path_uids[i+1]]
            if cfg_node.opcode == "JUMPDEST" and pre_cfg_node.opcode == "JUMPI":
            # if cfg_node.opcode == "JUMPDEST" and pre_cfg_node.opcode in ["JUMP","JUMPI"]:
                cfg_path_uids_offset[cfg_node.offset] = cfg_path_uids_offset.get(cfg_node.offset,[]) + [cfg_node.uid]
        print("cfg_path_uids_offset",cfg_path_uids_offset)
        # 如果存在offset一致的两组（默认循环次数限制为3次，我们设置--loop-bound 4），（超过两次）则视为发生循环
        if not ret_loop_cfg_uids:
            for offset in cfg_path_uids_offset:
                # if len(cfg_path_uids_offset[offset]) == 2:
                #     print("len(cfg_path_uids_offset[offset]) == 2 detect_path_loops",func_name,cfg_path_uids_offset,"cfg_path_uids",cfg_path_uids)
                #     return False
                if len(cfg_path_uids_offset[offset]) > 2:
                    print("detect_path_loops",func_name,cfg_path_uids_offset,cfg_path_uids)
                    return True
            return False
        else:
            # 获取循环的起止结点
            loop_uids_list = []
            for offset in cfg_path_uids_offset:
                if len(cfg_path_uids_offset[offset]) > 2:
                    loop_uids_list = loop_uids_list + cfg_path_uids_offset[offset]
            if len(loop_uids_list) <= 2:
                print("loop_uids_list",loop_uids_list)
                return None,None
            # 获取loop_uids_list的最大值和最小值
            loop_uids_list.sort()
            flag_transfer = False
            max_uid = loop_uids_list[-1]
            min_uid = loop_uids_list[0]
            return min_uid,max_uid
    
    ###  检测空投行为            
                
    @staticmethod   
    def detect_loops(nodes):# 检测存在循环结构的函数
        #TODO：分函数记录，检测循环结构，返回存在循环结构的函数名（先检测循环结构再检测存在核心结构的循环结构，逐步分析，避免遗漏）
        func_name_list = []
        res_func_cfg_uids = {}
        res_func_paths = {}
        # 遍历nodes获取所有函数名
        func_names = set()
        for node in nodes.values():
            if node.function_name != "" and node.function_name != "fallback":
                func_names.add(node.function_name)
        # 依次获取每个函数路径（get_all_path），只要有一个路径存在循环则认为该函数存在循环，返回函数名及其所有路径
        for func_name in func_names:
            # 排除掉常见的不是空投函数的情况，主要是transfer和transferfrom函数
            if any([not_airdrop in func_name for not_airdrop in not_airdrop_list]):
                continue
            flag_loop = False
            cfg_path_uids_dict,path_uids_list = Node.get_all_path(nodes,func_name) #path_uids_list：[[uid,...],...]，该路径上所有业务图（数据源节点、数据流结点和STATE类结点）结点ID
            for cfg_path_uids in cfg_path_uids_dict.values():
                # print("path_uids",cfg_path_uids)
                if Node.detect_path_loops(nodes,func_name,cfg_path_uids):
                    flag_loop = True
                    break
            if flag_loop:
                func_name_list.append(func_name)
                res_func_cfg_uids[func_name] = cfg_path_uids_dict
                res_func_paths[func_name] = path_uids_list
        # print("res_func_paths",res_func_paths)
        if flag_detailed:
            print("# detect_loops func_paths:",len(func_name_list))
            for func_name in func_name_list:
                print(func_name,res_func_cfg_uids[func_name])
        return func_name_list,res_func_cfg_uids,res_func_paths
    
    # 输入函数的路径，判断该路径是否存在循环体，且循环体中包含transfer
    @staticmethod
    def detect_transfer_in_path(nodes,func_name,func_cfg_uids,func_path):
        cfg_start,cfg_end = Node.detect_path_loops(nodes,func_name,func_cfg_uids,True)
        if flag_detailed:
            print(">> detect_transfer_in_path(cfg_start,cfg_end): ",cfg_start,cfg_end)
        if cfg_start == None or cfg_end == None:
            return False
        # func_cfg_uids中循环结构为cfg_start,cfg_end之间的结点
        func_cfg_uids = [func_cfg_uid for func_cfg_uid in func_cfg_uids if func_cfg_uid >= cfg_start and func_cfg_uid <= cfg_end]
        # 检测循环结构是否包含Call调用函数签名为transfer(from)的结点或包含balance结构
        for cfg_uid in func_cfg_uids:
            for node_uid in nodes[cfg_uid].cfg_uid_info:
                if nodes[node_uid].opcode in ["CALL","DELEGATECALL"]:
                    if hasattr(nodes[node_uid], 'value') and nodes[node_uid].value != "0":
                        return True
                    if hasattr(nodes[node_uid], 'call_func_signature') and nodes[node_uid].call_func_signature is None: # 调用transfer函数
                        print("     ERROR:CALL node",node_uid,"call_func_signature is None")
                        print(" 3.continue 0")
                        continue
                    if nodes[node_uid].call_func_signature in [FuncHash.TRANSFER,FuncHash.TRANSFER_FROM]:
                        if flag_detailed:
                            print(" 3.return True")
                            print("     nodes[node_uid].call_func_signature",nodes[node_uid].call_func_signature)
                        return True
                elif nodes[node_uid].opcode in ["SSTORE"]: #_balances[recipient] += amount;
                    slot_start_nodes_ids = Node.find_start_node_ids(nodes,nodes[node_uid].predecessors_list[0])
                    value_start_nodes_ids = Node.find_start_node_ids(nodes,nodes[node_uid].predecessors_list[1])
                    print("     nodes[node_uid].opcode",nodes[node_uid].uid,",symbol_var_exrps:",nodes[node_uid].symbol_vars_expr)
                    print("     slot_start_nodes_ids",slot_start_nodes_ids)
                    print("     value_start_nodes_ids",value_start_nodes_ids)
                    # if len(slot_start_nodes_ids) == 1 \
                    #     and check_roles(nodes[slot_start_nodes_ids[0]].symbol_vars_expr[0],Role.PARAM):  #_balances[recipient],判断：slot来自参数
                    #     print(" 3.return True")
                    #     return True
                    # if len(slot_start_nodes_ids) == 1 \
                    #     and nodes[slot_start_nodes_ids[0]].opcode == "CALLDATALOAD":  #_balances[recipient],判断：slot来自参数
                    #     print(" 3.slot OK")
                    #     #value中包含加法
                    #     value_predecessor_list = nodes[node_uid].predecessors_list[1]
                    #     if check_opcode(nodes,value_predecessor_list,"ADD"):
                    #         print(" 3.return True")
                    #         return True
                    # # elif len(slot_start_nodes_ids) == 2 \
                    # #     and check_roles(nodes[slot_start_nodes_ids[0]].symbol_vars_expr[0],Role.PARAM) \
                    # #     and check_roles(nodes[slot_start_nodes_ids[1]].symbol_vars_expr[0],Role.PARAM):
                    # #     print(" 3.return True:ERC1155")
                    # #     return True
                    # elif len(slot_start_nodes_ids) == 2 \
                    #     and nodes[slot_start_nodes_ids[0]].opcode in "CALLDATALOAD" \
                    #     and nodes[slot_start_nodes_ids[1]].opcode in "CALLDATALOAD":
                    #     # value中包含加法
                    #     print(" 3.slot OK2")
                    #     value_predecessor_list = nodes[node_uid].predecessors_list[1]
                    #     if check_opcode(nodes,value_predecessor_list,"ADD"):
                    #         print(" 3.return True")
                    #         return True
                    for i in range(len(slot_start_nodes_ids)):
                        if nodes[slot_start_nodes_ids[i]].opcode == "CALLDATALOAD":
                            print(" 3.slot OK")
                            value_predecessor_list = nodes[node_uid].predecessors_list[1]
                            if check_opcode(nodes,value_predecessor_list,"ADD"):
                                print(" 3.return True")
                                return True
                            else:
                                break
                    # print(" 3.continue 2","len(value_start_nodes_ids)=",len(value_start_nodes_ids),"check_opcode(ADD)",check_opcode(nodes,value_start_nodes_ids,"ADD"))
                    print(" 3.continue 1")
                    continue
                elif nodes[node_uid].opcode in ["LOG"]:
                    print(" 3.return True:LOG")
                    return True
        return False
        
       
    #TODO:检测空投函数=存在循环结构，且循环结构中存在SSTORE结点（tranfer或tranferfrom） ,如果是直接修改balance返回核心结构对应identity            
    @staticmethod
    def detect_transfer_in_loop(nodes,func_name_list,func_cfg_uids,func_paths):
        res_func_name_list = []
        for func_name in func_name_list: #检测每个函数
            if flag_detailed:
                print("> function",func_name,"detect_transfer_in_loop <") 
            #func_cfg_uids[func_name].values(),func_paths[func_name]是对应一一关系
            func_cfg_uids_list = list(func_cfg_uids[func_name].values())
            for i in range(len(func_cfg_uids_list)): # 检测函数的每条路径
                if flag_detailed:
                    print(">> function",func_name,"path",i)
                # print("func_cfg_uids_list",func_cfg_uids_list)
                # print("func_paths",func_paths[func_name][i])
                # 1.首先检测路径是否存在循环: 排除没有循环的函数
                if not Node.detect_path_loops(nodes,func_name,func_cfg_uids_list[i]):
                    if flag_detailed:
                        print(" 1.路径不存在循环")
                    continue
                # 2.检测函数路径中是否存在SSTORE结点或CALL/DELEGATECALL结点
                flag_sstore_or_call = False
                for uid in func_paths[func_name][i]:
                    if nodes[uid].opcode in ["SSTORE"]:
                        if flag_detailed:
                            print(" 2.存在SSTORE结点",uid)
                        # print("detect_transfer_in_loop",func_name,func_cfg_uids_list[i])
                        flag_sstore_or_call = True
                        break
                    elif nodes[uid].opcode in ["CALL","DELEGATECALL"]:
                        if flag_detailed:
                            print(" 2.存在CALL结点",uid)
                        flag_sstore_or_call = True
                        break
                    elif nodes[uid].opcode.startswith("LOG"):
                        if flag_detailed:
                            print(" 2.存在LOG结点",uid)
                        flag_sstore_or_call = True
                        break
                if not flag_sstore_or_call:
                    if flag_detailed:
                        print(" 2.不存在SSTORE或CALL、LOG结点")
                    continue
                # 3.检测是否存在_balances[recipient] += amount;结构或CALL调用token.transfer(from)或CALL的value不为0
                if Node.detect_transfer_in_path(nodes,func_name,func_cfg_uids_list[i],func_paths):
                    res_func_name_list.append(func_name)
                    break
        print("detect_transfer_in_loop res_func_name_list",res_func_name_list)
        return res_func_name_list #TODO 对于直接修改balance的类型
    
    #TODO：检测空投行为的正确性，三种类型：
    def detect_airdrop_correctness(nodes,func_name_list,func_cfg_uids,func_paths):
        print("----detect_airdrop_correctness----")
        issues = []
        # 1.跨合约调用transfer或transferFrom，token.transferFrom(msg.sender, _addresses[i], _amounts[i]);
        # 2.发送ETH空投，_addresses[i].call{value: _amounts[i]}("")
        # 3.直接修改balance
        for func_name in func_name_list: #检测每个函数
            print("> airdrop function",func_name," event correctness checking ... <") 
            #func_cfg_uids[func_name].values(),func_paths[func_name]是对应一一关系
            func_cfg_uids_list = list(func_cfg_uids[func_name].values())
            for i in range(len(func_cfg_uids_list)): # 检测函数的每条路径
                # print(">> function",func_name,"path",i)
                # 1.首先检测路径是否存在循环: 排除没有循环的函数
                if not Node.detect_path_loops(nodes,func_name,func_cfg_uids_list[i]):
                    continue
                # 2.检测函数路径中是否存在SSTORE结点或CALL/DELEGATECALL结点
                flag_sstore_or_call = False
                for uid in func_paths[func_name][i]:
                    if nodes[uid].opcode in ["SSTORE"]:
                        print(" 2.存在SSTORE结点",uid)
                        # print("detect_transfer_in_loop",func_name,func_cfg_uids_list[i])
                        flag_sstore_or_call = True
                        break
                    elif nodes[uid].opcode in ["CALL","DELEGATECALL"]:
                        print(" 2.存在CALL结点",uid)
                        flag_sstore_or_call = True
                        break
                    # elif nodes[uid].opcode.startswith("LOG"):
                    #     print(" 2.存在LOG结点",uid)
                    #     flag_sstore_or_call = F
                    #     break
                # state获取该路径最后一个节点的state
                state = nodes[func_paths[func_name][i][-1]].state
            if not flag_sstore_or_call:
                print("ERROR: airdrop only event log, no SSTORE or CALL/DELEGATECALL")
                description_head = "AirDrop function only event log"
                description = f"AirDrop function only event log, no SSTORE or CALL/DELEGATECALL"
                issue = ret_issues(state,description_head=description_head, description_tail=description)
                issues.append(issue)
                continue
        if issues:
            # 如果存在只有event log的空投函数，则直接返回
            print("----detect_airdrop_correctness end----")
            return issues
        # 进一步检查正确性，检查权限是否正确
        for func_name in func_name_list: #检测每个函数
            print("> airdrop function",func_name," authorisation correctness checking ... <") 
            flag_correctness = True
            # 确保 func_name 存在于 func_cfg_uids 字典中
            if func_name not in func_cfg_uids:
                continue
            #
            # 检查是否对msg.sender进行了限制
            # state = copy(nodes[func_paths[func_name][i][-1]].state)
            # 从后向前遍历，找到最后一个SSTORE、CALL、DELEGATECALL结点
            func_cfg_uids_list = list(func_cfg_uids[func_name].values())
            # 如果func_cfg_uids[func_name]为空list，跳过
            if not func_cfg_uids[func_name]:
                continue
            # try:
            #     for i in range(len(func_cfg_uids[func_name])):
            #         if nodes[func_cfg_uids[func_name][i]].uid >= last_node.uid \
            #             and nodes[func_cfg_uids[func_name][i]].opcode in ["SSTORE","CALL","DELEGATECALL"]:
            #             last_node = nodes[func_cfg_uids[func_name][i]]
            # except Exception as e:
            #     print(f"# ERROR2: {e}")
            #     print(f"# func_name: {func_name}")
            #     print(f"# func_cfg_uids[func_name]: {func_cfg_uids[func_name]}")
            for i in range(len(func_cfg_uids_list)-1):
                last_node = nodes[func_cfg_uids_list[i][-1]]
                for j in range(len(func_cfg_uids_list[i])-1):
                    if func_cfg_uids_list[i][j] >= last_node.uid \
                        and nodes[func_cfg_uids_list[i][j]].opcode in ["SSTORE","CALL","DELEGATECALL"]:
                        last_node = nodes[func_cfg_uids_list[i][j]]
                        state = copy(last_node.state)
                    instruction = state.get_current_instruction()
                    constraints = copy(state.world_state.constraints)
                    constraints += [
                        state.environment.sender == ACTORS.attacker,
                    ]
                    try:
                        solver.get_model(constraints)
                        flag_correctness = False
                    except UnsatError:
                        continue # 限制msg.sender，不是任意的地址
            
            # 检查是否修改了balance，或者调用了transfer或transferFrom
            for uid in func_paths[func_name][i]:
                if nodes[uid].opcode in ["SSTORE"]: # 检查是否存在balance[msg.sender]或balance[from]减少
                    current_node = nodes[uid]
                    slot_start_nodes_ids = Node.find_start_node_ids(nodes,current_node.predecessors_list[0])
                    value_start_nodes_ids = Node.find_start_node_ids(nodes,current_node.predecessors_list[1])
                    value_predecessor_list = current_node.predecessors_list[1]
                    if check_opcode(nodes,value_predecessor_list,"SUB"):
                        flag_correctness = True
                        break
                elif nodes[uid].opcode in ["CALL","DELEGATECALL"]: # 检查是否调用了transfer或transferFrom
                    if hasattr(nodes[uid], 'call_func_signature') and nodes[uid].call_func_signature is None: # 调用transfer函数
                        flag_correctness = True # 无法处理的CALL节点默认正确
                        break
                    if nodes[uid].call_func_signature in [FuncHash.TRANSFER,FuncHash.TRANSFER_FROM]:
                        flag_correctness = True
                        break
            if not flag_correctness:
                print("ERROR: airdrop function authorisation correctness")
                description_head = "AirDrop function authorisation correctness"
                description = f"AirDrop function authorisation correctness, function name:{func_name}"
                issue = ret_issues(state,description_head=description_head, description_tail=description)
                issues.append(issue)   
        
        print("----detect_airdrop_correctness end----")
        return issues
        
                
        
    @staticmethod
    def detect_airdrop(nodes,func_name=None):
        print("==== detect_airdrop ====")
        # 检测存在循环结构的函数:只要检测到一个循环结构就直接返回
        if flag_detailed:
            print("----detct loop----")
        func_name_list,func_cfg_uids,func_paths = Node.detect_loops(detector.nodes)
        #TODO:检测空投函数=存在循环结构，且循环结构中存在SSTORE结点（tranfer或tranferfrom）或CALL/DELEGATECALL结点（value!="0"或函数签名为transfer(from)）
        if flag_detailed:
            print("----detct transfer in loop----")
        res_func_name_list = Node.detect_transfer_in_loop(nodes,func_name_list,func_cfg_uids,func_paths)
        print("detect_airdrop res_func_name_list",res_func_name_list)
        # detect_transfer_in_loop
        #TODO：检测循环结构是否正确，三种类型：
        # 1.跨合约调用transfer或transferFrom，token.transferFrom(msg.sender, _addresses[i], _amounts[i]);
        # 2.发送ETH空投，_addresses[i].call{value: _amounts[i]}("")
        # 3.直接修改balance
        # 检查空投正确性
        issues = Node.detect_airdrop_correctness(nodes,res_func_name_list,func_cfg_uids,func_paths)
        print("# detect_airdrop issues",issues)
        return issues
    
    # 获取所有路径
    @staticmethod
    def get_all_path(nodes,func_name):
        start_time = time.time()
        cfg_path_uids_dict = {} # 记录该分支从entry节点开始，经过的所有cfg节点，最后一个节点的uid:[uids]
        path_uids_list = [] # 记录该分支所有业务图节点[[uids],...]
        for node in nodes.values():
            if node.function_name == func_name and node.opcode in ["JUMP","JUMPI","JUMPDEST"] and node.node_type != NodeType.DELETED:
                # 如果后继节点时exit节点，则为路径终点
                # if not hasattr(node, 'successors'):
                #     print("node.uid",node.uid)
                # else:
                #     print("node.uid",node.uid,"node.successors",node.successors)
                # print("node.uid",node.uid,"node.successors",node.successors)
                if hasattr(node, 'successors') and nodes[node.successors[0]].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                    cfg_path_uids_dict[node.uid] = [node.uid]
            # 检查是否有异常CFG节点
            # if node.opcode in ["JUMP","JUMPDEST"] and len(node.successors) > 2:
            #     # 如果后继节点时exit节点，则为路径终点
            #     print("####node.uid",node.uid,"node.successors",node.successors,"node.node_type",node.node_type)
            # 检查JUMPI是否正确
            # if node.opcode == "JUMPI" and len(node.successors) == 2:
            #     # 如果后继节点时exit节点，则为路径终点
            #     print("####node.uid",node.uid,"node.successors",node.successors)
        # 获取完整CFG路径
        for node_uid in cfg_path_uids_dict:
            if nodes[node_uid].node_type == NodeType.ENTRY_OR_EXIT_POINT: # 如果是只有一个entry结点所在基本块的情况
                continue
            cfg_node = nodes[node_uid]
            if cfg_node.opcode in ["CALL","DELEGATECALL"]:
                continue
            while cfg_node.node_type != NodeType.ENTRY_OR_EXIT_POINT: # 向前找CFG节点直到entry节点开始
                if not cfg_node.predecessors_list[0]:
                    print("ERROR:cfg_node",cfg_node.uid,"predecessors_list",cfg_node.predecessors_list)
                    break
                cfg_node = nodes[cfg_node.predecessors_list[0][0]]
                cfg_path_uids_dict[node_uid] = [cfg_node.uid] + cfg_path_uids_dict[node_uid]
        # 获取完整路径
        for node_uid in cfg_path_uids_dict:
            cfg_path = cfg_path_uids_dict[node_uid] #因为JUMPI节点有两个后继，JUMPI和JUMPDEST节点的cfg_uid_info分别记录了两条的基本块包含的节点
            block_path = []
            # 除去JUMPDEST前的相邻的JUMPI节点
            for i in range(len(cfg_path)-1):
                if nodes[cfg_path[i]].opcode == "JUMPI" and cfg_path[i] == nodes[cfg_path[i+1]].predecessors_list[0][0]:
                    continue
                block_path.append(cfg_path[i])
            block_path.append(cfg_path[-1])
            # print("block_path",block_path)
            # 获取完整路径
            path = []
            for block_uid in block_path:
                path += nodes[block_uid].cfg_uid_info
            path_uids_list.append(path)
        # # 打印路径
        # for uid in cfg_path_uids_dict:
        #     print(f"uid:{uid} offset {nodes[uid].offset} path:{cfg_path_uids_dict[uid]}")
        # for path in path_uids_list:
        #     print(f"path:{path}")
        if flag_time:
            print("get_all_path time:",time.time() - start_time)
        return cfg_path_uids_dict,path_uids_list


# 检查前驱前驱节点是否包含操作码为opcode的节点，例如ADD或SUB等，只判断遇到的第一个
def check_opcode(nodes, uids: list[int],opcode, limit: int=100) -> bool: 
        #因为使用的是队列，所以顺序是由右到左;uids时var i的直接前驱数组
        start_node_ids = set()
        visited = set()
        queue = deque(uids)
        queue.append(-1) #代表该循环完毕
        count = 0

        while queue:
            count += 1
            if count > 100*limit: #防止死循环
                print("Exceeded maximum number of iterations.")
                break
            current_uid = queue.popleft()
            if current_uid == -1:
                # 当queue中只剩下start_node_ids时，结束循环
                if set(queue).issubset(start_node_ids):
                    break
                else: #下一轮循环
                    queue.append(-1)
                    continue
            current_node = nodes[current_uid]
            print("current_node.uid: ",current_node.uid,"opcode",current_node.opcode)
            # print("current_node.predecessors_list.count",len(current_node.predecessors_list))
            # print("nodes[current_node.predecessors_list[0][0].uid].node_type",nodes[current_node.predecessors_list[0][0]].node_type)
            # print("start_node_ids",start_node_ids)
            # print("queue",queue)
            if current_uid in visited:
                if current_uid in start_node_ids:
                    queue.append(current_uid)

                continue
            
            visited.add(current_uid)
            if nodes[current_uid].opcode and nodes[current_uid].opcode == opcode:
                print(f"check_opcode {opcode} True, current_uid",current_uid)
                return True
            # elif nodes[current_uid].opcode in ["ADD","OR"]: # trick解决误报
            #     return True

            
            if current_node.node_type == NodeType.ENTRY_OR_EXIT_POINT:
                continue
            if current_node.node_type == NodeType.LOG_INFORMATION: #current_node.opcode == "SSTORE" or 
                continue
            if len(current_node.predecessors_list) == 1 and len(current_node.predecessors_list[0]) ==1 and nodes[current_node.predecessors_list[0][0]].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                start_node_ids.add(current_uid)
                queue.append(current_uid)
                if len(start_node_ids) >= limit:
                    print("ERROR:Reached limit of", limit, "start nodes.")
                    break
            # 处理起始结点
            if len(current_node.predecessors_list) == 1 and len(current_node.predecessors_list[0]) == 0:
                start_node_ids.add(current_uid)
                queue.append(current_uid)
                # print("hard code node",current_uid)
                continue
            
            # SLOAD处理
            if current_node.opcode == "SLOAD":
                # if len(current_node.predecessors_list) == 2 and current_node.predecessors_list[1] :
                #     # value有前驱节点，则将直接前驱SSTORE的value的前驱节点加入queue
                #     sstore_node=nodes[current_node.predecessors_list[1][0]]
                #     for predecessor_uid in sstore_node.predecessors_list[1]:
                #         queue.append(predecessor_uid)
                # else:
                #     # value没有前驱节点，则将slot的前驱节点加入queue
                #     for predecessor_uid in current_node.predecessors_list[0]:
                #         queue.append(predecessor_uid)
                continue
                        
            # for predecessor_uid in current_node.predecessors_list[0]:
            #     queue.append(predecessor_uid)
            for i in range(len(current_node.predecessors_list)):
                for predecessor_uid in current_node.predecessors_list[i]:
                    queue.append(predecessor_uid)

        # print("start_node_ids",start_node_ids)
        # print("queue",queue)
        print(f"check_opcode {opcode} False")
        return False


#to simplify the if expr, extract expr.
def CalldataProc(token_expr):
    pattern = re.compile(r'If[(][0-9]*_calldatasize<=[0-9]*,0,[0-9]*_calldata\[[0-9]*\][)]')
    while_count = 0
    while (while_count < while_limit):
        while_count+=1
        ret = pattern.search(token_expr)
        if ret == None:
            break
        ret = ret.group(0)
        elements = ret.split(",")
        if len(elements) == 3 and elements[0].find("_calldatasize") != -1 and elements[2].find("_calldata") != -1:
            token_expr = token_expr.replace(ret, elements[2][:-1])
        else:
            print("replace calldata error!", ret)
            break
    pattern = re.compile(r'[0-9]*_calldata\[[0-9]*\]')
    rightindex=0
    leftindex=0
    while_count = 0
    while (while_count < while_limit):
        while_count+=1
        ret = pattern.search(token_expr)
        if ret == None:
            break
        leftindex, rightindex =ret.span()[0], ret.span()[1]
        if rightindex >= len(token_expr):
            break
        max_index, min_index=0, leftindex
        max_calldataindex=0
        while_count = 0
        while(while_count < while_limit):
            while_count+=1
            cur_calldatastr=token_expr[leftindex:rightindex]
            leftindex_for_cur_calldatastr=cur_calldatastr[:-1].find('[')
            next_index = str(int(cur_calldatastr[leftindex_for_cur_calldatastr+1:-1])+1)
            next_calldatastr=cur_calldatastr.replace('['+cur_calldatastr[leftindex_for_cur_calldatastr+1:-1],'['+next_index)
            if token_expr[rightindex+1:rightindex+len(next_calldatastr)+1] == next_calldatastr:
                max_index = max(max_index, rightindex+len(next_calldatastr)+1)
                max_calldataindex=max(max_calldataindex,int(cur_calldatastr[leftindex_for_cur_calldatastr+1:-1])+1)
            else:
                break
            leftindex=rightindex+1
            rightindex=rightindex+len(next_calldatastr)+1
        token_expr=token_expr.replace(token_expr[min_index:max_index],token_expr[ret.span()[0]:ret.span()[1]-1]+":"+str(max_calldataindex)+']')

    return token_expr

#to simplify the if expr, extract expr.
def ExtractProc(token_expr):
    pattern = re.compile(r'Extract[(][0-9]*,0,sender_[0-9]*[)]')
    while_count = 0
    while (while_count < while_limit):
        while_count+=1
        ret = pattern.search(token_expr)
        if ret == None:
            break
        ret = ret.group(0)
        elements = ret.split(",")
        if len(elements) == 3 and elements[2].find("sender_") != -1:
            token_expr = token_expr.replace(ret, elements[2][:-1])
        else:
            print("replace extract error!", ret)
            break
    return token_expr

#to handle bool type symbol var
def IfAndOrProc(token_expr):
    pattern = re.compile(r'And\((?:Or\(\d+_calldata\[\d+\]==0,\d+_calldatasize<=\d+\),?|Or\(\d+_calldatasize<=\d+,\d+_calldata\[\d+\]==0\),?)+\)')
    matches = pattern.findall(token_expr)

    for match in matches:
        and_expr = match
        pattern = re.compile(r'(\d+)_calldatasize<=(\d+)')
        sub_matches = pattern.findall(match)

        # Extract all numbers after "calldatasize <= "
        tx_id = sub_matches[0][0]
        numbers = [int(sub_match[1]) for sub_match in sub_matches]

        # Find the minimum and maximum numbers
        min_number = min(numbers)
        max_number = max(numbers)
        
        ret="And({}_calldata[{}:{}])".format(tx_id,min_number,max_number)
      
        # Replace the matched pattern with ret
        token_expr = token_expr.replace(and_expr,ret)
    
    return token_expr

# def PreProcExpr(token_expr):
#     token_expr = token_expr.replace('\n', "").replace(" ", "") #去掉换行和空格
#     token_expr = IfAndOrProc(token_expr) #处理Bool型符号变量
#     token_expr = CalldataProc(token_expr)
#     token_expr = ExtractProc(token_expr)
#     return token_expr
def symbol_var_preprocess(token_expr):
    if flag_time:
        start_time = time.time()
    token_size = token_expr.raw.size()
    token_expr = str(token_expr.raw)
    # print("len(token_expr):",len(token_expr))
    token_expr = PreProcExpr(token_expr)
    if flag_time:
        print("symbol_var_preprocess time:",time.time() - start_time)
    return token_expr


def PreProcExpr(token_expr):
    token_expr = re.sub(r'\s+', '', token_expr)
    # 预编译所有正则表达式以提高性能
    pattern1 = re.compile(r'Or\((\d+)_calldata\[(\d+)\]==0,\1_calldatasize<=\2\)')
    replacement1 = r'\1_calldata[\2]'
    pattern2 = re.compile(r'Or\((\d+)_calldatasize<=(\d+),\1_calldata\[\2\]==0\)')
    replacement2 = r'\1_calldata[\2]'
    pattern3 = re.compile(r'If\((\d+)_calldatasize<=(\d+),0,\1_calldata\[\2\]\)')
    replacement3 = r'\1_calldata[\2]'
    # pattern4 = re.compile(r'(\d+)_calldata\[(\d+)\],\1_calldata\[(\d+)\]')
    # replacement4 = r'\1_calldata[\2:\3]'
    # pattern5 = re.compile(r'(\d+)_calldata\[(\d+):(\d+)\],\1_calldata\[(\d+):(\d+)\]')
    # replacement5 = r'\1_calldata[\2:\5]'
    # pattern6 = re.compile(r'(\d+)_calldata\[(\d+):(\d+)\],\1_calldata\[(\d+)\]')
    # replacement6 = r'\1_calldata[\2:\4]'
    pattern_combined = re.compile(r'(\d+)_calldata\[(\d+)\](,\1_calldata\[(\d+)\])+')
    replacement_combined = r'\1_calldata[\2:\4]'
    # 针对aidrop的特殊处理
    pattern7 = re.compile(r'If\((\d+)_calldatasize<=((\d+)\+Concat\(\1_calldata\[(\d+):(\d+)\]\)),0,\1_calldata\[\3\+Concat\(\1_calldata\[\4:\5\]\)\]\)')
    replacement7 = r'\1_calldata[\3+Concat(\1_calldata[\4:\5])]' #If(2_calldatasize<=48+Concat(2_calldata[4:35]),0,2_calldata[48+Concat(2_calldata[4:35])])
    pattern8 = re.compile(r'(\d+)_calldata\[(\d+\+Concat\(\d+_calldata\[\d+:\d+\]\))\](,\d+_calldata\[\d+\+Concat\(\d+_calldata\[\d+:\d+\]\)\])*,\d+_calldata\[(\d+\+Concat\(\d+_calldata\[\d+:\d+\]\))\]') #,(\d+)\)\)
    replacement8 = r'\1_calldata[\2:\4]'
    
    # 应用预编译的正则表达式进行替换
    transformed_expr = pattern1.sub(replacement1, token_expr)
    transformed_expr = pattern2.sub(replacement2, transformed_expr)
    transformed_expr = pattern3.sub(replacement3, transformed_expr)
    # print("transferred_expr1:", transformed_expr)
    transformed_expr = pattern_combined.sub(replacement_combined, transformed_expr)
    # transformed_expr = pattern4.sub(replacement4, transformed_expr)

    # # 使用 re.subn 替换 pattern5，避免重复搜索
    # replacements = 0
    # while True:
    #     transformed_expr, num_replacements = pattern5.subn(replacement5, transformed_expr)
    #     replacements += num_replacements
    #     if num_replacements == 0:
    #         break
    # transformed_expr = pattern6.sub(replacement6, transformed_expr)
    transformed_expr = pattern7.sub(replacement7, transformed_expr)
    # print(transformed_expr)
    transformed_expr = pattern8.sub(replacement8, transformed_expr)
    
    # 如果transformed_expr是以"0,"开头，则去除"0,"
    if transformed_expr.startswith("0,"):
        transformed_expr = transformed_expr[2:]
    return transformed_expr

def PreProcExpr2(token_expr):
    start_time = time.time()
    
    token_expr = token_expr.replace('\n', "").replace(" ", "")  # 去掉换行和空格
    replace_time = time.time()
    if replace_time - start_time>0.5:
        print(f"替换操作运行时间: {replace_time - start_time}秒")
    
    token_expr = IfAndOrProc(token_expr)  # 处理Bool型符号变量
    if_and_or_proc_time = time.time()
    if if_and_or_proc_time - replace_time>0.5:
        print(f"IfAndOrProc运行时间: {if_and_or_proc_time - replace_time}秒")
    
    token_expr = CalldataProc(token_expr)
    calldata_proc_time = time.time()
    if calldata_proc_time - if_and_or_proc_time>0.5:
        print(f"CalldataProc运行时间: {calldata_proc_time - if_and_or_proc_time}秒")
    
    token_expr = ExtractProc(token_expr)
    extract_proc_time = time.time()
    if extract_proc_time - calldata_proc_time>0.5:
        print(f"ExtractProc运行时间: {extract_proc_time - calldata_proc_time}秒")
    
    return token_expr

def ret_report(Funcname,error,slot,value):
    print("Function_name:", Funcname)
    print(error)
    print("slot: ", slot, "\nvalue: ", value, end="\n\n")
    
    
def ret_issues(state, severity:str="High", description_head:str="", description_tail:str=""):
    environment = state.environment
    function_name = environment.active_function_name
    # description_head, description_tail = descriptions
    if description_head == "":
        description_head = str(function_name)
    print("Function_name:", state.environment.active_function_name,description_tail,description_tail)
    issue = Issue(
        contract=environment.active_account.contract_name,
        function_name=function_name,
        address=state.get_current_instruction()["address"],
        swc_id=WRITE_TO_ARBITRARY_STORAGE,
        bytecode=environment.code.bytecode,
        title=function_name+" handle",
        severity=severity,
        description_head=description_head,
        description_tail=description_tail,
        gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
        # transaction_sequence=transaction_sequence,
    )
    return issue
    


# def sstore_extract_data(s):
#     # 定义正则表达式模式
#     # pattern = r'(\d+_calldata\[\d+:\d+\])|(sender_\d+)'
#     pattern = r'keccak256_512\(Concat\((?:0,)?(.*?),'
#     pattern_identity = r'keccak256_512\(Concat\((?:0,)?(?:.*?),(\d+)\)'
#     # pattern = r'keccak256_512\(Concat\((?:0,)?(.*?)(?:,|\))'
    
#     # 使用正则表达式进行匹配
#     matches = re.findall(pattern, s)
#     identity_matches = re.findall(pattern_identity, s)
    
#     # 提取匹配到的数据
#     data = [match for match in matches]
    
#     return data,identity_matches[0]

def identity_extract(expr):
    # pattern = r'keccak256_512\(Concat\((?:0,)?(?:.*?),(\d+)\)'
    pattern = r'keccak256_512\((?:0,)?(?:.*?),(\d+)\)'
    identity = re.findall(pattern, expr)
    if len(identity)>0:
        return identity[0]
    # 如果expr中不包含keccak256_512，且expr是只有一个数字的字符串
    elif "keccak256_512" not in expr and re.fullmatch(r'\d+', expr):
        return expr
    else:
        return -1

# def identity_sub(expr):
#     #删除expr中的identity
#     pattern = r'(keccak256_512\(Concat\((?:0,)?(?:.*?),)(\d+)(\))'
#     ret_expr = re.sub(pattern, r'\1\3', expr)
#     # print("###identity_sub",expr,"->",ret_expr)
#     return ret_expr


# def extract_calldata_index(calldata): #提取calldata序号
#     pattern = re.compile(r'calldata\[(\d+):(\d+)\]')
#     ret = pattern.search(calldata)
#     if ret == None:
#         return None
#     return ret.group(1), ret.group(2)

# def extract_slot_roles(slot): #提取mapping中的key
#     roles_pattern = r"keccak256_512\(Concat\((?:\d+,\s*)?(?:Extract\(\d+,\s*\d+,\s*)?((?:If\(\d+_calldatasize <= \d+,\s*\d+,\s*\d+_calldata\[\d+\]\),\s*)*(?:If\(\d+_calldatasize <= \d+,\s*\d+,\s*\d+_calldata\[\d+\]\)|sender_\d+)?)(?:\s*,\s*(?:\d+\)\)|keccak256_512))?"

#     roles = []

#     # 查找匹配的内容
#     matches = re.findall(roles_pattern, slot, re.DOTALL)

#     # 如果找到匹配的内容，提取roles
#     if len(matches) > 0:
#         roles = matches
#     # 除去空字符串
#     roles = list(filter(None, roles))
    return roles

# 检查函数内是否存在ADDRESS结点
def check_address_node(nodes,current_node:Node): #检查是否存在ADDRESS结点
    current_uid = current_node.uid
    for node_uid in range(current_uid-1, -1, -1):
        if nodes[node_uid].function_name != current_node.function_name:
            continue
        if nodes[node_uid].tx_id != current_node.tx_id:
            continue
        if nodes[node_uid].opcode == "ADDRESS":
            return True
    return False

def hard_code_check(nodes,current_node:Node): #检查是否存在硬编码；并给出正确的数据源节点数
    issues = []
    slot_hard_code = []
    value_nard_code = []
    this_address_list = []
    sha3_node_count = 0
    # current_node = nodes[Node.count-1]
    state = current_node.state
    slot_start_node_ids,sha3_uids = Node.find_start_node_ids(nodes, current_node.predecessors_list[0],ret_SHA3_count=True)
    if len(slot_start_node_ids) == 0:
        # print("INFO:not mapping sstore")
        return issues
    elif len(slot_start_node_ids) != len(sha3_uids):
        func_name = state.environment.active_function_name
        description_head = f"Hardcode or ADDRESS node detected"
        description = f"Hardcode detected in {func_name} function."
        if check_address_node(nodes,current_node):
            description += "ADDRESS node.\n"
        else:
            description += "\n"
        description += "SHA3 node count is not equal to source node count.\n"
        print(f"sha3_count:{sha3_uids},source node count:{len(slot_start_node_ids),slot_start_node_ids}")
        severity = "High"
        issue = ret_issues(state,severity = severity, description_head=description_head, description_tail=description)
        issues.append(issue)
        # if 
        return issues
    value_start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[1])
    # print("start_node_ids",start_node_ids)
    # environment = state.environment
    # 检查slot是否有hard code
    for node_uid in slot_start_node_ids:
        # if nodes[node_uid].node_type == NodeType.ENVIRONMENT_CONTEXT:
        if nodes[node_uid].opcode == "CALLDATALOAD" or nodes[node_uid].opcode == "CALLER" :#or nodes[node_uid].opcode == "PUSH1"
            continue
        elif nodes[node_uid].opcode == "ADDRESS":
            print("current uid",current_node.uid)
            print("ERROR:Hardcode(ADDRESS) node in",node_uid,"slot")
            slot_hard_code.append(slot_start_node_ids.index(node_uid))
            this_address_list.append(node_uid)
        else: #存在hard node，注意ADDRESS操作码获取的合约地址也视为hard code
            print("current uid",current_node.uid)
            print("ERROR:Hardcode node in",node_uid,"slot")
            slot_hard_code.append(slot_start_node_ids.index(node_uid))
    # 检查value是否有hard code
    for node_uid in value_start_node_ids:
        # if nodes[node_uid].node_type == NodeType.ENVIRONMENT_CONTEXT:
        if nodes[node_uid].opcode == "CALLDATALOAD" or nodes[node_uid].opcode == "CALLER" :#or nodes[node_uid].opcode == "PUSH1"
            continue
        elif nodes[node_uid].opcode == "ADDRESS":
            print("current uid",current_node.uid)
            print("ERROR:Hardcode(ADDRESS) node in",node_uid,"value")
            value_nard_code.append(value_start_node_ids.index(node_uid))
            this_address_list.append(node_uid)
        else: #存在hard node
            print("current uid",current_node.uid)
            print("ERROR:Hardcode node in",node_uid,"value")
            value_nard_code.append(value_start_node_ids.index(node_uid))
    # if len(value_nard_code) > 0 and value_nard_code[0] in slot_hard_code:
    #     value_nard_code.remove(value_nard_code[0])
    if len(slot_hard_code) > 0 or len(value_nard_code) > 0:
        func_name = state.environment.active_function_name
        description = f"Hardcode detected in {func_name} function."
        if check_address_node(nodes,current_node):
            description += "ADDRESS node.\n"
        else:
            description += "\n"
        if len(slot_hard_code) > 0:
            description += "\tHardcode in slot detected in nodes: {} \n".format(slot_hard_code)
        elif len(value_nard_code) > 0:
            description += "\tHardcode in value detected in nodes: {} \n".format(value_nard_code)
        if len(this_address_list) > 0:
            description += "\t ADDRESS node in nodes: {} \n".format(this_address_list)
        # 如果所有的硬编码都为ADDRESS，则severity= "Medium"
        severity = "High"
        if all(node_uid in this_address_list for node_uid in slot_hard_code) and all(node_uid in this_address_list for node_uid in value_nard_code):
            severity = "Medium"
        description_head = f"Hardcode or ADDRESS node detected"
        issue = ret_issues(state,severity = severity, description_head=description_head, description_tail=description)
        issues.append(issue)
        
    return issues

def check_roles(expr:str,role:Role):
    if role: #不为Role.HARD_CODE
        match = re.match(role.value, expr)
        if match:
            return True
        if role == Role.PARAM1: #calldata[16:35]
            match = re.match(r'\d+_calldata\[16:35\]', expr)
            if match:
                return True


class FuncHash(Enum):
    """EVM函数选择器哈希值"""
    APPROVE = "0x095ea7b3" # approve(address,uint256)
    APPROVE_AND_CALL = "0xd505accf" # approveAndCall(address, bytes)
    SET_APPROVAL_FOR_ALL = "0xa22cb465" # setApprovalForAll(address,bool)
    TRANSFER = "0xa9059cbb" # transfer(address,uint256)
    TRANSFER_FROM = "0x23b872dd" # transferFrom(address,address,uint256)

# 将call_data转换为16进制字符串
def get_function_signature(call_data:list):
    # 获取前四个字节
    first_four_bytes = call_data[:4]
    # 如果是符号变量返回空
    # print("first_four_bytes",first_four_bytes)
    # 转换为16进制字符串
    hex_signature = "0x" + "".join(f"{byte:02X}" for byte in first_four_bytes)
    print("hex_signature",hex_signature)
    # 转换成小写
    hex_signature = hex_signature.lower()
    # print("hex_signature",hex_signature)
    return hex_signature

# 检查函数哈希,call_data:list, target_signatures:List[FuncHash]
def check_func_hash(call_data, target_signatures=None): # 默认情况下，检查是否为任意一种函数哈希
    # 获取calldata的函数签名
    try:
        function_signature = get_function_signature(call_data)
        if target_signatures == None:
            target_signatures = [FuncHash.TRANSFER, FuncHash.TRANSFER_FROM, FuncHash.APPROVE, FuncHash.APPROVE_AND_CALL, FuncHash.SET_APPROVAL_FOR_ALL]
        for target_signature in target_signatures:
            if function_signature == target_signature.value:
                return target_signature
    except:
        print("call_data[:4]:",PreProcExpr(str(call_data[:4])))
        print("ERROR:check_func_hash exception")
        return None
    return function_signature # 不是指定的函数哈希


     

class DefiCheck3(DetectionModule):
    """This module searches for defi issues."""

    name = "DefiCheck"
    swc_id = WRITE_TO_ARBITRARY_STORAGE
    description = DESCRIPTION
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["SSTORE","LOG2","LOG3","LOG4","SLOAD","SHA3",
                 "CALLDATALOAD","AND","OR","CALLER","ADDRESS",
                 "STOP","RETURN","REVERT",
                 "ADD","SUB","CALL","DELEGATECALL",
                 "ISZERO",
                 "JUMPDEST",
                 "JUMP","JUMPI"] #,"PUSH20","DELEGATECALL","PUSH1","MSTORE",
    post_hooks = Post_hooks
    
    function_dict = {}
    nodes: Dict[int, Node] = {}
    identity_dict = {}
    deficheck_time =0
    memory_dict = defaultdict(dict)
    # 计时
    func_opcode_time = {} # hook中的
    

    def __init__(self) -> None:
        """
        Cache satisfiability of defi constraints
        """
        super().__init__()

    def reset_module(self):
        """
        Resets the module by clearing everything
        :return:
        """
        super().reset_module()

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        if state.get_current_instruction()["address"] in self.cache: #避免重复处理指令
            # print("state.get_current_instruction():\n ",state.get_current_instruction()) #{'address': 24, 'opcode': 'SSTORE'}
            return 

        return self._analyze_state(state)

    def _analyze_state(self, state):
        """

        :param state:
        :return:
        """
        issues = []
        Func_name=state.environment.active_function_name
        # if Func_name=="revokeOperator(address)" or \
        #     Func_name=="authorizeOperator(address)" or \
        #     Func_name=="decreaseAllowance(address,uint256)"or \
        #     Func_name=="setApprovalForAll(address,bool)"or\
        #     Func_name=="decreaseApproval(address,uint256)" or\
        #     Func_name=="increaseAllowance(address,uint256)"or \
        #     Func_name=="increaseApproval(address,uint256)" or \
        #     Func_name=="approveAllAndCall(address, bytes)" or \
        #     Func_name == "_function_0xd505accf" or \
        #     Func_name == "setCrowdsaleAddress(address)":
        #         print("Func_name_r: ", Func_name)
        #         return []
        if Func_name == "balanceOf(address)" or \
            Func_name == "balanceOf(address,uint256)" or \
            Func_name == "ownerOf(uint256)" or \
            Func_name == "getApproved(uint256)" or \
            Func_name == "name()" or \
            Func_name == "symbol()" or \
            Func_name == "isApprovedForAll(address,address)":
            if flag_detailed:
                print("Func_name_r: ", Func_name)
            return []
        
            
        # if state.environment.active_function_name != "approve(address,uint256)": #只处理approve函数
        # # if state.environment.active_function_name != "transfer(address,uint256)": #只处理transfer函数
        # if state.environment.active_function_name != "transferFrom(address,address,uint256)": #只处理setApprovalForAll函数
            # return []
        func_list = ["approve",
                     "Approval",
                     "permit",
                     "transfer",
                     "airdrop",
                     "constructor",
                     "fallback"] 
        # 如果Func_name不包含func_list中任何一个元素(包含是指func_list[i] in Func_name)，则返回
        if flag_ERC and not any([func.lower() in Func_name.lower() for func in func_list]):
            return []
        
        # 如果检测空投函数，则排除常见的空投函数的检测
        if flag_airdrop and Func_name in not_airdrop_list:
            return []
        
        #如果函数名未记录function_list中，则记录
        if Func_name not in self.function_dict:
            self.function_dict[Func_name] = FunctionType.UNKNOWN
        if not flag_check: #是否使用插件进行检查
            return []
        prehook_opcode=state.get_current_instruction()["opcode"]
        if prehook_opcode in self.pre_hooks:
            Node.cur_pc+=1
        if flag_detailed:
            print("\nFunc_name: ",Func_name,"-----------------prehook_opcode: ",prehook_opcode)
            
        hook_start_time = time.time()
        account = state.environment.active_account
        address = account.address
        # print("address: ",address)
        # if account.balance:
        #     print("balance: ",PreProcExpr(str(account.balance()))) 
        environment = state.environment
        # 如果没有function_name == Func_name的node，则创建起始节点
        EntryNode_uid= -1
        for node in self.nodes:
            if self.nodes[node].function_name == Func_name and self.nodes[node].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                EntryNode_uid = self.nodes[node].uid
                break
        # if flag_create == False:
        if EntryNode_uid == -1:
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.ENTRY_OR_EXIT_POINT
                            )
            self.nodes[new_node.uid] = new_node
            EntryNode_uid = new_node.uid
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.ENTRY_OR_EXIT_POINT,
                            predecessors_list=[[]]
                            )
            self.nodes[new_node.uid] = new_node
            ExitNode_uid = new_node.uid
            #打印
            # for node in self.nodes:
            #     if self.nodes[node].function_name == Func_name:
            #         print("node:",self.nodes[node].get_dict())
        else:
            EntryNode_uid = -1
            ExitNode_uid = -1
            for node in self.nodes:
                if self.nodes[node].function_name == Func_name:
                    if self.nodes[node].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                        if EntryNode_uid == -1:
                            EntryNode_uid = node
                        else:
                            ExitNode_uid = node
                            break               

        #old_node时function_name == Func_name的最后一个节点
        # old_node = self.nodes[Node.count-1]
        
        # if Node.count>2 and old_node.post_flag: #POST_HOOK  and not is_prehook()
        old_node = None
        if not is_prehook():
            for node_uid in self.nodes:
                if self.nodes[node_uid].post_flag:
                    old_node = self.nodes[node_uid]
                    if flag_detailed:
                        print("find old_node",old_node.uid)
                    break
            if old_node == None:
                for node in self.nodes:
                    print("old_node == None")
                    print(self.nodes[node].function_name,"node:",self.nodes[node].get_dict())
            posthook_opcode = state.environment.code.instruction_list[state.mstate.pc - 1][
                "opcode"
            ]
            # old_node的起始结点
            for node in self.nodes:
                if self.nodes[node].function_name == old_node.function_name and self.nodes[node].node_type == NodeType.ENTRY_OR_EXIT_POINT:
                    EntryNode_uid = self.nodes[node].uid
                    break
            if flag_detailed:
                print("posthook_opcode",posthook_opcode)
            if flag_time:
                
                print("Func",Func_name,"Post_hook",posthook_opcode,hook_start_time)
            old_node.post_flag = False
            if flag_detailed:
                print("post_hook INFO:",old_node.function_name,old_node.opcode)
            # print("post_hook INFO")
            if old_node.opcode in ["AND","OR"]: #AND:calldata[4:35] ->calldata[16:35]
                # print("AND post")
                if old_node.opcode == "AND":
                    old_node.find_edge(self.nodes,ExitNode_uid)
                    # 如果没有前驱节点，则不需要
                    if len(old_node.predecessors_list) == 0:
                        print("Node.remove",old_node.uid,old_node.opcode)
                        Node.remove(old_node,self.nodes)
                    else:
                        if len(old_node.predecessors_list) == 0:
                            print("Node.remove",old_node.uid,old_node.opcode)
                            Node.remove(old_node,self.nodes)
                        if flag_detailed:
                            print("old_node.predecessors_list",old_node.predecessors_list)
                            # print("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                            print_limited("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                        old_node.symbol_vars = [simplify(state.mstate.stack[-1])]
                        if flag_detailed:
                            old_node.symbol_vars_expr = [Node.get_last_bracket_content(symbol_var_preprocess(var)) for var in old_node.symbol_vars]
                            print("after AND")
                            print("old_node.predecessors_list",old_node.predecessors_list)
                            # print("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                            print_limited("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                        else:
                            old_node.symbol_vars_expr = ["..."]
                else:  # OR
                    if len(old_node.predecessors_list) == 0:
                        if flag_detailed:
                            print("Node.remove",old_node.uid,old_node.opcode)
                        Node.remove(old_node,self.nodes)
                        # print("OR remove,time cost:",time.time()-post_or_time_start)
                    else:
                        if flag_detailed :
                            print("old_node.predecessors_list[0]",old_node.predecessors_list[0])
                            print("old_node.predecessors_list[1]",old_node.predecessors_list[1])
                            # print("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                            print_limited("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                        post_or_time_start = time.time()
                        old_node.find_edge(self.nodes,ExitNode_uid)
                        post_or_time = time.time()
                        if flag_time:
                            print("OR post find_edge time cost:",post_or_time - post_or_time_start)
                        old_node.symbol_vars = [simplify(state.mstate.stack[-1])]
                        post_or_time_end = time.time()
                        if flag_time:
                            print("OR post simplify time cost:",post_or_time_end - post_or_time)
                        if flag_detailed:
                            old_node.symbol_vars_expr = [Node.get_last_bracket_content(symbol_var_preprocess(old_node.symbol_vars[0]))]
                            # print("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                            print_limited("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                            print("old_node.predecessors_list",old_node.predecessors_list)
                        else:
                            old_node.symbol_vars_expr = ["..."]
                if flag_detailed:
                    print("AND/OR post END")
            elif old_node.opcode == "SLOAD":
                # print("SLOAD post")
                old_node.symbol_vars.append(simplify(state.mstate.stack[-1]))
                # print("##old_node.symbol_vars",old_node.symbol_vars)
                if flag_detailed:
                    old_node.symbol_vars_expr.append(Node.get_last_bracket_content(PreProcExpr(str(old_node.symbol_vars[1]))))
                else:
                    old_node.symbol_vars_expr.append("...")
                old_node.find_edge(self.nodes,ExitNode_uid) 
                if flag_detailed:
                    # print("SLOAD symbol_vars_expr:",old_node.symbol_vars_expr)
                    print_limited("SLOAD symbol_vars_expr",old_node.symbol_vars_expr)
            elif old_node.opcode == "ADD" or old_node.opcode == "SUB":
                # print("ADD post")
                if flag_detailed:
                    # print("ADD/SUB symbol_vars_expr:",old_node.symbol_vars_expr)
                    print_limited("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                # if old_node.symbol_vars_expr[0] == "1" or old_node.symbol_vars_expr[1] == "1" \
                #     or re.fullmatch(r'_calldata\[\d+:\d+\]', old_node.symbol_vars_expr[0]) or re.fullmatch(r'\d+_calldata\[\d+:\d+\]', old_node.symbol_vars_expr[1]):
                #     old_node.symbol_vars = [state.mstate.stack[-1]]
                #     # old_node.symbol_vars_expr = [Node.get_last_bracket_content(PreProcExpr(str(simplify(old_node.symbol_vars[0]))))]
                #     old_node.symbol_vars_expr = [Node.get_last_bracket_content(PreProcExpr(str(old_node.symbol_vars[0])))]
                # else:
                #     old_node.remove(self.nodes)
                # old_node.symbol_vars = [state.mstate.stack[-1]]
                old_node.symbol_vars = [simplify(state.mstate.stack[-1])]
                if flag_detailed: #old_node.opcode == "ADD" or 
                    old_node.symbol_vars_expr = [Node.get_last_bracket_content(symbol_var_preprocess(old_node.symbol_vars[0]))]
                else:
                    old_node.symbol_vars_expr = ["..."]
                if flag_detailed:
                    print_limited("ADD/SUB symbol_vars_expr:",old_node.symbol_vars_expr)
                    print_limited("Stack[-1]:",Node.get_last_bracket_content(symbol_var_preprocess(state.mstate.stack[-1])))
                    if old_node.opcode == "ADD":
                        print("ADD INFO END") #
                    else:
                        print("SUB INFO END")
            elif old_node.opcode in ["CALL","DELEGATECALL"]:
                if flag_detailed:
                    print(old_node.opcode,"post")
                    print("ERROR unhandle CALL post_hook,TODO")
                    print(old_node.opcode,"post END")
            elif old_node.opcode == "ISZERO": # 添加到直接前驱节点的符号变量中，并删除本节点
                # print("ISZERO post")
                if len(old_node.predecessors_list[0]) > 0:
                    symbol_var = state.mstate.stack[-1]
                    # symbol_var_expr = Node.get_last_bracket_content(PreProcExpr(str(old_node.symbol_vars[0])))
                    pre_node = self.nodes[old_node.predecessors_list[0][0]] #ISZERO结点的前驱结点
                    if flag_detailed:
                        symbol_var_expr = Node.get_last_bracket_content(symbol_var_preprocess(old_node.symbol_vars[0]))
                    else:
                        symbol_var_expr = "..."
                    if symbol_var not in pre_node.symbol_vars:
                        pre_node.symbol_vars.append(symbol_var)
                        pre_node.symbol_vars_expr.append(symbol_var_expr)
                    if flag_detailed:
                        print_limited("ISZERO symbol_vars_expr:",symbol_var_expr)
                        print("ISZERO post END")
                old_node.remove(self.nodes) # 删除ISZERO结点
            elif old_node.opcode in Post_hooks:
                # old_node.slot=state.mstate.stack[-1]
                # old_node.symbol_vars = [state.mstate.stack[-1]]
                old_node.symbol_vars = [simplify(state.mstate.stack[-1])]
                if flag_detailed or old_node.opcode in ["CALLDATALOAD","CALLER","ADDRESS","SHA3"]:
                    try:
                        # old_node.symbol_vars_expr = [Node.get_last_bracket_content(PreProcExpr(str(var))) for var in old_node.symbol_vars]
                        old_node.symbol_vars_expr = [Node.get_last_bracket_content(symbol_var_preprocess(var)) for var in old_node.symbol_vars]
                    except:
                        # old_node.symbol_vars_expr = [PreProcExpr(str(var)) for var in old_node.symbol_vars]
                        old_node.symbol_vars_expr = [symbol_var_preprocess(var) for var in old_node.symbol_vars]
                        # print_limited("ISZERO symbol_vars_expr:",symbol_var_expr)
                        print("#ERROR:old_node.symbol_vars_expr error:",old_node.symbol_vars_expr)
                else:
                    old_node.symbol_vars_expr = ["..." for var in old_node.symbol_vars]
                old_node.predecessors_list = [[] for _ in range(len(old_node.symbol_vars))]
                if old_node.opcode not in ["CALLDATALOAD","CALLER","ADDRESS"] and old_node.node_type != NodeType.ENTRY_OR_EXIT_POINT:# 不是起始节点和PUSH20 #,"PUSH1"
                    old_node.find_edge(self.nodes,ExitNode_uid)
                else: #CALLDATALOAD和CALLER、ADDRESS指向起始节点 #PUSH1
                    # if old_node.predecessors == []:
                    if old_node.predecessors_list[0] == []:
                        old_node.predecessors_list[0].append(EntryNode_uid)
                        if ExitNode_uid in old_node.successors:
                            old_node.successors.remove(ExitNode_uid)
                            self.nodes[ExitNode_uid].predecessors_list[0].remove(old_node.uid)
                        if old_node.uid not in self.nodes[EntryNode_uid].successors:
                            self.nodes[EntryNode_uid].successors.append(old_node.uid)
            else:
                print("###ERROR:unhandle opcode:",old_node.opcode)
                # print(old_node.get_dict())     
                print_limited(old_node.get_dict())         
            #打印
            # for node in self.nodes:
            #     if self.nodes[node].function_name == Func_name:
            #         print("node:",self.nodes[node].get_dict())
                    
            # print("###",str(state.mstate.stack[-1]))
            # print(PreProcExpr(str(state.mstate.stack[-1])))
            # print(PreProcExpr(str(state.mstate.stack[-2])))
            # 
            if flag_detailed:
                if len(old_node.predecessors_list) > 0:
                    print("old_node.predecessors_list[0]",old_node.predecessors_list[0])
                    print_limited("old_node.symbol_vars_expr",old_node.symbol_vars_expr)
                    symbol_var_expr = Node.get_last_bracket_content(PreProcExpr(str(state.mstate.stack[-1])))
                    print_limited("symbol_var_expr:",symbol_var_expr)
                        
                print("post_hook INFO END")
            # old_node.remove_nodes()
            if flag_time:
                hook_end_time = time.time()
                duration = hook_end_time - hook_start_time
                self.deficheck_time+=duration
                if duration>1:
                    print("time!!!:")
                if Node.count>2 and old_node: #POST_HOOK
                    print("Func",old_node.function_name,"post_hook",posthook_opcode,"duration",duration,"hook_end_time",hook_end_time,"total",self.deficheck_time)
                # 统计函数及操作码用时
                if Func_name not in self.func_opcode_time:
                    self.func_opcode_time[Func_name] = {}
                    self.func_opcode_time[Func_name][old_node.opcode] = duration
                elif old_node.opcode not in self.func_opcode_time[Func_name]:
                    self.func_opcode_time[Func_name][old_node.opcode] = duration
                else:
                    self.func_opcode_time[Func_name][old_node.opcode] += duration
            return issues
        else:
            if flag_time:
                # hook_start_time = time.time()
                print("Func",Func_name,"pre_hook",prehook_opcode,hook_start_time)
        
        if prehook_opcode== "SSTORE":
            write_slot = state.mstate.stack[-1]
            write_value = state.mstate.stack[-2]
            # print("write_slot: \n",write_value)
            # if "transfer" in Func_name and "from" not in Func_name:
            #     print("write_value: \n",write_value)
            #     print("PreProcExpr(str(write_value))",PreProcExpr(str(write_value)))
            #     print("Node.get_last_bracket_content(PreProcExpr(str(write_value)))",Node.get_last_bracket_content(PreProcExpr(str(write_value))))
            if flag_detailed and len(Node.get_last_bracket_content(PreProcExpr(str(write_value))))<400:
                print("Node.get_last_bracket_content(PreProcExpr(str(write_value)))",Node.get_last_bracket_content(PreProcExpr(str(write_value))))
            
            # print("###write_value: ",str(write_value))
            # print("###write_value: ",str(simplify(write_value)))
            # print("###write_value2: ",PreProcExpr(str(simplify(write_value))))
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            # slot=simplify(write_slot),
                            # value=simplify(write_value),
                            node_type=NodeType.STATE_VARIABLES,
                            symbol_vars=[simplify(write_slot),simplify(write_value)],
                            ExitNode_uid=ExitNode_uid
                            )
            # old_node = self.nodes
            self.nodes[new_node.uid] = new_node
            Node.fix_sstore_prepredecessors(self.nodes,new_node.uid) #trick 修复SSTORE的前驱节点因为可能受到其他SLOAD的value为0的干扰
            #打印
            if flag_detailed:
                print(Func_name,"SSTORE:")
                for node in self.nodes:
                    if self.nodes[node].function_name == Func_name:
                        print_limited("node",self.nodes[node].get_dict())
            # start_node_ids = Node.find_start_node_ids(self.nodes, new_node.predecessors_list[0])
            # self.nodes[new_node.uid].start_node_ids=start_node_ids
            # print("start_node_ids: ",start_node_ids)
        elif prehook_opcode == "SLOAD":
            try:
                read_slot = simplify(state.mstate.stack[-1])
            except Exception as e:
                if Func_name == "constructor":
                    print("#WARNING:read_slot error:",e)
                else:
                    print("#ERROR:read_slot error:",e)
                    read_slot = ""
            if flag_detailed:
                print("SLOAD INFO:")
                read_slot_expr = Node.get_last_bracket_content(PreProcExpr(str(read_slot)))
                if len(read_slot_expr)<100:
                    print_limited("read_slot: ", read_slot_expr)
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,function_name=Func_name,
                            state=state,
                            node_type=NodeType.STATE_VARIABLES,
                            # slot=simplify(state.mstate.stack[-1]),
                            symbol_vars=[simplify(state.mstate.stack[-1])],
                            ExitNode_uid=ExitNode_uid
                            )
            # old_node = self.nodes
            # print("new_node.uid",new_node.uid)
            self.nodes[new_node.uid] = new_node
            if flag_detailed:
                print("SLOAD INFO END")
            #打印
            # for node in self.nodes:
            #     print("node:",self.nodes[node].get_dict())   
        elif prehook_opcode.startswith("LOG"):
            log_number = int(prehook_opcode[3:]) #1~4
            # print("LOG"+str(log_number)+" INFO")
            symbol_vars = []                  
            # for topic_index in range(-3,-3-log_number,-1):
            for topic_index in range(-3,-4-log_number,-1):
                # 检查堆栈长度，确保不会发生堆栈下溢
                if len(state.mstate.stack) > abs(topic_index):
                    topic = hex(state.mstate.stack[topic_index].value) if state.mstate.stack[topic_index].value else PreProcExpr(str(state.mstate.stack[topic_index]))
                    symbol_vars.append(simplify(state.mstate.stack[topic_index]))
                    if flag_detailed:
                        print("topic" + str(-3 - topic_index) + ":" + topic)
                else:
                    logging.warning(f"Stack underflow: trying to access index {topic_index} but stack length is {len(state.mstate.stack)}")
                    continue
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.LOG_INFORMATION,
                            symbol_vars=symbol_vars,
                            ExitNode_uid=ExitNode_uid
                            )
            self.nodes[new_node.uid] = new_node
            # for node in self.nodes:
            #     if self.nodes[node].function_name == Func_name:
            #         print("node:",self.nodes[node].get_dict())
            # LOG check
            if flag_detailed:
                print("LOG"+str(log_number)+" INFO END")
        elif prehook_opcode == "CALLER":
            if flag_detailed:
                try:
                    read_slot = simplify(state.mstate.stack[-1])
                    read_slot_expr = Node.get_last_bracket_content(PreProcExpr(str(read_slot)))
                    print_limited("read_slot: ", read_slot_expr)
                except Exception as e:
                    print("#ERROR:read_slot error:",e)
                    # return issues
                print("CALLER INFO:")
                
                
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,function_name=Func_name,
                            state=state,
                            # slot=simplify(state.mstate.stack[-1]),
                            node_type=NodeType.ENVIRONMENT_CONTEXT,
                            # symbol_vars=[simplify(state.mstate.stack[-1])],
                            ExitNode_uid=ExitNode_uid
                            )
            # old_node = self.nodes
            # print("new_node.uid",new_node.uid)
            self.nodes[new_node.uid] = new_node
            if flag_detailed:
                print("CALLER INFO END")
            #打印
            # for node in self.nodes:
            #     print("node:",self.nodes[node].get_dict())
        elif prehook_opcode == "ADDRESS": # 添加ADDRESS节点
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,function_name=Func_name,
                            state=state,
                            node_type=NodeType.ENVIRONMENT_CONTEXT,
                            ExitNode_uid=ExitNode_uid
                            )
            self.nodes[new_node.uid] = new_node
            if flag_detailed:
                print("ADDRESS INFO END")
        # elif prehook_opcode == "PUSH1":
        #     # if instructions[global_state.mstate.pc].get("argument") is not None:
        #     #                 argument = str(instructions[global_state.mstate.pc]["argument"])
        #     instruction = state.get_current_instruction()
        #     if instruction.get("argument") is not None:
        #         argument = str(instruction["argument"])
        #         if flag_detailed:
        #             print("PUSH1 INFO:")
        #             print("argument:",argument)
        #         if str(argument) == "1":
        #             new_node = Node(nodes=self.nodes,
        #                             contract_name=environment.active_account.contract_name,
        #                             function_name=Func_name,
        #                             state=state,
        #                             node_type=NodeType.DATA_FLOW,
        #                             ExitNode_uid=ExitNode_uid
        #                             )
        #             # old_node = self.nodes
        #             self.nodes[new_node.uid] = new_node
        #             if flag_detailed:
        #                 print("PUSH1 INFO END")
        elif prehook_opcode == "SHA3":
            if flag_detailed:
                print("SHA3 INFO")
            # print(PreProcExpr(str(simplify(state.mstate.stack[-1]))))
            # print(PreProcExpr(str(simplify(state.mstate.stack[-2]))))
            # print(PreProcExpr(str(state.mstate.stack[-3])))
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.DATA_FLOW,
                            ExitNode_uid=ExitNode_uid
                            )
            # old_node = self.nodes
            self.nodes[new_node.uid] = new_node
            #打印
            # for node in self.nodes:
            #     print("node:",self.nodes[node].get_dict())
            if flag_detailed:
                print("SHA3 INFO END")
        elif prehook_opcode == "CALLDATALOAD":
            # print("CALLDATALOAD INFO")
            if flag_detailed:
                print_limited("CALLDATALOAD stack[-1]",PreProcExpr(str(simplify(state.mstate.stack[-1]))))
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.DATA_FLOW,
                            ExitNode_uid=ExitNode_uid
                            )
            # old_node = self.nodes
            self.nodes[new_node.uid] = new_node
            if flag_detailed:
                print("CALLDATALOAD INFO END")
        # elif prehook_opcode == "PUSH20" or prehook_opcode == "PUSH32":
        elif prehook_opcode in ["AND","OR"]:
            if flag_detailed:
                print("PUSH INFO")
            if prehook_opcode == "AND":
                new_node = Node(nodes=self.nodes,
                                contract_name=environment.active_account.contract_name,
                                function_name=Func_name,
                                state=state,
                                node_type=NodeType.DATA_FLOW,
                                symbol_vars=[simplify(state.mstate.stack[-1]),simplify(state.mstate.stack[-2])],
                                ExitNode_uid=ExitNode_uid
                                )
                self.nodes[new_node.uid] = new_node
                # print(new_node.uid)
                # print_limited("PreProcExpr(str(state.mstate.stack[-1]))",PreProcExpr(str(state.mstate.stack[-1])))
                # print_limited("PreProcExpr(str(state.mstate.stack[-2]))",PreProcExpr(str(state.mstate.stack[-2])))
                # symbol_var = ""
                # if re.match(r"Concat\(\d+_calldata\[(4:35|36:67|68:99)\]\)", PreProcExpr(str(state.mstate.stack[-1]))):
                #     symbol_var = state.mstate.stack[-1]
                # elif re.match(r"Concat\(\d+_calldata\[(4:35|36:67|68:99)\]\)", PreProcExpr(str(state.mstate.stack[-2]))):
                #     symbol_var = state.mstate.stack[-2]
                # if str(symbol_var) != "":
                #     new_node = Node(nodes=self.nodes,
                #                     contract_name=environment.active_account.contract_name,
                #                     function_name=Func_name,
                #                     state=state,
                #                     node_type=NodeType.DATA_FLOW,
                #                     symbol_vars=[simplify(symbol_var)],
                #                     ExitNode_uid=ExitNode_uid
                #                     )
                #     self.nodes[new_node.uid] = new_node
                # # old_node = self.nodes
            else:
                new_node = Node(nodes=self.nodes,
                                contract_name=environment.active_account.contract_name,
                                function_name=Func_name,
                                state=state,
                                node_type=NodeType.DATA_FLOW,
                                symbol_vars=[simplify(state.mstate.stack[-1]),simplify(state.mstate.stack[-2])],
                                ExitNode_uid=ExitNode_uid
                                )
                self.nodes[new_node.uid] = new_node
                # 打印
                # for node in self.nodes:
                #     print("node:",self.nodes[node].get_dict())
            if flag_detailed:
                print_limited("PreProcExpr(str(state.mstate.stack[-1]))",PreProcExpr(str(state.mstate.stack[-1])))
                print_limited("PreProcExpr(str(state.mstate.stack[-2]))",PreProcExpr(str(state.mstate.stack[-2])))
                print("AND/OR INFO END")
        elif prehook_opcode in ["STOP","RETURN"]:#"REVERT":非正常结束，不处理
            # print("STOP/RETURN INFO")
            #打印
            # if flag_detailed:
            #     for node in self.nodes:
            #         if self.nodes[node].function_name == Func_name: #只处理当前函数的node
            #             print("node:",self.nodes[node].get_dict())
            # 判断函数类型，并调用对应检测方案
            # func_type,identity_dict = self.check_func_type(Func_name,self.nodes,flag_detailed)
            # if Func_name not in self.function_dict or self.function_dict[Func_name] != FunctionType.UNKNOWN:
            #     self.function_dict[Func_name] = func_type
            # if flag_detailed:
            #     print(Func_name," func_type: ",func_type,"identity_dict:",identity_dict)
            # if func_type == FunctionType.UNKNOWN or func_type == FunctionType.ERC_IGNORE:
            #     pass
            # elif "approve" in func_type.value or "Approval" in func_type.value:
            #     if flag_detailed:
            #         print("approve_handler")
            #     if func_type == FunctionType.ERC20_APPROVE:
            #         if flag_detailed:
            #             print("approve_handler ERC20")
            #         issues.extend(self.Approvehandler(1,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict)) #ERC20 approve
            #     elif func_type == FunctionType.ERC721_APPROVE:
            #         if flag_detailed:
            #             print("approve_handler ERC721")
            #         issues.extend(self.Approvehandler(2,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict)) #ERC721 approve
            #     elif func_type == FunctionType.ERC721_SETAPPROVALFORALL:
            #         if flag_detailed:
            #             print("approve_handler ERC721_SETAPPROVALFORALL")
            #         issues.extend(self.Approvehandler(3,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict)) #ERC721 setApprovalForAll
            #     elif func_type == FunctionType.ERC20_TRANSFER:
            #         pass
            #     else:
            #         if flag_detailed:
            #             print("ERROR:unhandled approve function:",Func_name)
            # elif "transfer" in func_type.value or "Transfer" in func_type.value:
            #     if func_type == FunctionType.ERC20_TRANSFER:
            #         if flag_detailed:
            #             print("transfer_handler ERC20")
            #         issues.extend(self.Transferfromhandler(FunctionType.ERC20_TRANSFER,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))
            #     elif func_type == FunctionType.ERC20_TRANSFERFROM:
            #         if flag_detailed:
            #             print("transfer_handler ERC20_TRANSFERFROM")
            #         issues.extend(self.Transferfromhandler(FunctionType.ERC20_TRANSFERFROM,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))
            #     elif func_type == FunctionType.ERC721_TRANSFERFROM: #or func_type == FunctionType.ERC721_SAFE_TRANSFER_FROM
            #         if flag_detailed:
            #             print("transfer_handler ERC721_TRANSFERFROM")
            #         issues.extend(self.Transferfromhandler(FunctionType.ERC721_TRANSFERFROM,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))  
            #     else:
            #         if flag_detailed:
            #             print("ERROR:unhandled transfer function:",Func_name)
            # elif "mint" in func_type.value or "burn" in func_type.value:
            #     if func_type == FunctionType.ERC20_MINT:
            #         if flag_detailed:
            #             print("mint_handler ERC20")
            #         issues.extend(self.Minthandler(FunctionType.ERC20_MINT,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))
            #     elif func_type == FunctionType.ERC20_BURN:
            #         if flag_detailed:
            #             print("burn_handler ERC20")
            #         issues.extend(self.Burnhandler(FunctionType.ERC20_BURN,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))
            #     elif func_type == FunctionType.ERC721_MINT:
            #         if flag_detailed:
            #             print("mint_handler ERC721")
            #         issues.extend(self.Minthandler(FunctionType.ERC721_MINT,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))
            #         pass
            #     elif func_type == FunctionType.ERC721_BURN:
            #         if flag_detailed:
            #             print("burn_handler ERC721")
            #         issues.extend(self.Burnhandler(FunctionType.ERC721_BURN,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))
            #         pass
            #     else:
            #         if flag_detailed:
            #             print("ERROR:unhandled mint/burn function:",Func_name)
            
            if flag_detailed:
                print("STOP/RETURN INFO END")
        elif prehook_opcode == "ADD" or prehook_opcode == "SUB":#
            # var1_expr = Node.get_last_bracket_content(PreProcExpr(str(simplify(state.mstate.stack[-1]))))
            # var2_expr = Node.get_last_bracket_content(PreProcExpr(str(simplify(state.mstate.stack[-2]))))
            # 检查 var1_expr 和 var2_expr 是否等于 "1" 或者匹配 "calldata[\d+:\d+]" 的结构
            # if var1_expr == "1" or var2_expr == "1" \
            #     or re.fullmatch(r'_calldata\[\d+:\d+\]', var1_expr) or re.fullmatch(r'\d+_calldata\[\d+:\d+\]', var2_expr):
            # # if "1" in [var1_expr,var2_expr]:
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.DATA_FLOW,
                            symbol_vars=[simplify(state.mstate.stack[-1]),simplify(state.mstate.stack[-2])],
                            ExitNode_uid=ExitNode_uid
                            )
            self.nodes[new_node.uid] = new_node
            if flag_detailed:
                # var1_expr = Node.get_last_bracket_content(PreProcExpr(str(simplify(state.mstate.stack[-1]))))
                # var2_expr = Node.get_last_bracket_content(PreProcExpr(str(simplify(state.mstate.stack[-2]))))
                var1_expr = Node.get_last_bracket_content(symbol_var_preprocess(simplify(state.mstate.stack[-1])))
                var2_expr = Node.get_last_bracket_content(symbol_var_preprocess(simplify(state.mstate.stack[-2])))
                print_limited("var1_expr:",var1_expr)
                print_limited("var2_expr:",var2_expr)
                if prehook_opcode == "ADD":
                    print("ADD INFO END") #
                else:
                    print("SUB INFO END") #
        elif prehook_opcode == "CALL":
            gas = state.mstate.stack[-1]
            to = state.mstate.stack[-2]
            value = state.mstate.stack[-3]
            memory_input_offset = state.mstate.stack[-4]
            memory_input_size = state.mstate.stack[-5]
            memory_output_offset = state.mstate.stack[-6]
            memory_output_size = state.mstate.stack[-7]
              
            
            if flag_detailed:
                print("CALL INFO:")
                print_limited("gas",PreProcExpr(str(simplify(gas))))
                print_limited("to",PreProcExpr(str(simplify(to))))
                print_limited("value",PreProcExpr(str(simplify(value))))
                print_limited("memory_input_size",PreProcExpr(str(memory_input_size)))
                print_limited("memory_input_offset",PreProcExpr(str(memory_input_offset)))
                # print("call_data: ",PreProcExpr(str(call_data._calldata)))
                # print("call_data.concrete(None): ",PreProcExpr(str(call_data.concrete(None)))) # 得到list，前四个字节为函数选择器
                # print("call_data:\n",str(call_data._calldata.raw))
                # print("call_data: ",PreProcExpr(str(call_data._calldata.raw)))
                # print("memory_output_offset: ",PreProcExpr(str(memory_output_offset)))
                # print("memory_output_size: ",PreProcExpr(str(memory_output_size)))
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.CONTROL_FLOW,
                            symbol_vars=[simplify(gas),simplify(to),simplify(value),simplify(memory_input_offset),simplify(memory_input_size),simplify(memory_output_offset),simplify(memory_output_size)],
                            ExitNode_uid=ExitNode_uid
                            )
            self.nodes[new_node.uid] = new_node
            if flag_detailed:
                print("CALL INFO END")
        elif prehook_opcode == "DELEGATECALL":
            print("DELEGATECALL Node")
            # print("func_name: ",Func_name)
            memory_output_size, memory_output_offset = state.mstate.stack[-6:-4]
            # gas, to = global_state.mstate.pop(2)
            gas, to = state.mstate.stack[-1], state.mstate.stack[-2]
            # value =  0
            memory_input_offset = state.mstate.stack[-3]
            memory_input_size = state.mstate.stack[-4]
            call_data = get_call_data(state, memory_input_offset, memory_input_size)
            if flag_detailed:
                print("DELEGATECALL INFO: ")
                print_limited("gas ",PreProcExpr(str(simplify(gas))))
                print_limited("to ",PreProcExpr(str(simplify(to))))
                # print_limited("value ",PreProcExpr(str(simplify(value))))
                # print("memory_input_offset: ",PreProcExpr(str(simplify(memory_input_offset))))
                # print("memory_input_size: ",PreProcExpr(str(simplify(memory_input_size))))
                print("call_data ",PreProcExpr(str(call_data._calldata)))
                # print("memory_output_offset: ",PreProcExpr(str(simplify(memory_output_offset))))
                # print("memory_output_size: ",PreProcExpr(str(simplify(memory_output_size))))
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.CONTROL_FLOW,
                            symbol_vars=[simplify(gas),simplify(to),simplify(memory_input_offset),simplify(memory_input_size),simplify(memory_output_offset),simplify(memory_output_size)],
                            ExitNode_uid=ExitNode_uid
                            )
            self.nodes[new_node.uid] = new_node
            # print("DELEGATECALL Node",new_node.uid)
            if flag_detailed:
                print("DELEGATECALL INFO END")            
        elif prehook_opcode == "JUMP" or prehook_opcode == "JUMPI":
            counter = simplify(state.mstate.stack[-1])
            if prehook_opcode == "JUMPI":
                b = simplify(state.mstate.stack[-2])
                symbol_vars = [counter,b]
            else:
                symbol_vars = [counter]
            if flag_detailed:
                pass
                # for symbol_var in symbol_vars:
                #     print("symbol_var: ",Node.get_last_bracket_content(PreProcExpr(str(symbol_var))))
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.CONTROL_FLOW,
                            symbol_vars=symbol_vars,
                            ExitNode_uid=ExitNode_uid
                            )
            self.nodes[new_node.uid] = new_node
            #查找JUMP/JUMPI前驱的JUMPDEST或JUMPI结点
            new_node.find_edge(self.nodes,ExitNode_uid)
            if flag_detailed:
                print("JUMP/JUMPI INFO END")
        elif prehook_opcode == "JUMPDEST":
            if flag_detailed:
                print("JUMPDEST")
            symbol_vars = []
            new_node = Node(nodes=self.nodes,
                            contract_name=environment.active_account.contract_name,
                            function_name=Func_name,
                            state=state,
                            node_type=NodeType.CONTROL_FLOW,
                            symbol_vars=symbol_vars,
                            ExitNode_uid=ExitNode_uid
                            )
            self.nodes[new_node.uid] = new_node
            new_node.find_edge(self.nodes,ExitNode_uid)
            if flag_detailed:
                print("JUMPDEST INFO END")
        elif prehook_opcode == "ISZERO":
            simplify_time_start =time.time()
            symbol_var = simplify(state.mstate.stack[-1])
            if flag_detailed:
                if flag_time:
                    print("time@@ simplify",time.time()-simplify_time_start)
                # symbol_var_expr=PreProcExpr(str(symbol_var))
                symbol_var_expr=symbol_var_preprocess(symbol_var)
                if flag_time:
                    print("time@@@ PreProcExpr",time.time()-simplify_time_start)
                symbol_var_expr = Node.get_last_bracket_content(symbol_var_expr)
                if flag_time:
                    print("time@@@@ Node.get_last_bracket_content",time.time()-simplify_time_start)
                print("ISZERO INFO:")
                print_limited("symbol_var: ",symbol_var_expr)
            new_node = Node(nodes=self.nodes,
                        contract_name=environment.active_account.contract_name,
                        function_name=Func_name,
                        state=state,
                        node_type=NodeType.DATA_FLOW,
                        symbol_vars=[symbol_var],
                        ExitNode_uid=ExitNode_uid
                        )
            self.nodes[new_node.uid] = new_node
            # if time.time()-simplify_time_start>10:
            #     print("ISZERO symbol_vars:",symbol_var)
            if flag_time:
                print("time@@@@@ Node",time.time()-simplify_time_start)
            if flag_detailed:
                print("ISZERO INFO END")
        # elif prehook_opcode == "MSTORE":
            # print("MSTORE INFO")
            # mstart = simplify(state.mstate.stack[-1])
            # value = state.mstate.stack[-2] #simplify()
            # if str(mstart) == '0' or str(mstart) == '32':
            #     self.memory_dict[Func_name][str(mstart)] = Node.get_last_bracket_content(PreProcExpr(str(value)))
            # print("mstart:",Node.get_last_bracket_content(PreProcExpr(str(mstart))))
            # print("value:",Node.get_last_bracket_content(PreProcExpr(str(value))))
            # print("self.memory_dict",self.memory_dict)
            # pass
        if flag_time:
            hook_end_time = time.time()
            duration = hook_end_time - hook_start_time
            self.deficheck_time+=duration
            if duration>1:
                print("time!!!:")
            if Node.count>2 and old_node: #POST_HOOK
                print("Func",old_node.function_name,"post_hook",posthook_opcode,"duration",duration,"hook_end_time",hook_end_time,"total",self.deficheck_time)
            else:
                print("Func",Func_name,"pre_hook",prehook_opcode,"duration",duration,"hook_end_time",hook_end_time,"total",self.deficheck_time)    
                # 统计函数及操作码用时
                if Func_name not in self.func_opcode_time:
                    self.func_opcode_time[Func_name] = {}
                    self.func_opcode_time[Func_name][prehook_opcode] = duration
                elif prehook_opcode not in self.func_opcode_time[Func_name]:
                    self.func_opcode_time[Func_name][prehook_opcode] = duration
                else:
                    self.func_opcode_time[Func_name][prehook_opcode] += duration
            

        return issues
    
    def defi_handle(self): #ERC20/ERC721检测approver/transfer/transferFrom
        print("=== detect ERC20/ERC721 approve/transfer/transferFrom ===")
        issues = []
        # 判断函数类型，并调用对应检测方案
        for Func_name in self.function_dict:
            func_type,identity_dict = self.check_func_type(Func_name,self.nodes,flag_detailed)
            if Func_name not in self.function_dict or self.function_dict[Func_name] != FunctionType.UNKNOWN:
                self.function_dict[Func_name] = func_type
            if flag_detailed:
                print(Func_name," func_type: ",func_type,"identity_dict:",identity_dict)
            if func_type == FunctionType.UNKNOWN or func_type == FunctionType.ERC_IGNORE:
                pass
            elif "approve" in func_type.value or "Approval" in func_type.value or "permit" in func_type.value:
                if flag_detailed:
                    print("approve_handler")
                if func_type == FunctionType.ERC20_APPROVE:
                    if flag_detailed:
                        print("approve_handler ERC20")
                    issues.extend(self.Approvehandler(FunctionType.ERC20_APPROVE,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict)) #ERC20 approve
                elif func_type == FunctionType.ERC20_PERMIT:
                    if flag_detailed:
                        print("approve_handler ERC20_PERMIT")
                    issues.extend(self.Approvehandler(FunctionType.ERC20_PERMIT,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))
                elif func_type == FunctionType.ERC721_APPROVE:
                    if flag_detailed:
                        print("approve_handler ERC721")
                    issues.extend(self.Approvehandler(FunctionType.ERC721_APPROVE,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict)) #ERC721 approve
                elif func_type == FunctionType.ERC721_SETAPPROVALFORALL:
                    if flag_detailed:
                        print("approve_handler ERC721_SETAPPROVALFORALL")
                    issues.extend(self.Approvehandler(FunctionType.ERC721_SETAPPROVALFORALL,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict)) #ERC721 setApprovalForAll
                else:
                    if flag_detailed:
                        print("ERROR:unhandled approve function:",Func_name)
            elif "transfer" in func_type.value or "Transfer" in func_type.value:
                if func_type == FunctionType.ERC20_TRANSFER:
                    if flag_detailed:
                        print("transfer_handler ERC20")
                    issues.extend(self.Transferfromhandler(FunctionType.ERC20_TRANSFER,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))
                elif func_type == FunctionType.ERC20_TRANSFERFROM:
                    if flag_detailed:
                        print("transfer_handler ERC20_TRANSFERFROM")
                    issues.extend(self.Transferfromhandler(FunctionType.ERC20_TRANSFERFROM,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))
                elif func_type == FunctionType.ERC721_TRANSFERFROM: #or func_type == FunctionType.ERC721_SAFE_TRANSFER_FROM
                    if flag_detailed:
                        print("transfer_handler ERC721_TRANSFERFROM")
                    issues.extend(self.Transferfromhandler(FunctionType.ERC721_TRANSFERFROM,nodes=self.nodes,func_name=Func_name,identity_dict=identity_dict))  
                else:
                    if flag_detailed:
                        print("ERROR:unhandled transfer function:",Func_name)
        return issues
    
    def defi_handle2(self): # 检测ERC721/1155 mint/burn
        print("=== detect ERC721/1155 mint/burn ===")
        issues = []
        # 判断函数类型，并调用对应检测方案（TODO：由于在defi_handle后执行，如果如果直接识别不易，后续可以集合defi_handle的结果，但是必须运行defi_handle）
        for Func_name in self.function_dict:
            # 过滤掉无关函数
            # if Func_name in ["constructor","fallback"]:
            #     continue
            if self.function_dict[Func_name] != FunctionType.UNKNOWN:
                continue
            # 通过核心结构检查是否是NFT-mint/burn
            print("> func_name",Func_name)
            # TODO:只检测最常见NFT-burn/mint前10的函数签名，所有此部分忽略
            # 如果fun_name不包含NFT_MB_func_sign_dict中任一key，则跳过
            if not any(func_sign in Func_name for func_sign in NFT_MB_func_sign_dict) \
                and (
                    'burn' not in Func_name and 'mint' not in Func_name
                ):
                print("skip")
                continue
            else:
                for func_sign in NFT_MB_func_sign_dict:
                    if func_sign in Func_name:
                        key = func_sign
                        self.function_dict[Func_name] = NFT_MB_func_sign_dict[key]
                        print("NFT_MB_func_sign_dict[",key,"]:",NFT_MB_func_sign_dict[key])
                        break        
                
            cur_func_type,state = self.check_nft_MB(Func_name,self.nodes)
            # 检查函数一致性
            if self.function_dict[Func_name] in [FunctionType.ERC721_BURN,FunctionType.ERC1155_BURN,FunctionType.NFT_BURN] \
                and cur_func_type in [FunctionType.ERC721_MINT,FunctionType.ERC1155_MINT,FunctionType.NFT_MINT]:
                print("ERROR:FunctionType inconsistent:",Func_name,"burn_func_name with mint behavior")
                # description_head = "FunctionType inconsistent:"
                description = "FunctionType inconsistent: burn_func_name with mint behavior"
                issue = ret_issues(state= state, description_tail=description)
                issues.append(issue)
            elif self.function_dict[Func_name] in [FunctionType.ERC721_MINT,FunctionType.ERC1155_MINT,FunctionType.NFT_MINT] \
                and cur_func_type in [FunctionType.ERC721_BURN,FunctionType.ERC1155_BURN,FunctionType.NFT_BURN]:
                print("ERROR:FunctionType inconsistent:",Func_name,"mint_func_name with burn behavior")
                # description_head = "FunctionType inconsistent:"
                description = "FunctionType inconsistent: mint_func_name with burn behavior"
                issue = ret_issues(state= state, description_tail=description)
                issues.append(issue)
            if cur_func_type not in [FunctionType.ERC1155_TRANSFERFROM]: 
                #TODO:ERC1155_TRANSFERFROM类型可能存在误报，所以此处不处理
                self.function_dict[Func_name] = cur_func_type
            #TODO 检查函数正确性
            if cur_func_type in [FunctionType.ERC721_MINT,FunctionType.ERC721_BURN,FunctionType.ERC1155_MINT,FunctionType.ERC1155_BURN]:
                issues.extend(self.NFTMBhandler(cur_func_type,nodes=self.nodes,func_name=Func_name))

        return issues
            
    
    # 检查单个函数的type
    def check_func_type(self,Func_name:str,nodes,flag_detailed=False):
        if flag_detailed:
            print("check_func_type:",Func_name)
        core_structures = []
        log_structures = []
        if Func_name in self.function_dict and self.function_dict[Func_name] != FunctionType.UNKNOWN:
            func_type = self.function_dict[Func_name]
        else:
            func_type = FunctionType.UNKNOWN #初始化为UNKNOWN
            for node in nodes:
                if nodes[node].function_name != Func_name: #只处理当前函数的node
                    continue
                opcode = nodes[node].opcode
                if opcode == "SSTORE":
                    slot = nodes[node].symbol_vars_expr[0]
                    value = nodes[node].symbol_vars_expr[1]
                    # slot_predecessors = nodes[node].predecessors_list[0]
                    slot_start_node_ids = Node.find_start_node_ids(nodes, nodes[node].predecessors_list[0])
                    # value_predecessors = nodes[node].predecessors_list[1]
                    value_start_node_ids = Node.find_start_node_ids(nodes, nodes[node].predecessors_list[1])
                    identity = identity_extract(slot)
                    core_structures.append((slot, value, slot_start_node_ids, value_start_node_ids,identity))
            if flag_detailed:
                # print(Func_name,"core_structures",core_structures)
                # 省略过长的slot和value
                print(Func_name)
                print_limited("core_structures",core_structures)
                            
                if opcode.startswith("LOG"):
                    log_hash = nodes[node].log_hash
                    log_number = int(opcode[3:])
                    vars = nodes[node].symbol_vars_expr
                    # var是一个list,包含了所有的symbol_vars_expr，每个查找一个起始结点
                    vars_start_node_ids = [Node.find_start_node_ids(nodes, uid) for uid in nodes[node].predecessors_list]
                    log_structures.append((log_hash, log_number, vars, vars_start_node_ids))
                    
            # 匹配参数类型
            ## 根据函数签名和核心结构，并确定identity对应的核心结构
            if Func_name == "constructor":
                func_type = FunctionType.CONSTRUCTOR
            elif Func_name == "fallback":
                func_type = FunctionType.FALLBACK
            elif any(func in Func_name for func in ["approveAndCall(address,uint256,bytes)","approve(address,uint256)"]): #approve
                if len(core_structures) > 0 :
                    slot_start_node_ids = core_structures[-1][2]
                    if len(slot_start_node_ids) == 2:
                        func_type = FunctionType.ERC20_APPROVE
                    elif len(slot_start_node_ids) == 1:
                        func_type = FunctionType.ERC721_APPROVE
            elif "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)" in Func_name or "0xd505accf" in Func_name:
                if len(core_structures) > 0:
                    func_type = FunctionType.ERC20_PERMIT
            elif "setApprovalForAll(address,bool)" in Func_name:
                if len(core_structures) > 0:
                    func_type = FunctionType.ERC721_SETAPPROVALFORALL
            elif "transfer(address,uint256)" in Func_name:
                if len(core_structures) > 0:
                    func_type = FunctionType.ERC20_TRANSFER
            elif any(func in Func_name for func in ["transferFrom(address,address,uint256)","safeTransferFrom(address,address,uint256)","safeTransferFrom(address,address,uint256)"]): #transferFrom
                if len(core_structures) > 0:
                    # 是存在包含两个keccak256_512的结构
                    for slot, value, slot_start_node_ids, value_start_node_ids,_ in core_structures:
                        if len(slot_start_node_ids) == 2 \
                            and check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) \
                            and check_roles(nodes[slot_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM):
                            func_type = FunctionType.ERC20_TRANSFERFROM
                            break
                    if func_type == FunctionType.UNKNOWN:
                        for slot, value, slot_start_node_ids, value_start_node_ids,_ in core_structures:
                            if len(slot_start_node_ids) == 1 \
                                and len(value_start_node_ids) == 1\
                                and check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM2):#_owners[tokenId] = to;
                                func_type = FunctionType.ERC721_TRANSFERFROM
                            
            # elif "mint(address,uint256)" in Func_name: #mint
            #     if len(core_structures) > 0:
            #         for slot, value, slot_start_node_ids, value_start_node_ids,_ in core_structures:
            #             if len(slot_start_node_ids) == 1 \
            #                 and check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM2):
            #                 func_type = FunctionType.ERC721_MINT
            #                 break
            #             # elif len(slot_start_node_ids) == 1 \
            #             #     and check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM1):
            #             #     func_type = FunctionType.ERC20_MINT
            #             #     break  
            #         if func_type == FunctionType.UNKNOWN: #TODO:根据条件判断
            #             func_type = FunctionType.ERC20_MINT      
            # elif "burn(uint256)" in Func_name: #burn
            #     if len(core_structures) > 0:
            #         for slot, value, slot_start_node_ids, value_start_node_ids,_ in core_structures:
            #             if len(slot_start_node_ids) == 1 \
            #                 and check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER): 
            #                 func_type = FunctionType.ERC20_BURN
            #                 break
            #             elif len(slot_start_node_ids) == 1 \
            #                 and check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM1):
            #                 func_type = FunctionType.ERC721_BURN
            #                 break
            #     if func_type == FunctionType.UNKNOWN:
            #         print("ERROR: burn function not check",Func_name)
            
            elif any(func in Func_name for func in ["totalSupply()","balanceOf(address)","allowance(address,address)",
                            "name()", "symbol()", "decimals()","ownerOf(uint256)"
                            "getApproved(uint256)","isApprovedForAll(address,address)"]):
                func_type = FunctionType.ERC_IGNORE
            
            ## 根据事件确定函数类型（log_structures:log_hash, log_number, vars, vars_start_node_ids）
            if func_type == FunctionType.UNKNOWN:
                if len(log_structures)>0:
                    log_number = log_structures[0][1]
                    if not all([log[1] == log_number for log in log_structures]):
                        print("ERROR: log_number is not the same in",Func_name)
                        return func_type,{}
                    if log_number == 1:
                        # func_type = FunctionType.ERC20_TRANSFER
                        # 识别函数类型
                        pass
            # el
            #0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925 approve log
            # elif func_type == FunctionType.ERC20_TRANSFER:
                    # log_hash_list = []
                    # if log_number == 2
                    # for log_hash, log_number, vars, vars_start_node_ids in log_structures:

            
            
            ## 根据核心结构确定函数类型
            if func_type == FunctionType.UNKNOWN:# 根据核心结构确定函数类型
                param_types = re.findall(r'\((.*?)\)', Func_name)
                if param_types:
                    param_types = param_types[0].split(',')
                else:
                    if flag_detailed:
                        print("no parameter function: Func_name",Func_name)
                    return func_type,{}
                if len(param_types) == 2:
                    # print("param_types",param_types)
                    # print("param_types",param_types[0])
                    # print("param_types",param_types[1])
                    if param_types[0] == "address" and param_types[1] == "uint256":
                        # print("core_structures",core_structures)
                        if len(core_structures) != 0:   
                            # 可能为approve、transfer或mint函数
                            # ERC721.approve判断:len(slot_start_node_ids)=1,len(value_start_node_ids)=2且value不包含加减号
                            func_type = FunctionType.ERC721_APPROVE
                            for slot, value, slot_start_node_ids, value_start_node_ids,_ in core_structures:
                                if len(slot_start_node_ids) != 1 or len(value_start_node_ids) != 2 or re.search(r'[+-]', value):
                                    func_type = FunctionType.UNKNOWN
                                    break
                            if func_type == FunctionType.UNKNOWN:
                                # ERC721.approve判断:len(slot_start_node_ids)=1,len(value_start_node_ids)=2且value不包含加减号
                                func_type = FunctionType.ERC20_APPROVE
                                for slot, value, slot_start_node_ids, value_start_node_ids,_ in core_structures:
                                    if len(slot_start_node_ids) != 2 or len(value_start_node_ids) != 1:
                                        func_type = FunctionType.UNKNOWN
                                        break
                            # if func_type == FunctionType.UNKNOWN:       
                            # else:
                            #     func_type = FunctionType.UNKNOWN
                            pass
                        else:
                            print("WARNING: core_structures is empty",Func_name)
                    elif param_types[0] == "address" and param_types[1] == "bool":
                        if len(core_structures) != 1:
                            #可能为ERC721.setApprovalForAll函数或ERC20.freezeAccount(address,bool) 
                            func_type = FunctionType.ERC721_SETAPPROVALFORALL
                            for slot, value, slot_start_node_ids, value_start_node_ids,_ in core_structures:
                                if "If" in value:
                                    func_type = FunctionType.UNKNOWN
                                    break
                        else:
                            print("WARNING: core_structures is empty",Func_name)    
                        # print("core_structures",core_structures)
        
        #识别是否有identity
        identity_dict = {}
        if func_type == FunctionType.UNKNOWN:
            return func_type,identity_dict
        else:
            for core_structure in core_structures:
                    if core_structure[4] and core_structure[4] != -1:
                        if core_structure[4] not in identity_dict:
                            identity_dict[core_structure[4]] = IdentityType.UNKNOWN
        # elif func_type == FunctionType.ERC20_APPROVE:
        #     if len(core_structures) == 0:
        #         pass
        #     else:
        #         for core_structure in core_structures:
        #             if core_structure[4] and core_structure[4] != -1:
        #                 if core_structure[4] not in identity_dict:
        #                     identity_dict[core_structure[4]] = IdentityType.ERC20_ALLOWANCE           
        # elif func_type == FunctionType.ERC721_APPROVE:
        #     if len(core_structures) == 0:
        #         pass
        #     else:
        #         for core_structure in core_structures:
        #             if core_structure[4] and core_structure[4] != -1:
        #                 if core_structure[4] not in identity_dict:
        #                     identity_dict[core_structure[4]] = IdentityType.ERC721_OWNER
        #                 else:
        #                     identity_dict[core_structure[4]] = IdentityType.ERC721_BALANCE
        #     pass
        # elif func_type == FunctionType.ERC721_SETAPPROVALFORALL:
        #     if len(core_structures) == 0:
        #         pass
        #     else:
        #         for core_structure in core_structures:
        #             if core_structure[4] and core_structure[4] != -1:
        #                 if core_structure[4] not in identity_dict:
        #                     identity_dict[core_structure[4]] = IdentityType.ERC721_OPERATORAPPROVAL
        #     pass
        # elif func_type == FunctionType.ERC20_TRANSFER:
        #     if len(core_structures) == 0:
        #         pass
        #     else:
        #         for core_structure in core_structures:
        #             if core_structure[4] and core_structure[4] != -1:
        #                 if core_structure[4] not in identity_dict:
        #                     identity_dict[core_structure[4]] = IdentityType.ERC20_BALANCE
        # elif func_type == FunctionType.ERC20_TRANSFERFROM:
        #     if len(core_structures) == 0:
        #         pass
        #     else:
        #         for core_structure in core_structures:
        #             if core_structure[4] and core_structure[4] != -1:
        #                 if core_structure[4] not in identity_dict:
        #                     slot_start_node_ids = core_structure[2]
        #                     if len(slot_start_node_ids) == 2:
        #                         identity_dict[core_structure[4]] = IdentityType.ERC20_ALLOWANCE
        #                     elif len(slot_start_node_ids) == 1:
        #                         identity_dict[core_structure[4]] = IdentityType.ERC20_BALANCE
        #                     else:
        #                         print("ERROR:ERC20_TRANSFERFROM identity_dict error")                
        # elif func_type == FunctionType.ERC721_TRANSFERFROM:
        #     if len(core_structures) == 0:
        #         pass
        #     else:
        #         for core_structure in core_structures:
        #             if core_structure[4] and core_structure[4] != -1:
        #                 if core_structure[4] not in identity_dict:
        #                     # identity_dict[core_structure[4]] = IdentityType.ERC721_OPERATORAPPROVAL
        #                     if check_roles(nodes[core_structure[2][0]].symbol_vars_expr[0],Role.PARAM3) :
        #                         identity_dict[core_structure[4]] = IdentityType.ERC721_OWNER
        #                     else:
        #                         identity_dict[core_structure[4]] = IdentityType.ERC721_BALANCE
        # # elif func_type == FunctionType.ERC
        # else:
        #     pass

        return func_type,identity_dict
            
    # 通过核心结构检查是否是NFT-mint/burn
    def check_nft_MB(self,Func_name,nodes):
        # ERC721需要两个核心结构共同确定
        flag_ERC721_burn_balance = False # _balances[owner] -= 1; // owner = ownerOf(tokenId);
        flag_ERC721_burn_owner = False # delete _tokenOwners[tokenId];
        flag_ERC721_mint_balance = False
        flag_ERC721_mint_owner = False
        # ERC1155需要和safeBatchTransferFrom区别
        flag_ERC1155_burn_balance = False
        flag_ERC1155_mint_balance = False
        state = None
        for node_id in nodes:
            # 只检查当前函数
            if Func_name != nodes[node_id].function_name:
                continue
            # 只检查核心结构
            if nodes[node_id].opcode != "SSTORE":
                continue
            state = nodes[node_id].state
            slot_expr = nodes[node_id].symbol_vars_expr[0]
            value_expr = nodes[node_id].symbol_vars_expr[1]
            slot_start_node_ids,slot_sload_count = Node.find_start_node_ids(nodes, nodes[node_id].predecessors_list[0],ret_sload_count= True)
            value_start_node_ids,value_sload_count = Node.find_start_node_ids(nodes, nodes[node_id].predecessors_list[1],ret_sload_count= True)
            # 打印变量
            print(f"slot_expr: {slot_expr}")
            print(f"value_expr: {value_expr}")
            print(f"slot_start_node_ids: {slot_start_node_ids}, slot_sload_count: {slot_sload_count}")
            print(f"value_start_node_ids: {value_start_node_ids}, value_sload_count: {value_sload_count}")
            # 检查
            if len(slot_start_node_ids) == 2 \
                and (check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)) \
                and (check_roles(nodes[slot_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[slot_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER)):
                # slot满足条件：二维映射，有两个key来自参数
                # 检查value
                if len(value_start_node_ids) == 3 \
                    and (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)) \
                    and (check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER)) \
                    and (check_roles(nodes[value_start_node_ids[2]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[2]].symbol_vars_expr[0],Role.SENDER)):
                    # value满足条件：三个key来自参数
                    if '115792089237316195423570985008687907853269984665640564039457584007913129639935' in value_expr: #check_opcode(nodes,nodes[node_id].predecessors_list[1],"SUB") \
                        # 返回函数类型：ERC1155的burn函数
                        flag_ERC1155_burn_balance = True
                        # return FunctionType.ERC1155_BURN
                    elif check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"):
                        flag_ERC1155_mint_balance = True
                        # return FunctionType.ERC1155_MINT
                if len(value_start_node_ids) == 2 and value_sload_count ==1:
                    if check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"):
                        flag_ERC1155_mint_balance = True
            elif len(slot_start_node_ids) == 2 and slot_sload_count == 3:
                if value_expr == '0':
                    # _holderTokens[owner].remove(tokenId); ERC721 set save tokenId (replace balance)
                    flag_ERC721_burn_balance = True
            elif len(slot_start_node_ids) == 1 : #and (check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)) # 放宽条件，以便检测到tokenId来自storage的
                # slot满足条件：一维映射，key来自参数，
                if slot_sload_count >= 1: #且是嵌套映射
                    # 检查value
                    if len(value_start_node_ids) == 1 \
                        and (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)):
                        if value_sload_count >= 2:
                            if value_sload_count > 2:
                                if value_sload_count >= 3 \
                                    and (
                                        minus_one in value_expr
                                        or check_opcode(nodes,nodes[node_id].predecessors_list[1],"SUB")
                                    ) :
                                    # value满足条件：-1 (2^20-1)
                                    flag_ERC721_burn_balance = True  # 结构体BURN
                                else:
                                    print("#ERROR:value_sload_count > 1")
                            # 嵌套映射
                            if '115792089237316195423570985008687907853269984665640564039457584007913129639935' in value_expr:#
                                # value满足条件：-1 (2^32-1)
                                flag_ERC721_burn_balance = True 
                            elif check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"):
                                flag_ERC721_mint_balance = True
                else: # slot_sload_count == 0
                    if len(value_start_node_ids) == 1 \
                        and (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)):
                        if value_sload_count == 1:
                            # value_expr以逗号分割，最后一位是否位0
                            if ',' in value_expr\
                                and value_expr.split(',')[-1].strip() == '0':
                                flag_ERC721_burn_owner = True
                            else:
                                if check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"):
                                    flag_ERC721_mint_balance = True
                                if (
                                    minus_one in value_expr
                                    or check_opcode(nodes,nodes[node_id].predecessors_list[1],"SUB")
                                ):
                                    flag_ERC721_burn_balance = True
                        elif value_sload_count == 2: 
                            if ',' in value_expr\
                                and value_expr.split(',')[-1].strip() == '0':
                                flag_ERC721_burn_owner = True
                            
                    elif len(value_start_node_ids) == 2 \
                        and (
                            (check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER))
                            or ((check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)))
                        ):
                        # and (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)) \
                        if value_sload_count == 1:
                            flag_ERC721_mint_owner = True
                            if (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER))\
                                and check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"): # TODO：可能导致721误报为1155
                                flag_ERC1155_mint_balance = True
                        elif value_sload_count == 2:
                            flag_ERC721_mint_owner = True # 结构体BURN
            elif len(slot_start_node_ids) == 1:
                if slot_sload_count == 0:
                    if len(value_start_node_ids) == 2 \
                        and (
                            check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) \
                            or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER) \
                            or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) \
                            or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER)
                        ):
                        if value_sload_count == 1:
                            # print("value_expr.split(',')[-1].strip()",value_expr.split(',')[-1].strip())
                            if ',' in value_expr\
                                and check_roles(value_expr.split(',')[-1].strip(),Role.PARAM):
                                flag_ERC721_mint_balance = True # 结构体BURN
                        elif value_sload_count == 2:
                            flag_ERC721_mint_owner = True # BURN的SHA3没有正确查找前驱结点
                    elif len(value_start_node_ids) == 1\
                        and check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM):
                        if value_sload_count == 1: #ERC721 balance[to] +=1
                            flag_ERC721_mint_balance = True
                elif slot_sload_count == 1:
                    if len(value_start_node_ids) == 2\
                        and (
                            check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) \
                            or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER) \
                            or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) \
                            or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER)
                        ):
                        if value_sload_count == 2:
                            flag_ERC721_mint_balance = True
        
        # ERC1155
        if flag_ERC1155_burn_balance and flag_ERC1155_mint_balance:
            return FunctionType.ERC1155_TRANSFERFROM,state
        elif flag_ERC1155_burn_balance:
            return FunctionType.ERC1155_BURN,state
        elif flag_ERC1155_mint_balance:
            return FunctionType.ERC1155_MINT,state
        # ERC721     
        if flag_ERC721_burn_balance and flag_ERC721_burn_owner:
            return FunctionType.ERC721_BURN,state
        if flag_ERC721_mint_balance and flag_ERC721_mint_owner:
            return FunctionType.ERC721_MINT,state
        print("flag_ERC721_burn_balance and flag_ERC721_burn_owner",flag_ERC721_burn_balance,flag_ERC721_burn_owner)
        print("flag_ERC721_mint_balance and flag_ERC721_mint_owner",flag_ERC721_mint_balance,flag_ERC721_mint_owner)
        
        return FunctionType.UNKNOWN,state
                            
    def NFTMBhandler(self,nftmbType:FunctionType,nodes,func_name):  #NFT mint/burn
        issues = []
        # 检查内容：
        # 1.检查函数名称和行为不一致 (函数前已实现)
        # 2.检查是否没有更新所有者余额
        # 3.检查所有权是否存在问题
         # ERC721需要两个核心结构共同确定
        flag_ERC721_burn_balance = False # _balances[owner] -= 1; // owner = ownerOf(tokenId);
        flag_ERC721_burn_owner = False # delete _tokenOwners[tokenId];
        flag_ERC721_mint_balance = False
        flag_ERC721_mint_owner = False
        # ERC1155需要和safeBatchTransferFrom区别 (已实现)
        flag_ERC1155_burn_balance = False
        flag_ERC1155_mint_balance = False
        for node_id in nodes:
            # 只检查当前函数
            if func_name != nodes[node_id].function_name:
                continue
            # 只检查核心结构
            if nodes[node_id].opcode != "SSTORE":
                continue
            state = nodes[node_id].state
            slot_expr = nodes[node_id].symbol_vars_expr[0]
            value_expr = nodes[node_id].symbol_vars_expr[1]
            slot_start_node_ids,slot_sload_count = Node.find_start_node_ids(nodes, nodes[node_id].predecessors_list[0],ret_sload_count= True)
            value_start_node_ids,value_sload_count = Node.find_start_node_ids(nodes, nodes[node_id].predecessors_list[1],ret_sload_count= True)
            # 打印变量
            # print(f"slot_expr: {slot_expr}")
            # print(f"value_expr: {value_expr}")
            # print(f"slot_start_node_ids: {slot_start_node_ids}, slot_sload_count: {slot_sload_count}")
            # print(f"value_start_node_ids: {value_start_node_ids}, value_sload_count: {value_sload_count}")
            # 检查
            if len(slot_start_node_ids) == 2 \
                and (check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)) \
                and (check_roles(nodes[slot_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[slot_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER)):
                # slot满足条件：二维映射，有两个key来自参数
                # 检查value
                if len(value_start_node_ids) == 3 \
                    and (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)) \
                    and (check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER)) \
                    and (check_roles(nodes[value_start_node_ids[2]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[2]].symbol_vars_expr[0],Role.SENDER)):
                    # value满足条件：三个key来自参数
                    if '115792089237316195423570985008687907853269984665640564039457584007913129639935' in value_expr:
                        # 返回函数类型：ERC1155的burn函数
                        flag_ERC1155_burn_balance = True
                        balance_state = state
                        # return FunctionType.ERC1155_BURN
                    elif check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"):
                        flag_ERC1155_mint_balance = True
                        balance_state = state
                        # return FunctionType.ERC1155_MINT
                if len(value_start_node_ids) == 2 and value_sload_count ==1:
                    if check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"):
                        flag_ERC1155_mint_balance = True
                        balance_state = state
            elif len(slot_start_node_ids) == 2 and slot_sload_count == 3:
                if value_expr == '0':
                    # _holderTokens[owner].remove(tokenId); ERC721 set save tokenId (replace balance)
                    flag_ERC721_burn_balance = True
                    balance_state = state
            elif len(slot_start_node_ids) == 1: # and (check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[slot_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER))
                # slot满足条件：一维映射，key来自参数，
                if slot_sload_count >= 1: #且是嵌套映射
                    # 检查value
                    if len(value_start_node_ids) == 1 \
                        and (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)):
                        if value_sload_count >= 2:
                            if value_sload_count > 2:
                                if value_sload_count >= 3 \
                                    and (
                                    minus_one in value_expr
                                    or check_opcode(nodes,nodes[node_id].predecessors_list[1],"SUB")
                                ): 
                                    # value满足条件：-1 (2^20-1)
                                    flag_ERC721_burn_balance = True  # 结构体BURN
                                    balance_state = state
                                else:
                                    print("#ERROR:value_sload_count > 1")
                            # 嵌套映射
                            if (
                                minus_one in value_expr
                                or check_opcode(nodes,nodes[node_id].predecessors_list[1],"SUB")
                                ):
                                # value满足条件：-1 (2^32-1)
                                flag_ERC721_burn_balance = True 
                                balance_state = state
                            elif check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"):
                                flag_ERC721_mint_balance = True
                                balance_state = state
                    elif len(value_start_node_ids) == 1\
                        and check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM):
                        if value_sload_count == 1: #ERC721 balance[to] +=1
                            flag_ERC721_mint_balance = True
                            balance_state = state
                else: # slot_sload_count == 0
                    if len(value_start_node_ids) == 1 \
                        and (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)):
                        if value_sload_count == 1:
                            # value_expr以逗号分割，最后一位是否位0
                            if ',' in value_expr\
                                and value_expr.split(',')[-1].strip() == '0':
                                flag_ERC721_burn_owner = True
                                owner_state = state
                            else:
                                if check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"):
                                    flag_ERC721_mint_balance = True
                                    balance_state = state
                                if (
                                    minus_one in value_expr
                                    or check_opcode(nodes,nodes[node_id].predecessors_list[1],"SUB")
                                ):
                                    flag_ERC721_burn_balance = True
                                    balance_state = state
                        elif value_sload_count == 2: 
                            if ',' in value_expr\
                                and value_expr.split(',')[-1].strip() == '0':
                                flag_ERC721_burn_owner = True
                                owner_state = state
                            
                    elif len(value_start_node_ids) == 2 \
                        and (
                            (check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER))
                            or ((check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)))
                        ):
                        #and (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER)) \
                        if value_sload_count == 1:
                            flag_ERC721_mint_owner = True
                            owner_state = state
                            if (check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER))\
                                and check_opcode(nodes,nodes[node_id].predecessors_list[1],"ADD"): # TODO：可能导致721误报为1155
                                flag_ERC1155_mint_balance = True
                                balance_state = state
                        elif value_sload_count == 2:
                            flag_ERC721_mint_owner = True # 结构体BURN
                            owner_state = state
            elif len(slot_start_node_ids) == 1:
                if slot_sload_count == 0:
                    if len(value_start_node_ids) == 2 \
                        and (
                            check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) \
                            or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER) \
                            or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) \
                            or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER)
                        ):
                        if value_sload_count == 1:
                            # print("value_expr.split(',')[-1].strip()",value_expr.split(',')[-1].strip())
                            if ',' in value_expr\
                                and check_roles(value_expr.split(',')[-1].strip(),Role.PARAM):
                                flag_ERC721_mint_balance = True # 结构体BURN
                                balance_state = state
                            elif value_sload_count == 2:
                                flag_ERC721_mint_owner = True # BURN的SHA3没有正确查找前驱结点
                                owner_state = state
                elif slot_sload_count == 1:
                    if len(value_start_node_ids) == 2\
                        and (
                            check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM) \
                            or check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.SENDER) \
                            or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.PARAM) \
                            or check_roles(nodes[value_start_node_ids[1]].symbol_vars_expr[0],Role.SENDER)
                        ):
                        if value_sload_count == 2:
                            flag_ERC721_mint_balance = True
                            balance_state = state
        # 正确性检测
        if False and nftmbType in [FunctionType.ERC721_BURN,FunctionType.ERC721_MINT]\
            and (flag_ERC721_mint_owner or flag_ERC721_burn_owner):
            # 需要检查owner正确性
            constraints = copy(owner_state.world_state.constraints)
            constraints += [
                owner_state.environment.sender == ACTORS.attacker,
            ]
            try:
                solver.get_model(constraints)
                # 正确性问题：没有进行权限检查
                print(f"ERROR: {nftmbType} function authorisation correctness, function name:{func_name}")
                description_head = f"{nftmbType} function authorisation correctness"
                description = f"{nftmbType} function authorisation correctness (in [owner]), function name:{func_name}"
                issue = ret_issues(owner_state,description_head=description_head, description_tail=description)
                issues.append(issue) 
            except UnsatError:
                pass
        #  TODO:检查逻辑存在问题，--unconstrained-storage参数导致是符号变量化的storage，无法检查
        if False and (flag_ERC1155_burn_balance or flag_ERC1155_mint_balance or flag_ERC721_burn_balance or flag_ERC721_mint_balance):
            # 需要检查余额state
            constraints = copy(balance_state.world_state.constraints)
            constraints += [
                balance_state.environment.sender == ACTORS.attacker,
            ]
            try:
                solver.get_model(constraints)
                # 正确性问题：没有进行权限检查
                print(f"ERROR: {nftmbType} function authorisation correctness, function name:{func_name}")
                description_head = f"{nftmbType} function authorisation correctness"
                description = f"{nftmbType} function authorisation correctness (in [balance]), function name:{func_name}"
                issue = ret_issues(balance_state,description_head=description_head, description_tail=description)
                issues.append(issue) 
            except UnsatError:
                pass
        # 检查是否没有更新所有者余额(ERC721)
        if (nftmbType == FunctionType.ERC721_BURN and not flag_ERC721_burn_balance) \
            or (nftmbType == FunctionType.ERC721_MINT and not flag_ERC721_mint_balance):
            # 缺少balance
            print(f"ERROR: {nftmbType} function lack of balance , function name:{func_name}")
            description_head = f"{nftmbType} function lack of balance"
            description = f"{nftmbType} function lack of balance, function name:{func_name}"
            issue = ret_issues(state,description_head=description_head, description_tail=description)
            issues.append(issue)
        # 检查是否没有删除代币所有者
        if (nftmbType == FunctionType.ERC721_BURN and not flag_ERC721_burn_owner) \
            or (nftmbType == FunctionType.ERC721_MINT and not flag_ERC721_mint_owner):
            # Clear approvals and delete _owners[tokenId];
            print(f"ERROR: {nftmbType} function lack of owner_delete , function name:{func_name}")
            description_head = f"{nftmbType} function lack of owner_delete"
            description = f"{nftmbType} function lack of owner_delete, function name:{func_name}"
            issue = ret_issues(state,description_head=description_head, description_tail=description)
            issues.append(issue)
        
        # 检查所有权是否存在问题(ERC721)
        if (nftmbType == FunctionType.ERC721_BURN and not flag_ERC721_burn_owner) \
            or (nftmbType == FunctionType.ERC721_MINT and not flag_ERC721_mint_owner):
            # 缺少owner
            print(f"ERROR: {nftmbType} function lack of owner , function name:{func_name}")
            description_head = f"{nftmbType} function lack of owner"
            description = f"{nftmbType} function lack of owner, function name:{func_name}"
            issue = ret_issues(state,description_head=description_head, description_tail=description)
            issues.append(issue)           
            
        return issues                    
                    
                
            
    
    def Transferfromhandler(self,transferfromType:FunctionType,nodes,func_name,identity_dict={}):  #a给b授权v
        if flag_time:
            start_time = time.time()
            print("Transferfromhandler start_time",start_time)
        issues = []
        if len(identity_dict) == 0:
            print("ERROR:ERC transfer or transferfrom identity_dict is empty")
        if transferfromType == FunctionType.ERC20_TRANSFER:
            print("transferfromhandler transferfromType: ",transferfromType)
            # log_hash = None
            for node in nodes:
                if func_name != nodes[node].function_name:
                    continue
                current_node = nodes[node]
                state = current_node.state
                # environment = state.environment
                if nodes[node].opcode == "SSTORE":
                    slot_expr = current_node.symbol_vars_expr[0]
                    value_expr = current_node.symbol_vars_expr[1]
                    if slot_expr == "":
                        print("ERROR:slot_expr is empty")
                    if "block.number" in value_expr:# 忽略value中包含block_number的情况
                        print("WARNING:block.number in value_expr")
                        pass
                    # identity = identity_extract(slot_expr)
                    hardcode_issues = hard_code_check(nodes,current_node)
                    if hardcode_issues != [] :
                        issues.extend(hardcode_issues)
                        return issues
                    start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[0])
                    if len(start_node_ids) == 0:
                        # print("INFO:not mapping sstore")
                        continue
                    value_start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[1])
                    start_nodes = [nodes[start_node_id] for start_node_id in start_node_ids]
                    value_start_nodes = [nodes[value_start_node_id] for value_start_node_id in value_start_node_ids]
                    if flag_detailed:
                        print("node",node,"slot",slot_expr,start_node_ids,"value",value_expr,value_start_node_ids)
                    # 判断slot并判断对应核心语句
                    if len(start_node_ids) == 1:
                        # balances[msg.sender] -= _amount;
                        if check_roles(start_nodes[0].symbol_vars_expr[0],Role.SENDER):
                            # 添加indentity
                            indentity = identity_extract(slot_expr)
                            if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                self.identity_dict[indentity] = IdentityType.ERC20_BALANCE
                            # print("core:",indentity,"slot",slot_expr,start_node_ids,"value",value_expr,value_start_node_ids)
                            
                            # 检查value：balances[msg.sender] - _amount
                            if len(value_start_node_ids) == 2 \
                                and check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.SENDER) \
                                and check_roles(value_start_nodes[1].symbol_vars_expr[0],Role.PARAM2) \
                                    and check_opcode(nodes,current_node.predecessors_list[1],"SUB"):
                                pass
                            else: #value错误
                                description = "ERROR value in mapping:value is not balances[msg.sender] - _amount"
                                issue = ret_issues(state,description_tail=description)
                                issues.append(issue)
                        # balances[_to] += _amount;
                        elif check_roles(start_nodes[0].symbol_vars_expr[0],Role.PARAM1):  
                            # 添加indentity
                            indentity = identity_extract(slot_expr)
                            if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                self.identity_dict[indentity] = IdentityType.ERC20_BALANCE
                            # 检查value：balances[_to] + _amount
                            if len(value_start_node_ids) == 2 \
                                and ((check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.PARAM2) \
                                    and check_roles(value_start_nodes[1].symbol_vars_expr[0],Role.PARAM1) \
                                    and check_opcode(nodes,current_node.predecessors_list[1],"ADD")) \
                                or (check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.PARAM1) \
                                    and check_roles(value_start_nodes[1].symbol_vars_expr[0],Role.PARAM2)) \
                                    and check_opcode(nodes,current_node.predecessors_list[1],"ADD")):
                                pass
                            
                            else: # value错误
                                description = "ERROR value in mapping:value is not balances[_to] + _amount"
                                issue = ret_issues(state,description_tail=description)
                                issues.append(issue)
                        else:
                            # slot ERROR
                            description = "ERROR slot key in mapping:owner is not msg.sender or to"
                            issue = ret_issues(state,description_tail=description)
                            issues.append(issue)
                    else:
                        print("ERROR:unhandled situation transfer start_node_ids or value_start_node_ids error")
                        print("start_node_ids: ",start_node_ids)
                        print("value_start_node_ids: ",value_start_node_ids)
            ## 判断identity_dict的key个数
            balances_count = 0
            for key in self.identity_dict:
                if self.identity_dict[key] == IdentityType.ERC20_BALANCE:
                    balances_count += 1
            if balances_count > 1:
                description_head = "identity_dict ERROR"
                description = "ERROR:ERC20_TRANSFER balance_count > 1"
                issue = ret_issues(state,description_head=description_head,description_tail=description)
                issues.append(issue)
            return issues
        elif transferfromType == FunctionType.ERC20_TRANSFERFROM:
            if flag_detailed:
                print("transferfromhandler transferfromType: ",transferfromType)
            for node in nodes:
                if func_name != nodes[node].function_name:
                    continue
                current_node = nodes[node]
                state = current_node.state
                if nodes[node].opcode == "SSTORE":
                    slot_expr = current_node.symbol_vars_expr[0]
                    value_expr = current_node.symbol_vars_expr[1]
                    if slot_expr == "":
                        print("ERROR:slot_expr is empty")
                    if "block.number" in value_expr:# 忽略value中包含block_number的情况
                        print("WARNING:block.number in value_expr")
                        pass
                    # identity = identity_extract(slot_expr)
                    # 避免approve(address(0)误报
                    if not re.search(r"keccak256_512\(Extract\(ff,8,\d+\+Storage0\[keccak256_512\(1_calldata\[16:35\],\d+\)\]\),ff\+Extract\(7,0,Storage0\[keccak256_512\(1_calldata\[16:35\],\d+\)\]\),keccak256_512\(1_calldata\[16:35\],\d+\)\)",value_expr)\
                        and not not re.search(r"Extract\(ff,160,Storage0\[keccak256_512\(1_calldata\[68:99\],\d+\)\]\),0",value_expr):
                        hardcode_issues = hard_code_check(nodes,current_node)
                        if hardcode_issues != [] :
                            issues.extend(hardcode_issues)
                            return issues
                        continue
                    start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[0])
                    if len(start_node_ids) == 0:
                        # print("INFO:not mapping sstore")
                        continue
                    value_start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[1])
                    start_nodes = [nodes[start_node_id] for start_node_id in start_node_ids]
                    value_start_nodes = [nodes[value_start_node_id] for value_start_node_id in value_start_node_ids]
                    if flag_detailed:
                        print("node",node,"slot",slot_expr,start_node_ids,"value",value_expr,value_start_node_ids)
                    # 判断slot并判断对应核心语句
                    if len(start_node_ids) == 2:# allowed[_from][msg.sender] -= _amount; 
                        if check_roles(start_nodes[0].symbol_vars_expr[0],Role.SENDER)\
                            and check_roles(start_nodes[1].symbol_vars_expr[0],Role.PARAM1):
                            # 添加indentity
                            indentity = identity_extract(slot_expr)
                            if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                self.identity_dict[indentity] = IdentityType.ERC20_ALLOWANCE
                            # print("core:",indentity,"slot",slot_expr,start_node_ids,"value",value_expr,value_start_node_ids)
                            
                            # 检查value：allowed[_from][msg.sender] - _amount  
                            if len(value_start_node_ids) == 3\
                                and check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.SENDER) \
                                and check_roles(value_start_nodes[1].symbol_vars_expr[0],Role.PARAM1) \
                                and check_roles(value_start_nodes[2].symbol_vars_expr[0],Role.PARAM3) \
                                and (
                                    minus_one in value_expr
                                    or check_opcode(nodes,current_node.predecessors_list[1],"SUB")
                                ):
                                pass
                            else:  # value错误
                                description = "ERROR value in mapping:value is not allowed[_from][msg.sender] - _amount"
                                issue = ret_issues(state,description_tail=description)
                                issues.append(issue)
                        else:
                            # slot ERROR
                            description = "ERROR slot key in mapping:owner is not _from or msg.sender"
                            issue = ret_issues(state,description_tail=description)
                            issues.append(issue)
                    elif len(start_node_ids) == 1:
                        # balances[_from] -= _amount; balances[_to] += _amount;  
                        if (
                            minus_one in value_expr
                            or check_opcode(nodes,current_node.predecessors_list[1],"SUB") 
                        ):# balances[_from] -= _amount;
                            # 检查slot
                            if check_roles(start_nodes[0].symbol_vars_expr[0],Role.PARAM1):
                                # 添加indentity
                                indentity = identity_extract(slot_expr)
                                if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                    self.identity_dict[indentity] = IdentityType.ERC20_BALANCE
                                # 检查value：balances[_from] - _amount
                                if len(value_start_node_ids) == 2 \
                                    and check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.PARAM1) \
                                    and check_roles(value_start_nodes[1].symbol_vars_expr[0],Role.PARAM3): # \
                                    # and (
                                    #     minus_one in value_expr
                                    #     or check_opcode(nodes,current_node.predecessors_list[1],"SUB")
                                    # )
                                    pass
                                else:
                                    description = "ERROR value in mapping:value is not balances[_from] - _amount"
                                    issue = ret_issues(state,description_tail=description)
                                    issues.append(issue)
                            else: 
                                description = "ERROR slot key in mapping:owner is not _from"
                                issue = ret_issues(state,description_tail=description)
                                issues.append(issue)    
                        else:# balances[_to] += _amount
                            if check_roles(start_nodes[0].symbol_vars_expr[0],Role.PARAM2):
                                # 添加indentity
                                indentity = identity_extract(slot_expr)
                                if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                    self.identity_dict[indentity] = IdentityType.ERC20_BALANCE
                                # 检查value：balances[_to] + _amount
                                if len(value_start_node_ids) == 2 \
                                    and ((check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.PARAM2) \
                                        and check_roles(value_start_nodes[1].symbol_vars_expr[0],Role.PARAM3) \
                                        and check_opcode(nodes,current_node.predecessors_list[1],"ADD"))\
                                    or (check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.PARAM3) \
                                        and check_roles(value_start_nodes[1].symbol_vars_expr[0],Role.PARAM2) \
                                        and check_opcode(nodes,current_node.predecessors_list[1],"ADD"))):
                                    pass
                                else:
                                    description = "ERROR value in mapping:value is not balances[_to] + _amount"
                                    issue = ret_issues(state,description_tail=description)
                                    issues.append(issue)
                            else:
                                description = "ERROR slot key in mapping:owner is not _to"
                                issue = ret_issues(state,description_tail=description)
                                issues.append(issue)
                    else:
                        print("ERROR:unhandled situation transferfrom start_node_ids or value_start_node_ids error")
                        print("node",node,"slot",slot_expr,start_node_ids,"value",value_expr,value_start_node_ids)
                        pass
            ## 判断identity_dict的key个数
            allowances_count = 0
            balances_count = 0
            for key in self.identity_dict:
                if self.identity_dict[key] == IdentityType.ERC20_ALLOWANCE:
                    allowances_count += 1
                elif self.identity_dict[key] == IdentityType.ERC20_BALANCE:
                    balances_count += 1
            if allowances_count > 1:
                description_head = "identity_dict ERROR"
                description = "ERROR:ERC20_TRANSFERFROM allowances_count > 1"
                issue = ret_issues(state,description_head=description_head,description_tail=description)
            elif balances_count > 1:
                print("ERROR:ERC20_TRANSFERFROM balances_count > 1")
                description_head = "identity_dict ERROR"
                description = "ERROR:ERC20_TRANSFERFROM balances_count > 1"
                issue = ret_issues(state,description_head=description_head,description_tail=description)
                issues.append(issue)             
        elif transferfromType == FunctionType.ERC721_TRANSFERFROM:
            if flag_detailed:
                print("transferfromhandler transferfromType: ",transferfromType)
            for node in nodes:
                if func_name != nodes[node].function_name:
                    continue
                current_node = nodes[node]
                state = current_node.state
                if nodes[node].opcode == "SSTORE":
                    slot_expr = current_node.symbol_vars_expr[0]
                    value_expr = current_node.symbol_vars_expr[1]
                    if slot_expr == "":
                        print("ERROR:slot_expr is empty")
                    if "block.number" in value_expr:# 忽略value中包含block_number的情况
                        print("WARNING:block.number in value_expr")
                        pass
                    # identity = identity_extract(slot_expr)
                    # 避免approve(address(0)误报
                    if not re.search(r"keccak256_512\(Extract\(ff,8,\d+\+Storage0\[keccak256_512\(1_calldata\[16:35\],\d+\)\]\),ff\+Extract\(7,0,Storage0\[keccak256_512\(1_calldata\[16:35\],\d+\)\]\),keccak256_512\(1_calldata\[16:35\],\d+\)\)",value_expr)\
                        and not re.search(r"Extract\(ff,160,Storage0\[keccak256_512\(1_calldata\[68:99\],\d+\)\]\),0",value_expr)\
                        and not (
                            re.search(r"keccak256_512\(Extract\(ff,8,\d+\+Storage0\[keccak256_512\(1_calldata\[16:35\],\d+\)\]\),ff\+Extract\(7,0,Storage0\[keccak256_512\(1_calldata\[16:35\],\d+\)\]\),keccak256_512\(1_calldata\[16:35\],\d+\)\)",slot_expr) \
                            and  value_expr == "0"
                        ):
                        hardcode_issues = hard_code_check(nodes,current_node)
                        if hardcode_issues != [] :
                            issues.extend(hardcode_issues)
                            return issues
                        continue
                    start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[0])
                    if len(start_node_ids) == 0:
                        # print("INFO:not mapping sstore")
                        continue
                    value_start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[1])
                    start_nodes = [nodes[start_node_id] for start_node_id in start_node_ids]
                    value_start_nodes = [nodes[value_start_node_id] for value_start_node_id in value_start_node_ids]
                    if flag_detailed:
                        print("node",node,"slot",slot_expr,start_node_ids,"value",value_expr,value_start_node_ids)
                    # 判断slot并判断对应核心语句
                    if len(start_node_ids) == 1:
                        #  _tokenOwners[tokenId] = to;
                        if check_roles(start_nodes[0].symbol_vars_expr[0],Role.PARAM3):
                            # 添加indentity
                            indentity = identity_extract(slot_expr)
                            if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                self.identity_dict[indentity] = IdentityType.ERC721_OWNER
                            # 检查value：_tokenOwners[tokenId] = to;
                            if (len(value_start_nodes) == 2 \
                                    and check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.PARAM2) \
                                    and check_roles(value_start_nodes[1].symbol_vars_expr[0],Role.PARAM3))\
                                or (len(value_start_nodes) == 1 \
                                    and check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.PARAM2)):
                                pass
                            # 或者是_approve(address(0), tokenId);，即value_expr以Extract(开头，以),0结束
                            elif (
                                value_expr.startswith("Extract(") and value_expr.endswith("),0")                                
                            ):
                                pass
                            elif (
                                value_expr== "0" #_approve(address(0), tokenId);
                            ):
                                pass
                            else:
                                description = "ERROR value in mapping:value is not to"
                                issue = ret_issues(state,description_tail=description)
                                issues.append(issue)
                        #  _balances[from] -= 1; #from来自于参数1或_ownerOf(tokenId);
                        elif (check_roles(start_nodes[0].symbol_vars_expr[0],Role.PARAM1) \
                            or check_roles(start_nodes[0].symbol_vars_expr[0],Role.PARAM2)) \
                            and (
                                minus_one in value_expr
                                or check_opcode(nodes,current_node.predecessors_list[1],"SUB")
                            ):
                            # 添加indentity
                            indentity = identity_extract(slot_expr)
                            if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                self.identity_dict[indentity] = IdentityType.ERC721_BALANCE
                            # 检查value：_balances[from] - 1;
                            if len(value_start_node_ids) == 1\
                                and check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.PARAM1):
                                pass
                            else: #value错误
                                description = "ERROR value in mapping:value is not _balances[from] - 1"
                                issue = ret_issues(state,description_tail=description)
                                issues.append(issue)
                        #  _balances[to] += 1;
                        elif check_roles(start_nodes[0].symbol_vars_expr[0],Role.PARAM2):
                            # 添加indentity
                            indentity = identity_extract(slot_expr)
                            if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                self.identity_dict[indentity] = IdentityType.ERC721_BALANCE
                            # 检查value：_balances[to] + 1;
                            if len(value_start_node_ids) == 1 \
                                and check_roles(value_start_nodes[0].symbol_vars_expr[0],Role.PARAM2)\
                                and check_opcode(nodes,current_node.predecessors_list[1],"ADD"):
                                pass
                            else:
                                description = "ERROR value in mapping:value is not _balances[to] + 1"
                                issue = ret_issues(state,description_tail=description)
                                issues.append(issue)
                        else: # slot ERROR
                            description = "ERROR slot key in mapping:key is not to or from"
                            issue = ret_issues(state,description_tail=description)
                            issues.append(issue)     
                    else: #不关心的其他结构
                        print("ERROR:unhandled situation transferfrom start_node_ids or value_start_node_ids error")
                        print("node",node,"slot",slot_expr,start_node_ids,"value",value_expr,value_start_node_ids)
                        pass
            ## 判断identity_dict的key个数
            tokenOwners_count = 0
            balances_count = 0
            for key in self.identity_dict:
                if self.identity_dict[key] == IdentityType.ERC721_OWNER:
                    tokenOwners_count += 1
                elif self.identity_dict[key] == IdentityType.ERC721_BALANCE:
                    balances_count += 1
            if tokenOwners_count > 1:
                description_head = "identity_dict ERROR"
                description = "ERROR:ERC721_TRANSFERFROM tokenOwners_count > 1"
                issue = ret_issues(state,description_head=description_head,description_tail=description)
                issues.append(issue)
            elif balances_count > 1:
                description_head = "identity_dict ERROR"
                description = "ERROR:ERC721_TRANSFERFROM balances_count > 1"
                issue = ret_issues(state,description_head=description_head,description_tail=description)
                issues.append(issue)                
        
        if flag_time:
            end_time = time.time()
            duration = end_time-start_time
            if duration>1:
                print("time!!!:")
            print("Transferfromhandler",end_time-start_time,"end_time",end_time)
        return issues

    def Approvehandler(self,approveType:FunctionType,nodes,func_name,identity_dict={}):  #a给b授权v
        # 记录开始时间
        if flag_time:
            start_time = time.time()
            print("Approvehandler start_time",start_time)
        issues = []
        if len(identity_dict) == 0:
            print("ERROR:ERC aprrove identity_dict is empty")
        
        if approveType == FunctionType.ERC20_APPROVE or approveType == FunctionType.ERC20_PERMIT: 
            #approve:allowances[owner][spender] = value,owner为msg.sender
            #permit:allowances[owner][spender] = value,owner为参数1
            if flag_detailed:
                print("Approvehandler approveType: ",approveType)
            log_hash = None
            for node in nodes:
                if func_name != nodes[node].function_name:
                    continue
                current_node = nodes[node]
                state = current_node.state
                environment = state.environment                
                # if nodes[node].function_name != environment.active_function_name:
                #     continue
                if nodes[node].opcode == "SSTORE":
                    # print("current_node.uid: ",current_node.uid)
                    slot_expr = current_node.symbol_vars_expr[0]
                    value_expr = current_node.symbol_vars_expr[1]
                    
                    # identity = identity_extract(slot_expr)
                    hardcode_issues = hard_code_check(nodes,current_node)
                    if hardcode_issues != [] : #该语句存在硬编码
                        issues.extend(hardcode_issues)
                        return issues
                    start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[0])
                    if len(start_node_ids) == 0:
                        # print("INFO:not mapping sstore")
                        continue
                    value_start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[1])
                    # if value_start_node_ids == [] and value_expr == "0":
                    #     value_start_node_ids.append(0)
                    # print("start_node_ids: ",start_node_ids)
                    # print("value_start_node_ids: ",value_start_node_ids)                    
                    
                    if len(start_node_ids) >= 2: 
                        slot_start_nodes = [nodes[start_node_ids[0]],nodes[start_node_ids[1]]]
                        
                        #检查hardcode
                        #key1 owner->msg.sender (key1的1是从expr右往左的序号)
                        if approveType == FunctionType.ERC20_APPROVE:
                            flag_1 = check_roles(slot_start_nodes[1].symbol_vars_expr[0],Role.SENDER)
                        else:#permit
                            flag_1 = check_roles(slot_start_nodes[1].symbol_vars_expr[0],Role.PARAM1)
                        # print("OK ERC20")
                        if approveType == FunctionType.ERC20_APPROVE:
                            #key2 spender 来自参数1 address _spender
                            flag_2 = check_roles(slot_start_nodes[0].symbol_vars_expr[0],Role.PARAM1)
                        else:#permit
                            flag_2 = check_roles(slot_start_nodes[0].symbol_vars_expr[0],Role.PARAM2)
                        # 判断slot
                        if flag_1 and flag_2:
                            # print("OK ERC20 slot")
                            ## 添加到identity_dict中  
                            indentity = identity_extract(slot_expr)    
                            if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                self.identity_dict[indentity] = IdentityType.ERC20_ALLOWANCE
                        else:
                            # description = "ERC20 approve ERROR slot key in mapping:\n"
                            description = f"{approveType} ERROR slot key in mapping:\n"
                            
                            if not flag_1:
                                if approveType == FunctionType.ERC20_APPROVE:
                                    print("#ERROR key1 in mapping:owner is not msg.sender",slot_start_nodes[1].symbol_vars_expr[0])
                                    description += "ERROR key1 in mapping:owner is not msg.sender\n"
                                else:
                                    print("#ERROR key1 in mapping:owner is not parameter 1",slot_start_nodes[1].symbol_vars_expr[0])
                                    description += "ERROR key1 in mapping:owner is not parameter 1\n"
                            if not flag_2:
                                if approveType == FunctionType.ERC20_APPROVE:
                                    print("#ERROR key2 in mapping:spender is not msg.sender",slot_start_nodes[0].symbol_vars_expr[0])
                                    description += "ERROR key2 in mapping:spender is not msg.sender\n"
                                else:
                                    print("#ERROR key2 in mapping:spender is not parameter 2",slot_start_nodes[0].symbol_vars_expr[0])
                                    description += "ERROR key2 in mapping:spender is not parameter 2\n"
                            issue = ret_issues(state,description_tail=description)
                            issues.append(issue)
                        # 判断value
                        # value_start_node = nodes[value_start_node_ids[0]]
                        if approveType == FunctionType.ERC20_APPROVE and len(value_start_node_ids) == 1 and check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM2):
                            pass
                        elif approveType == FunctionType.ERC20_PERMIT and len(value_start_node_ids) == 1 and check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM3):
                            pass
                        elif len(value_start_node_ids) == 1 and value_expr == "0":
                            pass #示例：0x2f09be58c1f5792171d9c5165afe210c011b88ac：ERC20函数，条件不符合设置allowance=0，允许
                        else:
                            if approveType == FunctionType.ERC20_APPROVE:
                                description = f"ERROR {approveType} value in mapping:value is not parameter 2"
                                issue = ret_issues(state,description_tail=description)                     
                                issues.append(issue)
                            else:
                                description = f"ERROR {approveType} value in mapping:value is not parameter 3"
                                issue = ret_issues(state,description_tail=description)                     
                                issues.append(issue)
                       
                    else:
                        print("ERROR:unhandled situation 1")
                # elif nodes[node].opcode.startswith("LOG"):
                #     #emit Approval(msg.sender, _spender,_amount);
                #     if flag_detailed:
                #         print("current_node.uid: ",current_node.uid,"LOG check")
                #     #先默认只有一个emit Approval(msg.sender, _spender,_amount);语句
                #     description = ""
                #     if log_hash == None:
                #         log_hash = current_node.log_hash
                #         #owner check
                #         # if not check_roles(current_node.symbol_vars_expr[0],Role.SENDER)
                #         # to
                #         if flag_detailed:
                #             print("log event log_hash",current_node.log_hash)
                #     # elif log_hash == current_node.log_hash:
                #     #     print(current_node.uid,"LOG duplicate")
                #         # pass
                #     else:
                #         print(current_node.uid,"LOG another duplicate:",current_node.log_hash)
                #     log_param1 = nodes[Node.find_start_node_ids(nodes, current_node.predecessors_list[0])[0]].symbol_vars_expr[0]
                #     log_param2 = nodes[Node.find_start_node_ids(nodes, current_node.predecessors_list[1])[0]].symbol_vars_expr[0]
                #     # log_param3 = nodes[Node.find_start_node_ids(nodes, current_node.predecessors_list[2])[0]].symbol_vars_expr[0]
                    
                #     if flag_detailed:
                #         print("log_param1: ",log_param1)
                #         print("log_param2: ",log_param2)
                #     if not check_roles(log_param1,Role.SENDER):
                #         print("#log ERROR:log_param1 is not msg.sender")
                #         description = "log ERROR:log_param1 is not msg.sender,"
                #     elif not check_roles(log_param2,Role.PARAM1):
                #         print("#log ERROR:spender is not parameter 1")
                #         description = "log ERROR:spender is not parameter 1,"
                        
                #     # elif not check_roles(log_param3,Role.PARAM2):
                #     #     print("#log ERROR:_amount is not parameter 2")
                #     #     description = "log ERROR:_amount is not parameter 2,"
                #     #     # severity = "high"
                #     else:
                #         pass
                #     if description:
                #         issue = ret_issues(state,description_tail=description)
                #         issues.append(issue)
                #         # return issues
                    
                #     pass
                else:
                    # print("node.opcode: ",nodes[node].opcode)
                    pass
            # 判断是否重复，即遍历nodes中所有的SSTORE结点，如果有相同的start_node_ids和identity，则说明重复
            # 如果self.identity_dict中IdentityType.ERC20_ALLOWANCE数目大于1
            allowance_count = 0
            for key in self.identity_dict:
                if self.identity_dict[key] == IdentityType.ERC20_ALLOWANCE:
                    allowance_count += 1
            if allowance_count > 1:
                print("#ERROR:suspected duplicate identity structure")
                description = "ERROR:suspected duplicate identity structure"
                issue = ret_issues(state,description_tail=description)
                issues.append(issue)
            return issues
        elif approveType==FunctionType.ERC721_APPROVE: # _tokenApprovals[tokenId] = to;
            if flag_detailed:
                print("Approvehandler approveType: ",approveType)
            
            log_hash = None
            for node in nodes: #处理所有SSTORE和LOG操作码
                if func_name != nodes[node].function_name:
                    continue
                current_node = nodes[node]
                state = current_node.state
                environment = state.environment
                # if nodes[node].function_name != environment.active_function_name:
                #     continue
                if nodes[node].opcode == "SSTORE":
                    if flag_detailed:
                        print("current_node.uid: ",current_node.uid)
                    slot_expr = current_node.symbol_vars_expr[0]
                    value_expr = current_node.symbol_vars_expr[1]
                    if slot_expr == "":
                        print("slot_expr is empty")
                        continue
                    identity = identity_extract(slot_expr)
                    hardcode_issues = hard_code_check(nodes,current_node)
                    if hardcode_issues != [] : #该语句存在硬编码
                        issues.extend(hardcode_issues)
                        return issues
                    # procceced_slot = PreProcExpr(str(slot))
                    # procceced_value = PreProcExpr(str(value))
                    start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[0])
                    if len(start_node_ids) == 0:
                        # print("INFO:not mapping sstore")
                        continue
                    value_start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[1])
                    # print("start_node_ids: ",start_node_ids)
                    if flag_detailed:
                        print("value_start_node_ids: ",value_start_node_ids)
                    slot_start_node = nodes[start_node_ids[0]]
                    # if len(value_start_node_ids) == 2 and '+' not in value_expr and '-' not in value_expr: #只有赋值，没有其他操作(ERC721的value符号变量会包含tokenId的切片，原因未知)

                    # 检测slot:判断slot_expr是否来自参数2 uint256 tokenId
                    if slot_start_node.opcode == "CALLDATALOAD" and check_roles(slot_start_node.symbol_vars_expr[0],Role.PARAM2): #slot正确
                        # print("OK ERC721 slot")
                        # slot正确，则添加对应indentity
                        indentity = identity_extract(slot_expr)
                        if identity not in self.identity_dict:
                            self.identity_dict[identity] = IdentityType.ERC721_TOKENAPPROVAL
                    else:
                        # slot key不是参数2
                        print("#ERROR key in mapping:tokenId is not parameter 2")
                        description = "ERROR key in mapping:tokenId is not parameter 2"
                        issue = ret_issues(state,description_tail=description)               
                        issues.append(issue)
                        return issues

                    # 检查value:判断value_expr是否为{}_calldata[4:35],{}为数字
                    if len(value_start_node_ids) >0 and check_roles(nodes[value_start_node_ids[0]].symbol_vars_expr[0],Role.PARAM1):
                        pass
                    # match = re.match(r"\d+_calldata\[4:35\]", value_start_node.symbol_vars_expr[0])
                    # if check_roles(value_start_node.symbol_vars_expr[0],Role.PARAM1): #value正确
                    #     pass
                    else:
                        print("#ERROR value in mapping:to is not parameter 1")
                        #value 不是 参数1 to
                        description = "ERROR value in mapping:to is not parameter 1"
                        issue = ret_issues(state,description_tail=description)
                        issues.append(issue)
                        return issues
                    
                    #检查identity是否重复
                    # if len(identity_dict) == 0:
                    #     print("ERROR:ERC721 aprrove identity_dict is empty")
                    # else:
                    #     dict_keys = list(identity_dict.keys())
                    #     for key in dict_keys:
                    #         if key not in self.identity_dict:
                    #             self.identity_dict[key] = IdentityType.ERC721_TOKENAPPROVAL
        
                    
                        
                # elif nodes[node].opcode.startswith("LOG"):
                #     # emit Approval(owner, to, tokenId);
                #     if flag_detailed:
                #         print("current_node.uid: ",current_node.uid,"LOG check")
                #     #先默认只有一个emit Approval(owner, to, tokenId);语句
                #     description = ""
                    # if log_hash == None:
                    #     if flag_detailed:
                    #         print("current_node.opcode: ",current_node.opcode)
                    #     log_hash = current_node.log_hash
                    #     #owner check
                    #     # if not check_roles(current_node.symbol_vars_expr[0],Role.SENDER)
                    #     # to
                    #     log_param1 = nodes[Node.find_start_node_ids(nodes, current_node.predecessors_list[0])[0]].symbol_vars_expr[0]
                    #     log_param2 = nodes[Node.find_start_node_ids(nodes, current_node.predecessors_list[1])[0]].symbol_vars_expr[0]
                    #     log_param3 = nodes[Node.find_start_node_ids(nodes, current_node.predecessors_list[2])[0]].symbol_vars_expr[0]
                    #     # print("log_param1: ",log_param1)
                    #     if not check_roles(log_param1,Role.PARAM2):
                    #         print("#log ERROR:(Approval(owner, to, tokenId)) owner is not parameter 2:",log_param1)
                    #         description = "log ERROR:(Approval(owner, to, tokenId)) owner is not parameter 2,"
                    #     elif not check_roles(log_param2,Role.PARAM1):
                    #         print("#log ERROR:(Approval(owner, to, tokenId)) to is not parameter 1:",log_param2)
                    #         description = "log ERROR:(Approval(owner, to, tokenId)) to is not parameter 1,"
                            
                    #     elif not check_roles(log_param3,Role.PARAM2):
                    #         print("#log ERROR:tokenId is not parameter 2:",log_param3)
                    #         description = "log ERROR:tokenId is not parameter 2,"
                    #         # severity = "high"
                    #     else:
                    #         pass
                    #     if description:
                    #         issue = ret_issues(state,description_tail=description)
                    #         issues.append(issue)
                    #         # return issues
                    # # elif log_hash == current_node.log_hash:
                    # #     print(current_node.uid,"LOG duplicate")
                    # #     pass
                    # else:
                    #     print(current_node.uid,"LOG another duplicate")
                    # print("ERC721 unhandled approve LOG situation")
            # 如果self.identity_dict中IdentityType.ERC721_TOKENAPPROVAL数目大于1
            tokenapproval_count = 0
            for key in self.identity_dict:
                if self.identity_dict[key] == IdentityType.ERC721_TOKENAPPROVAL:
                    tokenapproval_count += 1
            if tokenapproval_count > 1:
                print("#ERROR:suspected duplicate identity structure")
                description = "ERROR:suspected duplicate identity structure"
                issue = ret_issues(state,description_tail=description)
                issues.append(issue)
                return issues
        elif approveType==FunctionType.ERC721_SETAPPROVALFORALL: #_operatorApprovals[msg.sender][operator] = approved;
            if flag_detailed:
                print("Approvehandler approveType: ",approveType)
            log_hash = None
            for node in nodes:
                if func_name != nodes[node].function_name:
                    continue
                current_node = nodes[node]
                state = current_node.state
                # environment = state.environment
                if nodes[node].opcode == "SSTORE":
                    # print("current_node.uid: ",current_node.uid)
                    slot_expr = current_node.symbol_vars_expr[0]
                    value_expr = current_node.symbol_vars_expr[1]
                    if slot_expr == "":
                        print("ERROR:slot_expr is empty")
                        continue
                    identity = identity_extract(slot_expr)
                    hardcode_issues = hard_code_check(nodes,current_node)
                    if hardcode_issues != [] : #该语句存在硬编码
                        issues.extend(hardcode_issues)
                        return issues
                    start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[0])
                    if len(start_node_ids) == 0:
                        # print("INFO:not mapping sstore")
                        continue
                    value_start_node_ids = Node.find_start_node_ids(nodes, current_node.predecessors_list[1])
                    # print("start_node_ids: ",start_node_ids)
                    # print("value_start_node_ids: ",value_start_node_ids)
                    if len(start_node_ids)<2 :
                        print("ERROR:unhandled situation 3:setApprovalForAll:",func_name)
                        continue
                    # slot_start_nodes = [nodes[start_node_ids[0]],nodes[start_node_ids[1]]]
                    try:
                        slot_start_nodes = [nodes[start_node_ids[0]],nodes[start_node_ids[1]]]
                        value_start_node = nodes[value_start_node_ids[0]]
                    except:
                        print("#ERROR:setApprovalForAll value_start_node empty",func_name)
                        continue
                    if "If" in value_expr:
                        # 检查hard_code
                        # key1 msg.sender
                        flag_1 = check_roles(slot_start_nodes[1].symbol_vars_expr[0],Role.SENDER)
                        # key2 operator -> parameter 1
                        flag_2 = check_roles(slot_start_nodes[0].symbol_vars_expr[0],Role.PARAM1)
                        if flag_1 and flag_2:
                            # print("OK ERC721 setApproveForAll slot")
                            indentity = identity_extract(slot_expr)
                            if indentity not in self.identity_dict or self.identity_dict[indentity] == IdentityType.UNKNOWN:
                                self.identity_dict[indentity] = IdentityType.ERC721_OPERATORAPPROVAL  
                        else:
                            description = "ERC721 setApproveForAll ERROR slot key in mapping:\n"
                            if not flag_1:
                                print("#ERROR key1 in mapping:key1 is not msg.sender",slot_start_nodes[1].symbol_vars_expr[0],start_node_ids[1])
                                description += "ERROR key1 in mapping:key1 is not msg.sender\n"
                            if not flag_2:
                                print("#ERROR key2 in mapping:operator is not parameter 1",slot_start_nodes[0].symbol_vars_expr[0],start_node_ids[0])
                                description += "ERROR key2 in mapping:operator is not parameter 1\n"
                            issue = ret_issues(state,description_tail=description)
                            issues.append(issue)  
                        # value
                        if check_roles(value_start_node.symbol_vars_expr[0],Role.PARAM2):
                            # and "If" in value_expr:
                            pass
                        else:
                            description = "ERROR value in mapping:value is not parameter 2"
                            issue = ret_issues(state,description_tail=description)
                            issues.append(issue)
                    else:
                        print("ERROR:unhandled situation 3:setApprovalForAll")
            ## 判断identity_dict的key个数                        
            # 如果self.identity_dict中IdentityType.ERC721_OPERATORAPPROVAL数目大于1
            operatorapproval_count = 0
            for key in self.identity_dict:
                if self.identity_dict[key] == IdentityType.ERC721_OPERATORAPPROVAL:
                    operatorapproval_count += 1
            if operatorapproval_count > 1: 
                print("#ERROR:suspected duplicate identity structure")
                description_head = "identity_dict ERROR"
                description = "ERROR:suspected duplicate identity structure"
                issue = ret_issues(state,description_head=description_head,description_tail=description)
                issues.append(issue)
            if flag_detailed:
                print("Approvehandler approveType: ",approveType,",issues",issues)         
            return issues
        
        if flag_time:
            end_time = time.time()
            duration = end_time-start_time
            if duration>1:
                print("time!!!:")
            print("Approvehandler",end_time-start_time,"end_time",end_time)                          
        return issues



        

detector = DefiCheck3()




# ---------- Custom Error Listener ----------

class DuduDSLErrorListener(ConsoleErrorListener):
    """
    Custom error listener to collect and report lexer/parser errors.
    Overrides syntaxError to print detailed messages and track errors.
    """
    def __init__(self):
        super().__init__()
        self.errors = []

    def syntaxError(self, recognizer: Recognizer, offendingSymbol, line: int, column: int, msg: str, e: RecognitionException):
        """
        Called when a syntax error is encountered.
        Stores the error detail and also prints to stderr.
        """
        error_message = f"Syntax error at line {line}, column {column}: {msg}"
        self.errors.append((line, column, msg))
        sys.stderr.write(error_message + "\n")


# ---------- AST Node Definitions ----------

class ASTNode:
    """
    Base class for all AST nodes.
    Provides a method to pretty-print or traverse if needed.
    """
    def __init__(self):
        pass

    def __repr__(self):
        return self.__class__.__name__ + "()"


class ProgramNode(ASTNode):
    """
    Represents the root of the AST corresponding to 'program' rule.
    Contains a list of declarations and statements.
    """
    def __init__(self, children):
        super().__init__()
        self.children = children  # list of ASTNode

    def __repr__(self):
        return f"ProgramNode(children={self.children})"


class DeclNode(ASTNode):
    """
    Represents a function or variable declaration.
    Stores identifier name, parameter list (expressions), and either
    an expression (for '= Expr;') or a block (list of statements).
    """
    def __init__(self, name, params, expr=None, block=None):
        super().__init__()
        self.name = name            # string
        self.params = params        # list of ExprNode
        self.expr = expr            # ExprNode or None
        self.block = block          # list of ASTNode or None

    def __repr__(self):
        return f"DeclNode(name={self.name}, params={self.params}, expr={self.expr}, block={self.block})"


class LetNode(ASTNode):
    """
    Represents a 'let Identifier = Expr;' statement.
    """
    def __init__(self, name, expr):
        super().__init__()
        self.name = name   # string
        self.expr = expr   # ExprNode

    def __repr__(self):
        return f"LetNode(name={self.name}, expr={self.expr})"


class IfNode(ASTNode):
    """
    Represents an 'if(Expr) Block [else Block]' statement.
    """
    def __init__(self, cond, then_block, else_block=None):
        super().__init__()
        self.cond = cond                        # ExprNode
        self.then_block = then_block            # list of ASTNode
        self.else_block = else_block or []      # list of ASTNode

    def __repr__(self):
        return f"IfNode(cond={self.cond}, then={self.then_block}, else={self.else_block})"


class ForNode(ASTNode):
    """
    Represents a 'for(Expr; Expr; Expr) Block' statement.
    """
    def __init__(self, init_expr, cond_expr, post_expr, body):
        super().__init__()
        self.init_expr = init_expr    # ExprNode
        self.cond_expr = cond_expr    # ExprNode
        self.post_expr = post_expr    # ExprNode
        self.body = body              # list of ASTNode

    def __repr__(self):
        return f"ForNode(init={self.init_expr}, cond={self.cond_expr}, post={self.post_expr}, body={self.body})"


class ExprStmtNode(ASTNode):
    """
    Represents a bare expression used as a statement: 'Expr;'.
    """
    def __init__(self, expr):
        super().__init__()
        self.expr = expr   # ExprNode

    def __repr__(self):
        return f"ExprStmtNode(expr={self.expr})"


# ... Define other ASTNode subclasses as needed for expressions, transfers, etc. ...
# For brevity, only a core subset is shown. In a complete implementation, one
# would define nodes for Transfer, EthTransfer, Approve, Custom, etc., as well as
# expression node types (BinaryOpNode, LiteralNode, IdentifierNode, etc.)


# ---------- Example Listener ----------

class MyDuduDSLListener(duduDSLListener):
    """
    Example Listener that traverses the parse tree and prints events.
    """
    def enterProgram(self, ctx):
        print("[Listener] Entering program")

    def exitProgram(self, ctx):
        print("[Listener] Exiting program")

    def enterLetStmt(self, ctx):
        # ctx.Identifier().getText() gives the variable name
        var_name = ctx.Identifier().getText()
        print(f"[Listener] Let statement, variable = {var_name}")

    def enterIfStmt(self, ctx):
        # ctx.expr() returns the expression context for the condition
        cond_text = ctx.expr().getText()
        print(f"[Listener] Found if-statement with condition: {cond_text}")

    def enterForStmt(self, ctx):
        print("[Listener] Found for-statement")

    # Add more override methods for other rules as needed


# ---------- Example Visitor (for AST Construction) ----------

class ASTBuilderVisitor(duduDSLVisitor):
    """
    Example Visitor that builds a simple AST from the parse tree.
    For each relevant parse rule, override its visitXXX method.
    """
    def visitProgram(self, ctx):
        # ctx.decl() and ctx.stmt() return lists of child contexts
        children = []
        for child in ctx.children:
            # Use default visitor dispatch; child could be DeclContext or StmtContext
            node = self.visit(child)
            if node is not None:
                children.append(node)
        return ProgramNode(children)

    def visitDecl(self, ctx):
        # Two possibilities:
        # 1) def Identifier(ParamList?) = expr ;
        # 2) def Identifier(ParamList?) block
        name = ctx.Identifier().getText()
        # ParamList may be None
        params = []
        if ctx.paramList():
            params = self.visit(ctx.paramList())
        if ctx.expr():
            # Case 1: = Expr ;
            expr_node = self.visit(ctx.expr())
            return DeclNode(name=name, params=params, expr=expr_node, block=None)
        else:
            # Case 2: block
            block_nodes = self.visit(ctx.block())
            return DeclNode(name=name, params=params, expr=None, block=block_nodes)

    def visitParamList(self, ctx):
        # paramList: expr (',' expr)*
        expr_nodes = [self.visit(expr_ctx) for expr_ctx in ctx.expr()]
        return expr_nodes

    def visitBlock(self, ctx):
        # block: '{' stmt* '}'
        stmts = []
        for stmt_ctx in ctx.stmt():
            node = self.visit(stmt_ctx)
            if node is not None:
                stmts.append(node)
        return stmts

    def visitLetStmt(self, ctx):
        name = ctx.Identifier().getText()
        expr_node = self.visit(ctx.expr())
        return LetNode(name=name, expr=expr_node)

    def visitIfStmt(self, ctx):
        cond_node = self.visit(ctx.expr())
        then_block = self.visit(ctx.block(0))
        else_block = []
        if ctx.block(1):
            else_block = self.visit(ctx.block(1))
        return IfNode(cond=cond_node, then_block=then_block, else_block=else_block)

    def visitForStmt(self, ctx):
        init_node = self.visit(ctx.expr(0))
        cond_node = self.visit(ctx.expr(1))
        post_node = self.visit(ctx.expr(2))
        body_nodes = self.visit(ctx.block())
        return ForNode(init_expr=init_node, cond_expr=cond_node, post_expr=post_node, body=body_nodes)

    def visitExprStmt(self, ctx):
        expr_node = self.visit(ctx.expr())
        return ExprStmtNode(expr=expr_node)

    # Placeholder for expression visiting. In a complete implementation, override
    # visitArithExpr, visitRelExpr, visitBitExpr, visitPrimaryExpr, etc.
    # For example:
    def visitPrimaryExpr(self, ctx):
        # ctx could be a literal, variable, function call, etc. Return a generic node
        text = ctx.getText()
        return ASTNode()  # Placeholder; replace with actual expression node

    # Default behavior for nodes without override: visit children recursively
    def visitChildren(self, node):
        result = None
        for c in node.getChildren():
            result = c.accept(self)
        return result


# ---------- Main Program Logic ----------

def main():
    # 1. Parse command-line arguments
    parser = argparse.ArgumentParser(description="Parse and optionally process a duduDSL file.")
    parser.add_argument("input_file", help="Path to the .dsl source file to parse.")
    parser.add_argument("--show-tokens", action="store_true",
                        help="Print all tokens produced by the lexer.")
    parser.add_argument("--show-parse-tree", action="store_true",
                        help="Print the full parse tree (Lisp-style).")
    parser.add_argument("--use-visitor", action="store_true",
                        help="Use Visitor pattern to build AST instead of Listener.")
    parser.add_argument("--output-ast", metavar="FILE", type=str,
                        help="Serialize the constructed AST to the specified file (pickle).")
    args = parser.parse_args()

    # 2. Read input file as a CharStream (UTF-8)
    try:
        char_stream = FileStream(args.input_file, encoding="utf-8")
    except IOError as e:
        sys.stderr.write(f"Error opening file {args.input_file}: {e}\n")
        sys.exit(1)

    # 3. Initialize the lexer and attach custom error listener
    lexer = duduDSLLexer(char_stream)
    error_listener_lexer = DuduDSLErrorListener()
    # Remove default ConsoleErrorListener and add our custom listener
    lexer.removeErrorListeners()
    lexer.addErrorListener(error_listener_lexer)

    # 4. Create token stream
    token_stream = CommonTokenStream(lexer)

    # 5. Optionally show tokens
    if args.show_tokens:
        token_stream.fill()
        print("=== Tokens ===")
        for token in token_stream.tokens:
            token_type = lexer.symbolicNames[token.type]
            print(f"{token.text}\t<{token_type}>\tLine:{token.line}, Column:{token.column}")
        print("==============\n")

    # 6. Initialize the parser and attach custom error listener
    parser = duduDSLParser(token_stream)
    error_listener_parser = DuduDSLErrorListener()
    parser.removeErrorListeners()
    parser.addErrorListener(error_listener_parser)

    # 7. Parse starting from the 'program' rule
    tree = parser.program()

    # 8. If any lexer or parser errors occurred, report and exit
    if error_listener_lexer.errors or error_listener_parser.errors:
        sys.stderr.write("Parsing aborted due to errors.\n")
        sys.exit(2)

    # 9. Optionally print the parse tree (Lisp-style)
    if args.show_parse_tree:
        print("=== Parse Tree ===")
        print(tree.toStringTree(recog=parser))
        print("==================\n")

    # 10. Process the parse tree via Listener or Visitor
    if args.use_visitor:
        # Visitor mode: build AST
        visitor = ASTBuilderVisitor()
        ast_root = visitor.visit(tree)
        print("[Visitor] AST constructed:")
        print(ast_root)
    else:
        # Listener mode: just walk and print events
        walker = ParseTreeWalker()
        listener = MyDuduDSLListener()
        walker.walk(listener, tree)
        ast_root = None  # No AST built in listener demo

    # 11. Optionally serialize AST to a file
    if args.output_ast:
        if ast_root is None:
            sys.stderr.write("No AST was built; skipping AST serialization.\n")
        else:
            try:
                with open(args.output_ast, "wb") as f:
                    pickle.dump(ast_root, f)
                print(f"[Info] AST serialized to {args.output_ast}")
            except IOError as e:
                sys.stderr.write(f"Error writing AST to file {args.output_ast}: {e}\n")
                sys.exit(3)

    # 12. Normal exit
    sys.exit(0)


if __name__ == "__main__":
    main()
