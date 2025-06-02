"""This module contains functionality for hooking in detection modules and
executing them."""

from mythril.analysis.module import ModuleLoader, reset_callback_modules
from mythril.analysis.module.base import EntryPoint
from mythril.analysis.report import Issue

from typing import Optional, List
import logging
import hashlib
import json

from mythril.analysis.module.modules.DefiCheck3 import DefiCheck3,NodeType #,detector

log = logging.getLogger(__name__)

# 实现业务图的构建、存储和比较
class Graph:
    def __init__(self):
        self.nodes = {}
        self.edges = {}

    def add_node(self, node, node_type):
        self.nodes[node] = node_type

    def add_edge(self, from_node, to_node):
        if from_node in self.edges:
            self.edges[from_node].append(to_node)
        else:
            self.edges[from_node] = [to_node]

    def to_string(self):
        return json.dumps({'nodes': self.nodes, 'edges': self.edges}, sort_keys=True)

    def get_hash(self):
        graph_string = self.to_string()
        return hashlib.sha256(graph_string.encode('utf-8')).hexdigest()
    
    @staticmethod
    def compare_graphs(graph1, graph2):
        return graph1.get_hash() == graph2.get_hash()
    
    # @staticmethod
    # def save_graph(graph, filename):
    #     with open(filename, 'w') as f:
    #         f.write(graph.to_string())

    # @staticmethod
    # def load_graph(filename): #
    #     with open(filename, 'r') as f:
    #         data = json.load(f)
    #         graph = Graph()
    #         graph.nodes = data['nodes']
    #         graph.edges = data['edges']
    #         return graph
    
    @staticmethod
    def save_graph_hash(graph, filename,issue):
        with open(filename, 'a') as f:
            f.write(graph.get_hash(),issue,'\n')
    
    def load_graph_hash_list(filename):
        with open(filename, 'r') as f:
            return f.readlines()
    
    @staticmethod
    def build_graph(definodes,func_name): # 使用deficheck3构建业务图
        func_graph = Graph()
        #TODO
        return func_graph
        
    @staticmethod
    def defi_check_based_on_graphs(graph):
        #TODO:读取已有的业务图，进行比较
        detector = DefiCheck3()
        for func_name in detector.function_dict:
            func_graph = Graph.build_graph(detector.nodes,func_name)
            #读取文件中哈希及对应问题进行比较
        

def retrieve_callback_issues(white_list: Optional[List[str]] = None) -> List[Issue]:
    """Get the issues discovered by callback type detection modules"""
    issues: List[Issue] = []
    for module in ModuleLoader().get_detection_modules(
        entry_point=EntryPoint.CALLBACK, white_list=white_list
    ):
        log.debug("Retrieving results for " + module.name)
        issues += module.issues

    reset_callback_modules(module_names=white_list)
    import time
    from mythril.analysis.module.modules.DefiCheck3 import PreProcExpr,flag_detailed,flag_time,flag_airdrop,flag_check,flag_ERC,flag_NFT_MB
    # 添加issues
    detector = DefiCheck3()
    print("=== defi_check ===")
    if flag_check:
        if flag_ERC:
            issues += detector.defi_handle()
        if flag_NFT_MB:
            issues += detector.defi_handle2()
    
    if flag_time:
        start_time = time.time()
    for Func_name in detector.function_dict:
        func_type,identity_dict = detector.check_func_type(Func_name,detector.nodes)
        detector.function_dict[Func_name] = func_type
        print("\nFunc_name: ",Func_name,"func_type: ",func_type)
        for node in detector.nodes:
            if detector.nodes[node].function_name == Func_name:
                print("node:",detector.nodes[node].get_dict())
    
    for node_uid in range(len(detector.nodes)-1, -1, -1):
        if detector.nodes[node_uid].node_type != NodeType.CONTROL_FLOW:
            last_node = detector.nodes[node_uid]
            break
    
    print("== detect_loops1 ==") 
    if flag_check and flag_airdrop:
        # last_node.detect_loops_test(detector.nodes)
        from mythril.analysis.module.modules.DefiCheck3 import Node as DefiNode
        # DefiNode.get_all_path(func_name="approve(uint256)",nodes=detector.nodes)
        _,res_func_cfg_uids,res_func_paths = DefiNode.detect_loops(detector.nodes)
        # for func_name in res_func_paths:
        #     print("func_name: ",func_name)
        #     i = 0
        #     for path in res_func_cfg_uids[func_name].values():
        #         i = i + 1
        #         print("cfg",i,"path:",path)
        #     i = 0
        #     for path in res_func_paths[func_name]:
        #         i = i + 1
        #         print("func_path",i,": ",path)
        print("detect_airdrop:")
        airdrop_issues = DefiNode.detect_airdrop(detector.nodes)
        if airdrop_issues:
            # airdrop_issues list
            issues += airdrop_issues
                
    print("== detect_loops2 ==")
    
    if flag_time:
        end_time = time.time()
        print("Func nodes print time: ",end_time-start_time)
    
    print("\nidentity_dict: ")
    identity_list = detector.identity_dict.keys()
    for identity in identity_list:
        print("identity: ",identity,"  ",detector.identity_dict[identity])
    # 打印function_dict
    print("\nfunction_dict: ")
    for Func_name in detector.function_dict:
        print("Func_name: ",Func_name,"  func_type: ",detector.function_dict[Func_name])
    
    if flag_time:
        from mythril.analysis.module.modules.DefiCheck3 import Node as DefiNode
        print("\n== find_edge_time==")
        # print("find_edge_time total: ",DefiNode.find_edge_time)
        print("find_edge_time: ")
        for opcode in DefiNode.find_edge_time:
            print("opcode: ",opcode,"  time: ",DefiNode.find_edge_time[opcode])
        print("find_start_nodes_time total: ",DefiNode.find_start_nodes_time)
        # print("equal_is_time:")
        # for opcode in DefiNode.equal_is_time:
        #     print("opcode: ",opcode,"  time: ",DefiNode.equal_is_time[opcode])
        # print("equal_str_time:")
        # for opcode in DefiNode.equal_str_time:
        #     print("opcode: ",opcode,"  time: ",DefiNode.equal_str_time[opcode])
        # 打印detector每个函数的总用时及函数操作码用时：func_opcode_time
        # print("== hook func_opcode_time ==")
        # for func_name in detector.func_opcode_time:
        #     func_time = 0
        #     for opcode in detector.func_opcode_time[func_name]:
        #         print("* func_name: ",func_name,"  opcode: ",opcode,"  time: ",detector.func_opcode_time[func_name][opcode])
        #         func_time += detector.func_opcode_time[func_name][opcode]
        #     print("func_name: ",func_name,"  func_time: ",func_time)
        print("== func_opcode_time execute time ==")
        from mythril.laser.ethereum.svm import func_opcode_exec_time
        total_excute_time = 0
        for func_name in func_opcode_exec_time:
            func_time = 0
            for opcode in func_opcode_exec_time[func_name]:
                print("# func_name: ",func_name,"  opcode: ",opcode,"  time: ",func_opcode_exec_time[func_name][opcode])
                func_time += func_opcode_exec_time[func_name][opcode]
                total_excute_time += func_opcode_exec_time[func_name][opcode]
            print("func_name: ",func_name,"  func_time: ",func_time)
        print("total_excute_time: ",total_excute_time)
        # global start_exec_hooks_time,stop_exec_hooks_time,check_path_time
        from mythril.laser.ethereum.svm import start_exec_hooks_time,stop_exec_hooks_time,check_path_time
        print("start_exec_hooks time:",start_exec_hooks_time)
        print("stop_exec_hooks_time time:",stop_exec_hooks_time)
        print("check_path_time time:",check_path_time)

    return issues


def fire_lasers(statespace, white_list: Optional[List[str]] = None) -> List[Issue]:
    """Fire lasers at analysed statespace object

    :param statespace: Symbolic statespace to analyze
    :param white_list: Optionally whitelist modules to use for the analysis
    :return: Discovered issues
    """
    log.info("Starting analysis")

    issues: List[Issue] = []
    for module in ModuleLoader().get_detection_modules(
        entry_point=EntryPoint.POST, white_list=white_list
    ):
        log.info("Executing " + module.name)
        issues += module.execute(statespace)

    issues += retrieve_callback_issues(white_list)
    return issues
