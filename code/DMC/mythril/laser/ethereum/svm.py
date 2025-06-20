"""This module implements the main symbolic execution engine."""
import logging
from collections import defaultdict
from copy import copy
from datetime import datetime, timedelta
import random
from typing import Callable, Dict, DefaultDict, List, Tuple, Optional

from mythril.support.opcodes import OPCODES
from mythril.analysis.potential_issues import check_potential_issues
from mythril.laser.execution_info import ExecutionInfo
from mythril.laser.ethereum.cfg import NodeFlags, Node, Edge, JumpType
from mythril.laser.ethereum.evm_exceptions import StackUnderflowException, VmException
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.instruction_data import get_required_stack_elements
from mythril.laser.plugin.signals import PluginSkipWorldState, PluginSkipState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.strategy.basic import DepthFirstSearchStrategy
from mythril.laser.ethereum.strategy.constraint_strategy import DelayConstraintStrategy
from abc import ABCMeta
from mythril.laser.ethereum.time_handler import time_handler
import time


from mythril.laser.ethereum.transaction import (
    ContractCreationTransaction,
    TransactionEndSignal,
    TransactionStartSignal,
    execute_contract_creation,
    execute_message_call,
)
from mythril.laser.smt import And, symbol_factory, simplify
from mythril.support.support_args import args
from mythril.analysis.module.modules.DefiCheck3 import PreProcExpr,flag_detailed,flag_time
from mythril.analysis.module.modules.DefiCheck3 import DefiCheck3 #,detector
from mythril.analysis.module.modules.DefiCheck3 import not_airdrop_list,flag_airdrop
from mythril.analysis.module.modules.DefiCheck3 import not_NFT_MB,flag_NFT_MB

start_exec_hooks_time = 0
stop_exec_hooks_time = 0
check_path_time = 0
func_opcode_exec_time = {} # 执行用时

log = logging.getLogger(__name__)


class SVMError(Exception):
    """An exception denoting an unexpected state in symbolic execution."""

    pass


class LaserEVM:
    """The LASER EVM.

    Just as Mithril had to be mined at great efforts to provide the
    Dwarves with their exceptional armour, LASER stands at the heart of
    Mythril, digging deep in the depths of call graphs, unearthing the
    most precious symbolic call data, that is then hand-forged into
    beautiful and strong security issues by the experienced smiths we
    call detection modules. It is truly a magnificent symbiosis.
    """

    def __init__(
        self,
        dynamic_loader=None,
        max_depth=float("inf"),
        execution_timeout=60,
        create_timeout=10,
        strategy=DepthFirstSearchStrategy,
        transaction_count=2,
        requires_statespace=True,
        iprof=None,
        use_reachability_check=True,
        beam_width=None,
        tx_strategy=None,
    ) -> None:
        """
        Initializes the laser evm object

        :param dynamic_loader: Loads data from chain
        :param max_depth: Maximum execution depth this vm should execute
        :param execution_timeout: Time to take for execution
        :param create_timeout: Time to take for contract creation
        :param strategy: Execution search strategy
        :param transaction_count: The amount of transactions to execute
        :param requires_statespace: Variable indicating whether the statespace should be recorded
        :param iprof: Instruction Profiler
        :param use_reachability_check: Runs reachability check by solving constraints
        :param beam_width: The beam width for search strategies
        :param tx_strategy: A global tx prioritisation strategy
        """
        self.execution_info: List[ExecutionInfo] = []

        self.open_states: List[WorldState] = []
        self.total_states = 0
        self.dynamic_loader = dynamic_loader
        self.use_reachability_check = use_reachability_check

        self.work_list: List[GlobalState] = []
        self.strategy = strategy(self.work_list, max_depth, beam_width=beam_width)
        self.max_depth = max_depth
        self.transaction_count = transaction_count
        self.tx_strategy = tx_strategy

        self.execution_timeout = execution_timeout or 0
        self.create_timeout = create_timeout or 0

        self.requires_statespace = requires_statespace
        if self.requires_statespace:
            self.nodes: Dict[int, Node] = {}
            self.edges: List[Edge] = []

        self.time: datetime = None
        self.executed_transactions: bool = False

        self.pre_hooks: DefaultDict[str, List[Callable]] = defaultdict(list)
        self.post_hooks: DefaultDict[str, List[Callable]] = defaultdict(list)

        self._add_world_state_hooks: List[Callable] = []
        self._execute_state_hooks: List[Callable] = []

        self._start_exec_trans_hooks: List[Callable] = []
        self._stop_exec_trans_hooks: List[Callable] = []

        self._start_sym_trans_hooks: List[Callable] = []
        self._stop_sym_trans_hooks: List[Callable] = []

        self._start_sym_exec_hooks: List[Callable] = []
        self._stop_sym_exec_hooks: List[Callable] = []

        self._start_exec_hooks: List[Callable] = []
        self._stop_exec_hooks: List[Callable] = []

        self._transaction_end_hooks: List[Callable] = []

        self.iprof = iprof
        self.instr_pre_hook: Dict[str, List[Callable]] = {}
        self.instr_post_hook: Dict[str, List[Callable]] = {}
        for op in OPCODES:
            self.instr_pre_hook[op] = []
            self.instr_post_hook[op] = []
        self.hook_type_map = {
            "start_execute_transactions": self._start_exec_trans_hooks,
            "stop_execute_transactions": self._stop_exec_trans_hooks,
            "add_world_state": self._add_world_state_hooks,
            "execute_state": self._execute_state_hooks,
            "start_sym_exec": self._start_sym_exec_hooks,
            "stop_sym_exec": self._stop_sym_exec_hooks,
            "start_sym_trans": self._start_sym_trans_hooks,
            "stop_sym_trans": self._stop_sym_trans_hooks,
            "start_exec": self._start_exec_hooks,
            "stop_exec": self._stop_exec_hooks,
            "transaction_end": self._transaction_end_hooks,
        }
        log.info("LASER EVM initialized with dynamic loader: " + str(dynamic_loader))

    def extend_strategy(self, extension: ABCMeta, **kwargs) -> None:
        self.strategy = extension(self.strategy, **kwargs)

    def sym_exec(
        self,
        world_state: WorldState = None,
        target_address: int = None,
        creation_code: str = None,
        contract_name: str = None,
    ) -> None:
        """Starts symbolic execution
        There are two modes of execution.
        Either we analyze a preconfigured configuration, in which case the world_state and target_address variables
        must be supplied.
        Or we execute the creation code of a contract, in which case the creation code and desired name of that
        contract should be provided.

        :param world_state The world state configuration from which to perform analysis
        :param target_address The address of the contract account in the world state which analysis should target
        :param creation_code The creation code to create the target contract in the symbolic environment
        :param contract_name The name that the created account should be associated with
        """
        pre_configuration_mode = target_address is not None
        scratch_mode = creation_code is not None and contract_name is not None
        if pre_configuration_mode == scratch_mode:
            raise ValueError("Symbolic execution started with invalid parameters")

        log.debug("Starting LASER execution")
        for hook in self._start_sym_exec_hooks:
            hook()

        time_handler.start_execution(self.execution_timeout)
        self.time = datetime.now()

        if pre_configuration_mode:
            self.open_states = [world_state]
            log.info("Starting message call transaction to {}".format(target_address))
            print("Starting message call transaction to {}".format(target_address))
            self.execute_transactions(symbol_factory.BitVecVal(target_address, 256))

        elif scratch_mode:
            log.info("Starting contract creation transaction")
            print("Starting contract creation transaction")

            created_account = execute_contract_creation(
                self, creation_code, contract_name, world_state=world_state
            )
            log.info(
                "Finished contract creation, found {} open states".format(
                    len(self.open_states)
                )
            )
            print("Finished contract creation, found {} open states".format(
                    len(self.open_states)
                )
            )

            if len(self.open_states) == 0:
                log.warning(
                    "No contract was created during the execution of contract creation "
                    "Increase the resources for creation execution (--max-depth or --create-timeout) "
                    "Check whether the bytecode is indeed the creation code, otherwise use the --bin-runtime flag"
                )
                print("No contract was created during the execution of contract creation "
                    "Increase the resources for creation execution (--max-depth or --create-timeout) "
                    "Check whether the bytecode is indeed the creation code, otherwise use the --bin-runtime flag"
                )

            self.execute_transactions(created_account.address)

        log.info("Finished symbolic execution")
        print("Finished symbolic execution")
        if self.requires_statespace:
            log.info(
                "%d nodes, %d edges, %d total states",
                len(self.nodes),
                len(self.edges),
                self.total_states,
            )

        for hook in self._stop_sym_exec_hooks:
            hook()

    def execute_transactions(self, address) -> None:
        """This function helps runs plugins that can order transactions.
        Such plugins should set self.executed_transactions as True after its execution

        :param address: Address of the contract
        :return: None
        """
        for hook in self._start_exec_trans_hooks:
            hook()
        if self.tx_strategy is None:
            if self.executed_transactions is False:
                self.time = datetime.now()
                self._execute_transactions_incremental(
                    address, txs=args.transaction_sequences
                )
        else:
            self.time = datetime.now()
            self._execute_transactions_non_ordered(address)
        for hook in self._stop_exec_trans_hooks:
            hook()

    def _execute_transactions_non_ordered(self, address):
        """
        This function executes multiple transactions non-incrementally, using some type priority ordering

        :param address: Address of the contract
        :return:
        """
        for txs in self.strategy:
            log.info(f"Executing the sequence: {txs}")
            self._execute_transactions_incremental(address, txs=tx)

    def _execute_transactions_incremental(self, address, txs=None):
        """This function executes multiple transactions incrementally on the address

        :param address: Address of the contract
        :return:
        """

        for i in range(self.transaction_count):
            if len(self.open_states) == 0:
                break
            old_states_count = len(self.open_states)
            # Clear journal at every new user transaction
            for state in self.open_states:
                state.transient_storage.clear()
            if self.use_reachability_check:
                if isinstance(self.strategy, DelayConstraintStrategy):
                    open_states = []
                    for state in self.open_states:
                        c_val = self.strategy.model_cache.check_quick_sat(
                            simplify(And(*state.world_state.constraints)).raw
                        )
                        if c_val:
                            open_states.append(self.open_states)
                        else:
                            self.strategy.pending_worklist.append(state)

                else:
                    self.open_states = [
                        state
                        for state in self.open_states
                        if state.constraints.is_possible()
                    ]
                    prune_count = old_states_count - len(self.open_states)
                if prune_count:
                    log.info("Pruned {} unreachable states".format(prune_count))
            log.info(
                "Starting message call transaction, iteration: {}, {} initial states".format(
                    i, len(self.open_states)
                )
            )
            func_hashes = txs[i] if txs else None

            if func_hashes:
                for itr, func_hash in enumerate(func_hashes):
                    if func_hash in (-1, -2):
                        func_hashes[itr] = func_hash
                    else:
                        func_hashes[itr] = bytes.fromhex(hex(func_hash)[2:].zfill(8))

            for hook in self._start_sym_trans_hooks:
                hook()

            execute_message_call(self, address, func_hashes=func_hashes)

            for hook in self._stop_sym_trans_hooks:
                hook()

        self.executed_transactions = True

    def _check_create_termination(self) -> bool:
        if len(self.open_states) != 0:
            return (
                self.create_timeout > 0
                and self.time + timedelta(seconds=self.create_timeout) <= datetime.now()
            )
        return self._check_execution_termination()

    def _check_execution_termination(self) -> bool:
        return (
            self.execution_timeout > 0
            and self.time + timedelta(seconds=self.execution_timeout) <= datetime.now()
        )

    def exec(self, create=False, track_gas=False) -> Optional[List[GlobalState]]:
        """

        :param create:
        :param track_gas:
        :return:
        """
        final_states: List[GlobalState] = []
        # detector = DefiCheck3()
        temp_time = time.time()
        for hook in self._start_exec_hooks:
            hook()
        global start_exec_hooks_time,stop_exec_hooks_time,check_path_time
        start_exec_hooks_time += time.time()-temp_time
        print("start_exec_hooks_time: ",start_exec_hooks_time)

        for global_state in self.strategy:
            if create and self._check_create_termination():
                log.debug("Hit create timeout, returning.")
                print("Hit create timeout, returning.")
                return final_states + [global_state] if track_gas else None

            if not create and self._check_execution_termination():
                log.debug("Hit execution timeout, returning.")
                print("Hit execution timeout, returning.")
                return final_states + [global_state] if track_gas else None
            try:
                Func_name = global_state.environment.active_function_name
                Instruction_execute_start_time = time.time()
                #添加len(self.work_list)
                global_state.work_list_len = len(self.work_list)+1 # 加上自己
                new_states, op_code = self.execute_state(global_state)
                # 记录每个操作码的执行时间
                global func_opcode_exec_time
                if Func_name not in func_opcode_exec_time:
                    func_opcode_exec_time[Func_name] = {}
                    func_opcode_exec_time[Func_name][op_code] = time.time()-Instruction_execute_start_time
                elif op_code not in func_opcode_exec_time[Func_name]:
                    func_opcode_exec_time[Func_name][op_code] = time.time()-Instruction_execute_start_time
                else:
                    func_opcode_exec_time[Func_name][op_code] += time.time()-Instruction_execute_start_time
                
            except NotImplementedError:
                log.debug("Encountered unimplemented instruction")
                continue
            new_states_count = len(new_states)
            # print(new_states_count)
            if flag_airdrop: # 排除常见的非空投函数避免耗时过长
                if Func_name not in ["fallback","constructor"]: # 必须执行的函数
                    # if Func_name in not_airdrop_list:
                    if any(not_airdrop in Func_name for not_airdrop in not_airdrop_list):
                        new_states = []
            if flag_NFT_MB:
                if Func_name not in ["fallback","constructor"]: # 必须执行的函数
                    if any(Func_name.startswith(keyword) for keyword in not_NFT_MB):
                        new_states = []
                        print("not_NFT_MB: ",Func_name)
                    
                
            temp_time = time.time()
            if self.strategy.run_check() and (
                len(new_states) > 1 and random.uniform(0, 1) < args.pruning_factor
            ):
                new_states = [
                    state
                    for state in new_states
                    if state.world_state.constraints.is_possible()
                ]
            if flag_detailed and len(new_states) != new_states_count and global_state.environment.active_function_name != "constructor":
                print("Pruned {} unreachable states".format(new_states_count - len(new_states)))
                print("reachable new_states: ",len(new_states))
            check_path_time += time.time()-temp_time
            self.manage_cfg(op_code, new_states)  # TODO: What about op_code is None?
            if new_states:
                self.work_list += new_states
            elif track_gas:
                final_states.append(global_state)
            self.total_states += len(new_states)
            # print("total_states: ",self.total_states)

        temp_time = time.time()
        for hook in self._stop_exec_hooks:
            hook()
        stop_exec_hooks_time += time.time()-temp_time

        return final_states if track_gas else None

    def _add_world_state(self, global_state: GlobalState):
        """Stores the world_state of the passed global state in the open states"""
        if flag_detailed:
            print("# add world state")
        for hook in self._add_world_state_hooks:
            try:
                hook(global_state)
            except PluginSkipWorldState:
                return
        if flag_detailed:
            print("len(self.open_states): ",len(self.open_states))
        self.open_states.append(global_state.world_state)
        if flag_detailed:
            print("len(self.open_states): ",len(self.open_states))

    def handle_vm_exception(
        self, global_state: GlobalState, op_code: str, error_msg: str
    ) -> List[GlobalState]:
        _, return_global_state = global_state.transaction_stack.pop()

        if return_global_state is None:
            # In this case we don't put an unmodified world state in the open_states list Since in the case of an
            #  exceptional halt all changes should be discarded, and this world state would not provide us with a
            #  previously unseen world state
            log.debug("Encountered a VmException, ending path: `{}`".format(error_msg))
            print("# Encountered a VmException, ending path: `{}`".format(error_msg))
            new_global_states: List[GlobalState] = []
        else:
            # First execute the post hook for the transaction ending instruction
            self._execute_post_hook(op_code, [global_state])
            new_global_states = self._end_message_call(
                return_global_state, global_state, revert_changes=True, return_data=None
            )
        return new_global_states

    def execute_state(
        self, global_state: GlobalState
    ) -> Tuple[List[GlobalState], Optional[str]]:
        """Execute a single instruction in global_state.

        :param global_state:
        :return: A list of successor states.
        """
        # Execute hooks
        import time 
        state_hook_start_time = time.time()
        try:
            for hook in self._execute_state_hooks:
                hook(global_state)
        except PluginSkipState:
            return [], None
        state_hook_end_time = time.time()

        instructions_start_time = time.time()
        instructions = global_state.environment.code.instruction_list
        try:
            op_code = instructions[global_state.mstate.pc]["opcode"]
            
            Func_name = global_state.environment.active_function_name
            # if True:
            ignore_func = ['name()','symbol()','decimals()','totalSupply()','balanceOf(address)']
            # if True: # 打印操作码和堆栈信息，方便查看
            if flag_time:
                # 打印当前时间XX时XX分XX秒
                now = datetime.now()
                print("now:",now.strftime("%H:%M:%S"))
            if flag_detailed:  
                symbolVar_to_str_time = time.time()
                if Func_name in ignore_func:
                    pass # 跳过无关函数，加快速度
                elif Func_name != "constructor" and Func_name != "fallback":#and Func_name == "transferFrom(address,address,uint256)"
                    symbol_var_expr = PreProcExpr(str(simplify(global_state.mstate.stack[-1])))
                    argument = ""
                    if op_code.startswith("PUSH") :
                        #如果存在argument
                        if instructions[global_state.mstate.pc].get("argument") is not None:
                            argument = str(instructions[global_state.mstate.pc]["argument"])
                    if len(symbol_var_expr) > 1000:
                        if argument != "":
                            print("* ",Func_name," op_code:",op_code," argument: ",argument)
                        else:
                            print("* ",Func_name," op_code:",op_code," ")
                    else:
                        if argument != "":
                            print("* ",Func_name," op_code:",op_code," argument: ",argument,"  stack[-1]:  ",symbol_var_expr)
                        else:
                            print("* ",Func_name," op_code:",op_code,"  stack[-1]:  ",symbol_var_expr)
                        if op_code in ['ADD','SUB'] :
                            print("stack[-2]: ",PreProcExpr(str(simplify(global_state.mstate.stack[-2]))))
                elif Func_name == "constructor":
                    if op_code.startswith("PUSH") :
                        #如果存在argument
                        if instructions[global_state.mstate.pc].get("argument") is not None:
                            argument = str(instructions[global_state.mstate.pc]["argument"])
                            print("* ",Func_name," op_code:",op_code," argument: ",argument)
                    else:
                        print("* ",Func_name," op_code:",op_code," ")
                if flag_time:
                    print("symbolVar_to_str_time: ",time.time()-symbolVar_to_str_time)
            # else:
            #     print("* ",Func_name," op_code:",op_code," ")
                
                
        except IndexError:
            self._add_world_state(global_state)
            return [], None
        instructions_end_time = time.time()
        
        exception_start_time = time.time()
        if len(global_state.mstate.stack) < get_required_stack_elements(op_code):
            error_msg = (
                "Stack Underflow Exception due to insufficient "
                "stack elements for the address {}".format(
                    instructions[global_state.mstate.pc]["address"]
                )
            )
            new_global_states = self.handle_vm_exception(
                global_state, op_code, error_msg
            )
            self._execute_post_hook(op_code, new_global_states)
            return new_global_states, op_code
        exception_end_time = time.time()

        pre_hook_start_time = time.time()
        try:
            self._execute_pre_hook(op_code, global_state)
        except PluginSkipState:
            return [], None
        pre_hook_end_time = time.time()
        
        instr_start_time = time.time()
        try:
            new_global_states = Instruction(
                op_code,
                self.dynamic_loader,
                pre_hooks=self.instr_pre_hook[op_code],
                post_hooks=self.instr_post_hook[op_code],
            ).evaluate(global_state)

        except VmException as e:
            for hook in self._transaction_end_hooks:
                hook(
                    global_state,
                    global_state.current_transaction,
                    None,
                    False,
                )
            new_global_states = self.handle_vm_exception(global_state, op_code, str(e))
            

        except TransactionStartSignal as start_signal:
            # Setup new global state
            new_global_state = start_signal.transaction.initial_global_state()

            new_global_state.transaction_stack = copy(
                global_state.transaction_stack
            ) + [(start_signal.transaction, global_state)]
            new_global_state.node = global_state.node
            new_global_state.world_state.constraints = (
                start_signal.global_state.world_state.constraints
            )

            log.debug("Starting new transaction %s", start_signal.transaction)

            return [new_global_state], op_code

        except TransactionEndSignal as end_signal:
            (
                transaction,
                return_global_state,
            ) = end_signal.global_state.transaction_stack[-1]
            if flag_detailed:
                print("TransactionEndSignal")

            log.debug("Ending transaction %s.", transaction)

            for hook in self._transaction_end_hooks:
                hook(
                    end_signal.global_state,
                    transaction,
                    return_global_state,
                    end_signal.revert,
                )

            if return_global_state is None:
                if (
                    not isinstance(transaction, ContractCreationTransaction)
                    or transaction.return_data
                ) and not end_signal.revert:
                    check_potential_issues(global_state)
                    end_signal.global_state.world_state.node = global_state.node
                    self._add_world_state(end_signal.global_state)
                else:
                    if flag_detailed:
                        print("No add state:revert or ...")
                new_global_states = []
            else:
                if flag_detailed:
                    print("No add state:return_global_state is not None")
                # First execute the post hook for the transaction ending instruction
                self._execute_post_hook(op_code, [end_signal.global_state])

                # Propagate annotations
                new_annotations = [
                    annotation
                    for annotation in global_state.annotations
                    if annotation.persist_over_calls
                ]
                return_global_state.add_annotations(new_annotations)

                new_global_states = self._end_message_call(
                    copy(return_global_state),
                    global_state,
                    revert_changes=False or end_signal.revert,
                    return_data=transaction.return_data,
                )
        instr_end_time = time.time()

        post_hook_start_time = time.time()
        self._execute_post_hook(op_code, new_global_states)
        post_hoook_end_time = time.time()
        
        # if post_hoook_end_time - state_hook_start_time > 5:
        #     print("=======execute_state=======")
        #     print("state_hook time: ",state_hook_end_time-state_hook_start_time)
        #     print("instructions time: ",instructions_end_time-instructions_start_time)
        #     print("exception time: ",exception_end_time-exception_start_time)
        #     print("pre_hook time: ",pre_hook_end_time-pre_hook_start_time)
        #     print("instr time: ",instr_end_time-instr_start_time)
        #     print("post_hook time: ",post_hoook_end_time-post_hook_start_time)
        #     print("total time: ",post_hoook_end_time-state_hook_start_time)
        # else:
        #     print("execute_state total time: ",post_hoook_end_time-state_hook_start_time)
        
        # if flag_detailed:
        #     print("TransactionEndSignal handle end")
        return new_global_states, op_code

    def _end_message_call(
        self,
        return_global_state: GlobalState,
        global_state: GlobalState,
        revert_changes=False,
        return_data=None,
    ) -> List[GlobalState]:
        """

        :param return_global_state:
        :param global_state:
        :param revert_changes:
        :param return_data:
        :return:
        """

        return_global_state.world_state.constraints += (
            global_state.world_state.constraints
        )
        # Resume execution of the transaction initializing instruction
        op_code = return_global_state.environment.code.instruction_list[
            return_global_state.mstate.pc
        ]["opcode"]

        # Set execution result in the return_state
        return_global_state.last_return_data = return_data
        if not revert_changes:
            return_global_state.world_state = copy(global_state.world_state)
            return_global_state.environment.active_account = global_state.accounts[
                return_global_state.environment.active_account.address.value
            ]
            if isinstance(
                global_state.current_transaction, ContractCreationTransaction
            ):
                return_global_state.mstate.min_gas_used += (
                    global_state.mstate.min_gas_used
                )
                return_global_state.mstate.max_gas_used += (
                    global_state.mstate.max_gas_used
                )
        try:
            # Execute the post instruction handler
            new_global_states = Instruction(
                op_code,
                self.dynamic_loader,
                pre_hooks=self.instr_pre_hook[op_code],
                post_hooks=self.instr_post_hook[op_code],
            ).evaluate(return_global_state, True)
        except VmException:
            new_global_states = []
        # In order to get a nice call graph we need to set the nodes here
        for state in new_global_states:
            state.node = global_state.node

        return new_global_states

    def manage_cfg(self, opcode: str, new_states: List[GlobalState]) -> None:
        """

        :param opcode:
        :param new_states:
        """
        if opcode == "JUMP":
            assert len(new_states) <= 1
            for state in new_states:
                self._new_node_state(state)
        elif opcode == "JUMPI":
            assert len(new_states) <= 2
            for state in new_states:
                self._new_node_state(
                    state, JumpType.CONDITIONAL, state.world_state.constraints[-1]
                )
        elif opcode == "RETURN":
            for state in new_states:
                self._new_node_state(state, JumpType.RETURN)

        for state in new_states:
            state.node.states.append(state)

    def _new_node_state(
        self, state: GlobalState, edge_type=JumpType.UNCONDITIONAL, condition=None
    ) -> None:
        """

        :param state:
        :param edge_type:
        :param condition:
        """
        try:
            address = state.environment.code.instruction_list[state.mstate.pc][
                "address"
            ]
        except IndexError:
            return
        new_node = Node(state.environment.active_account.contract_name)
        old_node = state.node
        state.node = new_node
        new_node.constraints = state.world_state.constraints
        if self.requires_statespace:
            self.nodes[new_node.uid] = new_node
            self.edges.append(
                Edge(
                    old_node.uid, new_node.uid, edge_type=edge_type, condition=condition
                )
            )
            print("edge_type: ",edge_type)

        if edge_type == JumpType.RETURN:
            new_node.flags |= NodeFlags.CALL_RETURN
        elif edge_type == JumpType.CALL:
            try:
                if "retval" in str(state.mstate.stack[-1]):
                    new_node.flags |= NodeFlags.CALL_RETURN
                else:
                    new_node.flags |= NodeFlags.FUNC_ENTRY
            except StackUnderflowException:
                new_node.flags |= NodeFlags.FUNC_ENTRY

        environment = state.environment
        disassembly = environment.code

        # Only set when encountering new JUMPI
        if edge_type == JumpType.CONDITIONAL:
            if isinstance(
                state.world_state.transaction_sequence[-1], ContractCreationTransaction
            ):
                environment.active_function_name = "constructor"
            elif address in disassembly.address_to_function_name:
                # Enter a new function
                environment.active_function_name = disassembly.address_to_function_name[
                    address
                ]
                new_node.flags |= NodeFlags.FUNC_ENTRY

                log.debug(
                    "- Entering function "
                    + environment.active_account.contract_name
                    + ":"
                    + new_node.function_name
                )
            elif address == 0:
                environment.active_function_name = "fallback"

        new_node.function_name = environment.active_function_name

    def register_hooks(self, hook_type: str, hook_dict: Dict[str, List[Callable]]):
        """

        :param hook_type:
        :param hook_dict:
        """
        if hook_type == "pre":
            entrypoint = self.pre_hooks
        elif hook_type == "post":
            entrypoint = self.post_hooks
        else:
            raise ValueError(
                "Invalid hook type %s. Must be one of {pre, post}", hook_type
            )

        for op_code, funcs in hook_dict.items():
            entrypoint[op_code].extend(funcs)

    def register_laser_hooks(self, hook_type: str, hook: Callable):
        """registers the hook with this Laser VM"""

        if hook_type in self.hook_type_map:
            self.hook_type_map[hook_type].append(hook)
        else:
            raise ValueError(f"Invalid hook type {hook_type}")

    def register_instr_hooks(self, hook_type: str, opcode: str, hook: Callable):
        """Registers instructions hooks from plugins"""
        if hook_type == "pre":
            if opcode is None:
                for op in OPCODES:
                    self.instr_pre_hook[op].append(hook(op))
            else:
                self.instr_pre_hook[opcode].append(hook)
        else:
            if opcode is None:
                for op in OPCODES:
                    self.instr_post_hook[op].append(hook(op))
            else:
                self.instr_post_hook[opcode].append(hook)

    def instr_hook(self, hook_type, opcode) -> Callable:
        """Registers the annotated function with register_instr_hooks

        :param hook_type: Type of hook pre/post
        :param opcode: The opcode related to the function
        """

        def hook_decorator(func: Callable):
            """Hook decorator generated by laser_hook

            :param func: Decorated function
            """
            self.register_instr_hooks(hook_type, opcode, func)

        return hook_decorator

    def laser_hook(self, hook_type: str) -> Callable:
        """Registers the annotated function with register_laser_hooks

        :param hook_type:
        :return: hook decorator
        """

        def hook_decorator(func: Callable):
            """Hook decorator generated by laser_hook

            :param func: Decorated function
            """
            self.register_laser_hooks(hook_type, func)
            return func

        return hook_decorator

    def _execute_pre_hook(self, op_code: str, global_state: GlobalState) -> None:
        """

        :param op_code:
        :param global_state:
        :return:
        """
        if op_code not in self.pre_hooks.keys():
            return
        for hook in self.pre_hooks[op_code]:
            hook(global_state)

    def _execute_post_hook(
        self, op_code: str, global_states: List[GlobalState]
    ) -> None:
        """

        :param op_code:
        :param global_states:
        :return:
        """
        if op_code not in self.post_hooks.keys():
            return

        for hook in self.post_hooks[op_code]:
            for global_state in global_states:
                try:
                    hook(global_state)
                except PluginSkipState:
                    global_states.remove(global_state)

    def pre_hook(self, op_code: str) -> Callable:
        """

        :param op_code:
        :return:
        """

        def hook_decorator(func: Callable):
            """

            :param func:
            :return:
            """
            if op_code not in self.pre_hooks.keys():
                self.pre_hooks[op_code] = []
            self.pre_hooks[op_code].append(func)
            return func

        return hook_decorator

    def post_hook(self, op_code: str) -> Callable:
        """

        :param op_code:
        :return:
        """

        def hook_decorator(func: Callable):
            """

            :param func:
            :return:
            """
            if op_code not in self.post_hooks.keys():
                self.post_hooks[op_code] = []
            self.post_hooks[op_code].append(func)
            return func

        return hook_decorator
