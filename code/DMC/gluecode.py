import sys
from typing import List, Dict, Tuple, Any, Optional

# ------------------------------------------------------------------------------
# Data Structures and Type Aliases
# ------------------------------------------------------------------------------

SummaryStmt = Dict[str, Any]
StateVarsType = Dict[str, str]
InitValuesType = Dict[str, str]
APDefsType = Dict[str, str]
LTLSpecsType = List[str]

# ------------------------------------------------------------------------------
# Globals
# ------------------------------------------------------------------------------

STATE_VARS: StateVarsType = {}
INITIAL_VALUES: InitValuesType = {}
AP_DEFINITIONS: APDefsType = {}
BUSINESS_SPECS: LTLSpecsType = []
SAFETY_SPECS: LTLSpecsType = []

PerVarCases: Dict[str, List[Tuple[str, str]]] = {}

# ------------------------------------------------------------------------------
# Utility Functions
# ------------------------------------------------------------------------------

def sanitize_identifier(name: str) -> str:
    """Sanitize identifiers to ensure compatibility with NuSMV."""
    return "".join(c if c.isalnum() or c == "_" else f"_{ord(c):x}" for c in name)

def initialize_global_cases(state_vars: StateVarsType) -> None:
    """Initialize global state transition cases."""
    global PerVarCases
    PerVarCases = {sanitize_identifier(k): [] for k in state_vars.keys()}

def add_case_for_var(var_name: str, guard: str, expr: str) -> None:
    """Add a state transition case for a variable."""
    clean_var = sanitize_identifier(var_name)
    PerVarCases[clean_var].append((guard.strip(), expr.strip()))

def merge_default_cases() -> None:
    """Add default cases to ensure complete coverage."""
    for var, clauses in PerVarCases.items():
        if not any(guard == "TRUE" for guard, _ in clauses):
            clauses.append(("TRUE", var))

# ------------------------------------------------------------------------------
# Core Functions to Process Each Statement Type
# ------------------------------------------------------------------------------

def process_swap(stmt: SummaryStmt) -> None:
    """Process swap compound operations in DeFi protocols."""
    guard = stmt.get("guard", "TRUE").strip() or "TRUE"
    
    # Process input/output transfers
    input_transfers = stmt.get("input_transfers", [])
    output_transfers = stmt.get("output_transfers", [])
    
    # Build transfer conditions
    transfer_conditions = []
    for (from_addr, amount) in input_transfers:
        from_var = f"balance[{sanitize_identifier(from_addr)}]"
        transfer_conditions.append(f"{from_var} >= {amount}")
    
    for (to_addr, amount) in output_transfers:
        to_var = f"balance[{sanitize_identifier(to_addr)}]"
        transfer_conditions.append(f"{to_var} + {amount} <= MAX_UINT")
    
    combined_guard = guard
    if transfer_conditions:
        combined_guard = f"({guard}) & ({' & '.join(transfer_conditions)})"

    # Apply state updates
    for from_addr, amount in input_transfers:
        from_var = f"balance[{sanitize_identifier(from_addr)}]"
        add_case_for_var(from_var, combined_guard, f"{from_var} - {amount}")
    
    for to_addr, amount in output_transfers:
        to_var = f"balance[{sanitize_identifier(to_addr)}]"
        add_case_for_var(to_var, combined_guard, f"{to_var} + {amount}")

def process_add_liquidity(stmt: SummaryStmt) -> None:
    """Process add liquidity compound operations in DeFi protocols."""
    guard = stmt.get("guard", "TRUE").strip() or "TRUE"
    
    # Get asset pairs and liquidity token information
    assets = stmt.get("assets", [])
    liquidity_token = stmt.get("liquidity_token", "")
    
    # Calculate total supply
    total_supply = f"total_supply[{sanitize_identifier(liquidity_token)}]"
    
    # Build transfer conditions
    transfer_conditions = []
    for (asset, amount) in assets:
        asset_var = f"balance[{sanitize_identifier(asset)}]"
        transfer_conditions.append(f"{asset_var} >= {amount}")
    
    combined_guard = guard
    if transfer_conditions:
        combined_guard = f"({guard}) & ({' & '.join(transfer_conditions)})"

    # Update asset balances
    for asset, amount in assets:
        asset_var = f"balance[{sanitize_identifier(asset)}]"
        add_case_for_var(asset_var, combined_guard, f"{asset_var} - {amount}")
    
    # Update liquidity token supply
    if liquidity_token:
        add_case_for_var(total_supply, combined_guard, 
                        f"{total_supply} + calculate_liquidity_amount({', '.join(f'{a}={amt}' for a, amt in assets)})")

def process_remove_liquidity(stmt: SummaryStmt) -> None:
    """Process remove liquidity compound operations in DeFi protocols."""
    guard = stmt.get("guard", "TRUE").strip() or "TRUE"
    
    # Get liquidity token and asset pairs
    liquidity_token = stmt.get("liquidity_token", "")
    assets = stmt.get("assets", [])
    
    # Get current total supply
    total_supply = f"total_supply[{sanitize_identifier(liquidity_token)}]"
    
    # Build conditions
    conditions = [f"{total_supply} >= {stmt.get('liquidity_amount', 0)}"]
    combined_guard = f"({guard}) & ({' & '.join(conditions)})"

    # Update liquidity token supply
    if liquidity_token:
        add_case_for_var(total_supply, combined_guard, 
                        f"{total_supply} - {stmt.get('liquidity_amount', 0)}")
    
    # Update asset balances
    for asset, amount in assets:
        asset_var = f"balance[{sanitize_identifier(asset)}]"
        add_case_for_var(asset_var, combined_guard, f"{asset_var} + {amount}")

def process_rebase(stmt: SummaryStmt) -> None:
    """Process rebase operations in DeFi protocols."""
    guard = stmt.get("guard", "TRUE").strip() or "TRUE"
    
    # Get rebase parameters
    total_supply = stmt.get("total_supply", "total_supply")
    shares_per_token = stmt.get("shares_per_token", "shares_per_token")
    rebase_amount = stmt.get("rebase_amount", 0)
    
    # Update total supply
    add_case_for_var(total_supply, guard, 
                    f"{total_supply} + {rebase_amount}")
    
    # Update shares per token
    add_case_for_var(shares_per_token, guard,
                    f"{shares_per_token} * ({total_supply} + {rebase_amount}) / {total_supply}")

def process_airdrop(stmt: SummaryStmt) -> None:
    """Process airdrop operations in DeFi protocols."""
    guard = stmt.get("guard", "TRUE").strip() or "TRUE"
    
    # Get distribution information
    recipients = stmt.get("recipients", [])
    
    # Distribute tokens
    for recipient, amount in recipients:
        balance_var = f"balance[{sanitize_identifier(recipient)}]"
        add_case_for_var(balance_var, guard, f"{balance_var} + {amount}")

def process_custom(stmt: SummaryStmt) -> None:
    """Process custom operations in DeFi protocols."""
    guard = stmt.get("guard", "TRUE").strip() or "TRUE"
    
    # Get custom operation parameters
    operation_type = stmt.get("operation_type", "custom")
    parameters = stmt.get("parameters", {})
    
    # Handle specific operation types
    if operation_type == "swap":
        process_swap(stmt)
    elif operation_type == "add_liquidity":
        process_add_liquidity(stmt)
    elif operation_type == "remove_liquidity":
        process_remove_liquidity(stmt)
    elif operation_type == "rebase":
        process_rebase(stmt)
    elif operation_type == "airdrop":
        process_airdrop(stmt)
    else:
        # Default handling for simple updates
        for (lhs_raw, rhs_raw) in stmt.get("updates", []):
            lhs = sanitize_identifier(lhs_raw)
            rhs = rhs_raw.strip()
            add_case_for_var(lhs, guard, rhs)

def process_control_flow(stmt: SummaryStmt) -> None:
    """Process complex control flow structures in DeFi protocols."""
    guard = stmt.get("guard", "TRUE").strip() or "TRUE"
    
    # Handle if-else nesting
    if stmt.get("stmt_type") == "IfStmt":
        then_branch = stmt.get("then_branch", [])
        else_branch = stmt.get("else_branch", [])
        
        # Process then branch
        for nested in then_branch:
            nested_guard = f"({guard}) & ({nested.get('guard', 'TRUE')})"
            nested_copy = dict(nested)
            nested_copy["guard"] = nested_guard
            dispatch_statement(nested_copy)
        
        # Process else branch
        if else_branch:
            for nested in else_branch:
                nested_guard = f"(!({guard})) & ({nested.get('guard', 'TRUE')})"
                nested_copy = dict(nested)
                nested_copy["guard"] = nested_guard
                dispatch_statement(nested_copy)
    
    # Handle for loops
    elif stmt.get("stmt_type") == "ForStmt":
        loop_var = stmt.get("loop_var", "i")
        start = int(stmt.get("loop_start", 0))
        end = int(stmt.get("loop_end", 10))
        body = stmt.get("loop_body", [])
        
        for i in range(start, end):
            iter_guard = f"({guard}) & ({loop_var} = {i})"
            
            for nested in body:
                nested_copy = dict(nested)
                # Replace loop variables
                substituted_exprs = []
                for (lhs, rhs) in nested_copy.get("updates", []):
                    substituted_lhs = lhs.replace(loop_var, str(i))
                    substituted_rhs = rhs.replace(loop_var, str(i))
                    substituted_exprs.append((substituted_lhs, substituted_rhs))
                
                nested_copy["updates"] = substituted_exprs
                nested_copy["guard"] = f"{iter_guard} & ({nested_copy.get('guard', 'TRUE')})"
                dispatch_statement(nested_copy)

# ------------------------------------------------------------------------------
# Dispatch Function
# ------------------------------------------------------------------------------

def dispatch_statement(stmt: SummaryStmt) -> None:
    """Dispatch statements to appropriate handlers based on type."""
    stmt_type = stmt.get("stmt_type", "unknown")
    
    if stmt_type == "Transfer":
        process_transfer(stmt)
    elif stmt_type == "Approve":
        process_approve(stmt)
    elif stmt_type == "NFTApprove":
        process_nft_approve(stmt)
    elif stmt_type == "TransferFrom":
        process_transfer_from(stmt)
    elif stmt_type == "NFTTransferFrom":
        process_nft_transfer_from(stmt)
    elif stmt_type == "Custom":
        process_custom(stmt)
    elif stmt_type == "ControlFlow":
        process_control_flow(stmt)
    else:
        print(f"Warning: Unhandled stmt_type: {stmt_type}", file=sys.stderr)

# ------------------------------------------------------------------------------
# Main Function to Generate NuSMV Model
# ------------------------------------------------------------------------------

def generate_nusmv_model_from_summaries(
    dsl_summaries: List[SummaryStmt],
    state_vars: StateVarsType,
    initial_values: InitValuesType,
    ap_definitions: APDefsType,
    business_specs: LTLSpecsType,
    safety_specs: LTLSpecsType,
    filename: str
) -> None:
    """Generate a NuSMV model from DeFi summaries."""
    # Initialize state variable handling
    initialize_global_cases(state_vars)
    
    # Process all summary statements
    for stmt in dsl_summaries:
        dispatch_statement(stmt)
    
    # Merge default cases
    merge_default_cases()
    
    # Write NuSMV model
    with open(filename, "w") as f:
        f.write("MODULE main\n")
        f.write("/* Auto-generated NuSMV model from DSL summaries */\n\n")
        
        # Define state variables
        f.write("VAR\n")
        for var_name, var_range in state_vars.items():
            clean_name = sanitize_identifier(var_name)
            f.write(f"    {clean_name} : {var_range};\n")
        f.write("\n")
        
        # Define atomic propositions
        f.write("DEFINE\n")
        for ap_name, ap_expr in ap_definitions.items():
            clean_ap = sanitize_identifier(ap_name)
            f.write(f"    {clean_ap} := {ap_expr};\n")
        f.write("\n")
        
        # Initialize values
        f.write("INIT\n")
        for var_name, init_expr in initial_values.items():
            clean_var = sanitize_identifier(var_name)
            f.write(f"    {clean_var} := {init_expr};\n")
        f.write("\n")
        
        # State transitions
        f.write("TRANS\n")
        for var, clauses in PerVarCases.items():
            f.write(f"    next({var}) := case\n")
            for (guard, expr) in clauses:
                f.write(f"        {guard} : {expr};\n")
            f.write(f"    esac;\n\n")
        
        # Specifications
        f.write("SPEC\n")
        for spec in business_specs:
            f.write(f"    {spec};\n")
        for spec in safety_specs:
            f.write(f"    {spec};\n")
    
    print(f"NuSMV model successfully written to '{filename}'")