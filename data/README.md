### DISL Dataset

The DISL dataset comprises 514,506 unique Solidity smart contracts deployed on the Ethereum mainnet. These contracts were aggregated from Etherscan up to January 15, 2024 (approximately block 19,010,000). The dataset includes both raw and deduplicated subsets, with the deduplication performed using Jaccard similarity (threshold 0.9) to ensure diversity. Each entry contains the contract's source code, ABI, compiler version, optimization settings, and other metadata. This dataset serves as a valuable resource for developing machine learning systems and benchmarking software engineering tools designed for smart contracts.

### XBlock Framework

XBlock is the component architecture used by Open edX for building courseware. It provides a Python-based API for creating modular learning components, such as video players and problem types, which can be combined hierarchically to build complex educational experiences. XBlocks are deployable units that can be integrated into the Open edX platform, allowing for extensibility and customization of course content.

### Data Collection Process

To study common DeFi behaviors, we utilized the DISL dataset to obtain verified smart contract source codes, ABIs, and associated metadata. This information provided insights into contract functionalities and structures. Complementing this, we employed tools compatible with the XBlock framework to extract transaction data, including ERC-20 and ERC-721 token interactions, as well as contract bytecode. By integrating these datasets, we constructed a comprehensive view of DeFi activities, facilitating the analysis of prevalent behaviors within the ecosystem.


  For each of Defi behaviors (e.g., liquidity pool swaps, airdrop), follow a similar pattern:

1. **Event/Function Filter**
   - Identify specific event signatures or function selectors related to the behavior (e.g., Uniswap’s `Swap` events).
   - Scan DISL/XBlock transaction data for matching logs.
2. **Contract/Transaction Extraction**
   - Aggregate contract addresses or transaction hashes matching the filter.
   - Fetch on-chain bytecode or verify source from DISL when available.
3. **Deduplication & Validation**
   - Compute bytecode hashes to remove replicas.
   - Optionally cross-reference source code from DISL to confirm behavior-specific implementation.

For example, erc20_contracts.csv and erc721_contracts.csv are the contract addresses after deduplication.
