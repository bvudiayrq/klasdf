grammar duduDSL;

// Parser Rules

program
    : (decl | stmt)* EOF
    ;

decl
    : DEF Identifier LPAREN paramList? RPAREN ( ASSIGN expr SEMI | block )
    ;

stmt
    : ethtransfer
    | transfer
    | approve
    | nftApprove
    | transferFrom
    | nftTransferFrom
    | customStmt
    | letStmt
    | ifStmt
    | forStmt
    | exprStmt
    ;

exprStmt
    : expr SEMI
    ;

letStmt
    : LET Identifier ASSIGN expr SEMI
    ;

block
    : LBRACE stmt* RBRACE
    ;

paramList
    : expr ( COMMA expr )*
    ;

ethtransfer
    : TRANSFERETH LPAREN expr COMMA expr COMMA expr RPAREN SEMI
    ;

transfer
    : TRANSFER LPAREN expr COMMA expr RPAREN SEMI
    ;

approve
    : APPROVE LPAREN expr COMMA expr RPAREN SEMI
    ;

nftApprove
    : NFTAPPROVE LPAREN expr COMMA expr RPAREN SEMI
    ;

transferFrom
    : TRANSFERFROM LPAREN expr COMMA expr COMMA expr RPAREN SEMI
    ;

nftTransferFrom
    : NFTTRANSFERFROM LPAREN expr COMMA expr COMMA expr RPAREN SEMI
    ;

customStmt
    : CUSTOM LPAREN Identifier ( COMMA paramList )? RPAREN SEMI
    ;

ifStmt
    : IF LPAREN expr RPAREN block ( ELSE block )?
    ;

forStmt
    : FOR LPAREN expr SEMI expr SEMI expr RPAREN block
    ;

// Expression Rules (with operator precedence and indexing/slicing)

expr
    : expr LBRACK literalList RBRACK        # SliceExpr
    | expr LBRACK expr RBRACK               # IndexExpr
    | expr ArithOp expr                      # ArithExpr
    | expr RelOp expr                        # RelExpr
    | expr BitOp expr                        # BitExpr
    | primary                                # PrimaryExpr
    ;

primary
    : literal
    | MSGSENDER
    | CALCDATA
    | SHA3 LPAREN expr RPAREN
    | SLOAD LPAREN expr RPAREN
    | MLOAD LPAREN expr COMMA expr RPAREN
    | MSTORE LPAREN expr COMMA expr COMMA expr RPAREN
    | LENGTH LPAREN expr RPAREN
    | CONCAT LPAREN expr COMMA expr RPAREN
    | SSTORE LPAREN expr COMMA expr RPAREN
    | K LPAREN type COMMA expr RPAREN
    | BITVEC_K LPAREN literal RPAREN
    | LPAREN expr RPAREN
    | arrayLiteral
    ;

arrayLiteral
    : LBRACK expr ( COMMA expr )* RBRACK
    ;

literalList
    : literal ( COMMA literal )*
    ;

type
    : INT_TYPE
    | BITVEC_K LPAREN literal RPAREN
    ;

literal
    : INT_LITERAL
    | HEX_LITERAL
    ;

// Lexer Rules

ArithOp
    : PLUS
    | MINUS
    | MUL
    | DIV
    | MOD
    ;

RelOp
    : EQ
    | NEQ
    | LT
    | GT
    | LE
    | GE
    ;

BitOp
    : AND
    | OR
    | BITXOR
    | SHL
    | SHR
    ;

// Keywords

DEF            : 'def';
LET            : 'let';
IF             : 'if';
ELSE           : 'else';
FOR            : 'for';

TRANSFERETH    : 'transferEth';
TRANSFER       : 'transfer';
APPROVE        : 'approve';
NFTAPPROVE     : 'nftApprove';
TRANSFERFROM   : 'transferFrom';
NFTTRANSFERFROM: 'nftTransferFrom';
CUSTOM         : 'custom';

MSGSENDER      : 'msg.sender';
CALCDATA       : 'calldata';
SHA3           : 'sha3';
SLOAD          : 'sload';
MLOAD          : 'mload';
MSTORE         : 'mstore';
LENGTH         : 'length';
CONCAT         : 'concat';
SSTORE         : 'sstore';
K              : 'K';
BITVEC_K       : 'BitVec';

INT_TYPE       : 'Int';

// Operators & Delimiters

PLUS           : '+';
MINUS          : '-';
MUL            : '*';
DIV            : '/';
MOD            : '%';

EQ             : '==';
NEQ            : '!=';
LT             : '<';
GT             : '>';
LE             : '<=';
GE             : '>=';

AND            : '&';
OR             : '|';
BITXOR         : 'x';
SHL            : '<<';
SHR            : '>>';

LPAREN         : '(';
RPAREN         : ')';
LBRACE         : '{';
RBRACE         : '}';
LBRACK         : '[';
RBRACK         : ']';
COMMA          : ',';
SEMI           : ';';

ASSIGN         : '=';

// Literals

INT_LITERAL    : [0-9]+;
HEX_LITERAL    : '0x' [0-9A-Fa-f]+;

// Identifiers (must come after keywords)

Identifier
    : [a-zA-Z_] [a-zA-Z0-9_]*
    ;

// Whitespace and Comments

WS
    : [ \t\r\n]+ -> skip
    ;

LINE_COMMENT
    : '//' ~[\r\n]* -> skip
    ;

BLOCK_COMMENT
    : '/*' .*? '*/' -> skip
    ;
