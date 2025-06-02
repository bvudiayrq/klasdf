# Generated from duduDSL.g4 by ANTLR 4.12.0
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .duduDSLParser import duduDSLParser
else:
    from duduDSLParser import duduDSLParser

# This class defines a complete listener for a parse tree produced by duduDSLParser.
class duduDSLListener(ParseTreeListener):

    # Enter a parse tree produced by duduDSLParser#program.
    def enterProgram(self, ctx:duduDSLParser.ProgramContext):
        pass

    # Exit a parse tree produced by duduDSLParser#program.
    def exitProgram(self, ctx:duduDSLParser.ProgramContext):
        pass


    # Enter a parse tree produced by duduDSLParser#decl.
    def enterDecl(self, ctx:duduDSLParser.DeclContext):
        pass

    # Exit a parse tree produced by duduDSLParser#decl.
    def exitDecl(self, ctx:duduDSLParser.DeclContext):
        pass


    # Enter a parse tree produced by duduDSLParser#stmt.
    def enterStmt(self, ctx:duduDSLParser.StmtContext):
        pass

    # Exit a parse tree produced by duduDSLParser#stmt.
    def exitStmt(self, ctx:duduDSLParser.StmtContext):
        pass


    # Enter a parse tree produced by duduDSLParser#exprStmt.
    def enterExprStmt(self, ctx:duduDSLParser.ExprStmtContext):
        pass

    # Exit a parse tree produced by duduDSLParser#exprStmt.
    def exitExprStmt(self, ctx:duduDSLParser.ExprStmtContext):
        pass


    # Enter a parse tree produced by duduDSLParser#letStmt.
    def enterLetStmt(self, ctx:duduDSLParser.LetStmtContext):
        pass

    # Exit a parse tree produced by duduDSLParser#letStmt.
    def exitLetStmt(self, ctx:duduDSLParser.LetStmtContext):
        pass


    # Enter a parse tree produced by duduDSLParser#block.
    def enterBlock(self, ctx:duduDSLParser.BlockContext):
        pass

    # Exit a parse tree produced by duduDSLParser#block.
    def exitBlock(self, ctx:duduDSLParser.BlockContext):
        pass


    # Enter a parse tree produced by duduDSLParser#paramList.
    def enterParamList(self, ctx:duduDSLParser.ParamListContext):
        pass

    # Exit a parse tree produced by duduDSLParser#paramList.
    def exitParamList(self, ctx:duduDSLParser.ParamListContext):
        pass


    # Enter a parse tree produced by duduDSLParser#ethtransfer.
    def enterEthtransfer(self, ctx:duduDSLParser.EthtransferContext):
        pass

    # Exit a parse tree produced by duduDSLParser#ethtransfer.
    def exitEthtransfer(self, ctx:duduDSLParser.EthtransferContext):
        pass


    # Enter a parse tree produced by duduDSLParser#transfer.
    def enterTransfer(self, ctx:duduDSLParser.TransferContext):
        pass

    # Exit a parse tree produced by duduDSLParser#transfer.
    def exitTransfer(self, ctx:duduDSLParser.TransferContext):
        pass


    # Enter a parse tree produced by duduDSLParser#approve.
    def enterApprove(self, ctx:duduDSLParser.ApproveContext):
        pass

    # Exit a parse tree produced by duduDSLParser#approve.
    def exitApprove(self, ctx:duduDSLParser.ApproveContext):
        pass


    # Enter a parse tree produced by duduDSLParser#nftApprove.
    def enterNftApprove(self, ctx:duduDSLParser.NftApproveContext):
        pass

    # Exit a parse tree produced by duduDSLParser#nftApprove.
    def exitNftApprove(self, ctx:duduDSLParser.NftApproveContext):
        pass


    # Enter a parse tree produced by duduDSLParser#transferFrom.
    def enterTransferFrom(self, ctx:duduDSLParser.TransferFromContext):
        pass

    # Exit a parse tree produced by duduDSLParser#transferFrom.
    def exitTransferFrom(self, ctx:duduDSLParser.TransferFromContext):
        pass


    # Enter a parse tree produced by duduDSLParser#nftTransferFrom.
    def enterNftTransferFrom(self, ctx:duduDSLParser.NftTransferFromContext):
        pass

    # Exit a parse tree produced by duduDSLParser#nftTransferFrom.
    def exitNftTransferFrom(self, ctx:duduDSLParser.NftTransferFromContext):
        pass


    # Enter a parse tree produced by duduDSLParser#customStmt.
    def enterCustomStmt(self, ctx:duduDSLParser.CustomStmtContext):
        pass

    # Exit a parse tree produced by duduDSLParser#customStmt.
    def exitCustomStmt(self, ctx:duduDSLParser.CustomStmtContext):
        pass


    # Enter a parse tree produced by duduDSLParser#ifStmt.
    def enterIfStmt(self, ctx:duduDSLParser.IfStmtContext):
        pass

    # Exit a parse tree produced by duduDSLParser#ifStmt.
    def exitIfStmt(self, ctx:duduDSLParser.IfStmtContext):
        pass


    # Enter a parse tree produced by duduDSLParser#forStmt.
    def enterForStmt(self, ctx:duduDSLParser.ForStmtContext):
        pass

    # Exit a parse tree produced by duduDSLParser#forStmt.
    def exitForStmt(self, ctx:duduDSLParser.ForStmtContext):
        pass


    # Enter a parse tree produced by duduDSLParser#ArithExpr.
    def enterArithExpr(self, ctx:duduDSLParser.ArithExprContext):
        pass

    # Exit a parse tree produced by duduDSLParser#ArithExpr.
    def exitArithExpr(self, ctx:duduDSLParser.ArithExprContext):
        pass


    # Enter a parse tree produced by duduDSLParser#RelExpr.
    def enterRelExpr(self, ctx:duduDSLParser.RelExprContext):
        pass

    # Exit a parse tree produced by duduDSLParser#RelExpr.
    def exitRelExpr(self, ctx:duduDSLParser.RelExprContext):
        pass


    # Enter a parse tree produced by duduDSLParser#BitExpr.
    def enterBitExpr(self, ctx:duduDSLParser.BitExprContext):
        pass

    # Exit a parse tree produced by duduDSLParser#BitExpr.
    def exitBitExpr(self, ctx:duduDSLParser.BitExprContext):
        pass


    # Enter a parse tree produced by duduDSLParser#PrimaryExpr.
    def enterPrimaryExpr(self, ctx:duduDSLParser.PrimaryExprContext):
        pass

    # Exit a parse tree produced by duduDSLParser#PrimaryExpr.
    def exitPrimaryExpr(self, ctx:duduDSLParser.PrimaryExprContext):
        pass


    # Enter a parse tree produced by duduDSLParser#SliceExpr.
    def enterSliceExpr(self, ctx:duduDSLParser.SliceExprContext):
        pass

    # Exit a parse tree produced by duduDSLParser#SliceExpr.
    def exitSliceExpr(self, ctx:duduDSLParser.SliceExprContext):
        pass


    # Enter a parse tree produced by duduDSLParser#IndexExpr.
    def enterIndexExpr(self, ctx:duduDSLParser.IndexExprContext):
        pass

    # Exit a parse tree produced by duduDSLParser#IndexExpr.
    def exitIndexExpr(self, ctx:duduDSLParser.IndexExprContext):
        pass


    # Enter a parse tree produced by duduDSLParser#primary.
    def enterPrimary(self, ctx:duduDSLParser.PrimaryContext):
        pass

    # Exit a parse tree produced by duduDSLParser#primary.
    def exitPrimary(self, ctx:duduDSLParser.PrimaryContext):
        pass


    # Enter a parse tree produced by duduDSLParser#arrayLiteral.
    def enterArrayLiteral(self, ctx:duduDSLParser.ArrayLiteralContext):
        pass

    # Exit a parse tree produced by duduDSLParser#arrayLiteral.
    def exitArrayLiteral(self, ctx:duduDSLParser.ArrayLiteralContext):
        pass


    # Enter a parse tree produced by duduDSLParser#literalList.
    def enterLiteralList(self, ctx:duduDSLParser.LiteralListContext):
        pass

    # Exit a parse tree produced by duduDSLParser#literalList.
    def exitLiteralList(self, ctx:duduDSLParser.LiteralListContext):
        pass


    # Enter a parse tree produced by duduDSLParser#type.
    def enterType(self, ctx:duduDSLParser.TypeContext):
        pass

    # Exit a parse tree produced by duduDSLParser#type.
    def exitType(self, ctx:duduDSLParser.TypeContext):
        pass


    # Enter a parse tree produced by duduDSLParser#literal.
    def enterLiteral(self, ctx:duduDSLParser.LiteralContext):
        pass

    # Exit a parse tree produced by duduDSLParser#literal.
    def exitLiteral(self, ctx:duduDSLParser.LiteralContext):
        pass



del duduDSLParser