# Generated from duduDSL.g4 by ANTLR 4.12.0
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .duduDSLParser import duduDSLParser
else:
    from duduDSLParser import duduDSLParser

# This class defines a complete generic visitor for a parse tree produced by duduDSLParser.

class duduDSLVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by duduDSLParser#program.
    def visitProgram(self, ctx:duduDSLParser.ProgramContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#decl.
    def visitDecl(self, ctx:duduDSLParser.DeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#stmt.
    def visitStmt(self, ctx:duduDSLParser.StmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#exprStmt.
    def visitExprStmt(self, ctx:duduDSLParser.ExprStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#letStmt.
    def visitLetStmt(self, ctx:duduDSLParser.LetStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#block.
    def visitBlock(self, ctx:duduDSLParser.BlockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#paramList.
    def visitParamList(self, ctx:duduDSLParser.ParamListContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#ethtransfer.
    def visitEthtransfer(self, ctx:duduDSLParser.EthtransferContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#transfer.
    def visitTransfer(self, ctx:duduDSLParser.TransferContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#approve.
    def visitApprove(self, ctx:duduDSLParser.ApproveContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#nftApprove.
    def visitNftApprove(self, ctx:duduDSLParser.NftApproveContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#transferFrom.
    def visitTransferFrom(self, ctx:duduDSLParser.TransferFromContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#nftTransferFrom.
    def visitNftTransferFrom(self, ctx:duduDSLParser.NftTransferFromContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#customStmt.
    def visitCustomStmt(self, ctx:duduDSLParser.CustomStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#ifStmt.
    def visitIfStmt(self, ctx:duduDSLParser.IfStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#forStmt.
    def visitForStmt(self, ctx:duduDSLParser.ForStmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#ArithExpr.
    def visitArithExpr(self, ctx:duduDSLParser.ArithExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#RelExpr.
    def visitRelExpr(self, ctx:duduDSLParser.RelExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#BitExpr.
    def visitBitExpr(self, ctx:duduDSLParser.BitExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#PrimaryExpr.
    def visitPrimaryExpr(self, ctx:duduDSLParser.PrimaryExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#SliceExpr.
    def visitSliceExpr(self, ctx:duduDSLParser.SliceExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#IndexExpr.
    def visitIndexExpr(self, ctx:duduDSLParser.IndexExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#primary.
    def visitPrimary(self, ctx:duduDSLParser.PrimaryContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#arrayLiteral.
    def visitArrayLiteral(self, ctx:duduDSLParser.ArrayLiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#literalList.
    def visitLiteralList(self, ctx:duduDSLParser.LiteralListContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#type.
    def visitType(self, ctx:duduDSLParser.TypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by duduDSLParser#literal.
    def visitLiteral(self, ctx:duduDSLParser.LiteralContext):
        return self.visitChildren(ctx)



del duduDSLParser