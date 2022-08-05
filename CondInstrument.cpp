//------------------------------------------------------------------------------
// Clang rewriter sample. Demonstrates:
//
// * How to use RecursiveASTVisitor to find interesting AST nodes.
// * How to use the Rewriter API to rewrite the source code.
//
// Eli Bendersky (eliben@gmail.com)
// This code is in the public domain
//------------------------------------------------------------------------------
#include <cstdio>
#include <memory>
#include <iostream>
#include <sstream>
#include <string>

#include "clang/Frontend/FrontendAction.h"

#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/CommonOptionsParser.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/TargetOptions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Parse/ParseAST.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/raw_ostream.h"

struct IsBinCondResult {
  bool is_bc = false;
  clang::BinaryOperator *binaryOp = nullptr;
};

class BitmapHelper {
public:
  static std::map<std::string, int> blockIndexMap;
  static int blockBitmapCount;
  
  static std::map<std::string, int> condIndexMap;
  static int condBitmapCount;
  static std::map<int, std::string> condDesc;

  static std::map<std::string, int> decIndexMap;
  static int decBitmapCount;
  static std::map<int, std::string> decDesc;

  static std::map<std::string, int> mcdcIndexMap;
  static int mcdcBitmapCount;
  static std::map<int, int> mcdcConditionNumInDecision;
  static std::map<int, std::string> mcdcConditionDescInDecision;
};

std::string GetAddressString(void *ss) {
  std::stringstream ssStr;
  ssStr << ss;
  std::string bbStr = ssStr.str();
  return bbStr;
}

int RegistBitmapIDFromAddress(void *ss, std::map<std::string, int> blockIndexMap, int &bcount,
                std::string extra) {
  int cbid = bcount;
  bcount++;
  std::string cbbStr = GetAddressString(ss);
  blockIndexMap[cbbStr + extra] = cbid;
  return cbid;
}

std::string ASTNode2Str(clang::Stmt *d, clang::Rewriter & TheRewriter) {
  clang::SourceManager &sm = TheRewriter.getSourceMgr();
  const clang::LangOptions &lopt = TheRewriter.getLangOpts();
  clang::SourceLocation b(d->getBeginLoc()), _e(d->getEndLoc());
  if (b.isMacroID())
    b = sm.getSpellingLoc(b);
  if (_e.isMacroID())
    _e = sm.getSpellingLoc(_e);
  clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, sm, lopt));
  return std::string(sm.getCharacterData(b),
                     sm.getCharacterData(e) - sm.getCharacterData(b));
}

IsBinCondResult JudgeIsBinaryBoolCondition(clang::Stmt * s) {
  bool is_bc = false;
  clang::BinaryOperator *binaryOp = nullptr; 
  if (clang::isa<clang::BinaryOperator>(s)) {
    binaryOp = clang::cast<clang::BinaryOperator>(s);

    clang::BinaryOperator::Opcode op = binaryOp->getOpcode();

    clang::Expr *lhs = binaryOp->getLHS();
    clang::Expr *rhs = binaryOp->getRHS();

    switch (op) {
    case clang::BinaryOperator::Opcode::BO_LT: // "<"
    case clang::BinaryOperator::Opcode::BO_GT: // ">"
    case clang::BinaryOperator::Opcode::BO_LE: // "<="
    case clang::BinaryOperator::Opcode::BO_GE: // ">="
    case clang::BinaryOperator::Opcode::BO_EQ: // "=="
    case clang::BinaryOperator::Opcode::BO_NE: // "!="
      is_bc = true;
      break;
    case clang::BinaryOperator::Opcode::BO_And:
    case clang::BinaryOperator::Opcode::BO_Or:
      is_bc = true;
      break;
    default:
      break;
    }
  }
  if (clang::isa<clang::UnaryOperator>(s)) {
    // do nothing.
    // we only consider binary Comparator. 
  }
  IsBinCondResult ibor{is_bc, binaryOp};
  return ibor;
}

bool JudgeIsNonLeafCond(clang::Stmt * s) {
  bool condIsNonLeaf = false;
  if (clang::isa<clang::BinaryOperator>(s)) {
    clang::BinaryOperator *binaryOp = clang::cast<clang::BinaryOperator>(s);
    clang::BinaryOperator::Opcode op = binaryOp->getOpcode();
    switch (op) {
    case clang::BinaryOperator::Opcode::BO_And:
    case clang::BinaryOperator::Opcode::BO_Or:
      condIsNonLeaf = true;
      break;
    default:
      break;
    }
  }
  if (clang::isa<clang::UnaryOperator>(s)) {
    clang::UnaryOperator *unaryOp = clang::cast<clang::UnaryOperator>(s);
    clang::UnaryOperator::Opcode op = unaryOp->getOpcode();
    switch (op) {
    case clang::UnaryOperator::Opcode::UO_Not:
      condIsNonLeaf = true;
      break;
    default:
      break;
    }
  }
  if (clang::isa<clang::ParenExpr>(s)) {
    clang::ParenExpr *parenOp = clang::cast<clang::ParenExpr>(s);
    condIsNonLeaf = true;
  }
  return condIsNonLeaf;
}

int HandleDecisionCoverage(void *condAddr, std::string condStr) {
  /*
  handle condition coverage.
  */
  // this is for true of condition
  int cbid = BitmapHelper::decBitmapCount;
  BitmapHelper::decBitmapCount++;
  // this is for false of condition
  int fcbid = BitmapHelper::decBitmapCount;
  BitmapHelper::decBitmapCount++;
  std::string cbbStr =
      GetAddressString(condAddr); // static_cast<const void*>(cond_addr)
  BitmapHelper::decIndexMap[cbbStr] = cbid;
  BitmapHelper::decIndexMap[cbbStr + "F"] = fcbid;
  BitmapHelper::decDesc[cbid] = condStr + "==true";
  BitmapHelper::decDesc[fcbid] = condStr + "==false";
  return cbid;
}

int HandleConditionCoverage(void *condAddr, std::string condStr) {
  /*
  handle condition coverage.
  */
  // this is for true of condition
  int cbid = BitmapHelper::condBitmapCount;
  BitmapHelper::condBitmapCount++;
  // this is for false of condition
  int fcbid = BitmapHelper::condBitmapCount;
  BitmapHelper::condBitmapCount++;
  std::string cbbStr =
      GetAddressString(condAddr); // static_cast<const void*>(cond_addr)
  BitmapHelper::condIndexMap[cbbStr] = cbid;
  BitmapHelper::condIndexMap[cbbStr + "F"] = fcbid;
  BitmapHelper::condDesc[cbid] = condStr + "==true";
  BitmapHelper::condDesc[fcbid] = condStr + "==false";
  return cbid;
}

void HandleLeafConditionExpression(const int bid,
                                   clang::Stmt * cond, 
                                   int &decCondId,
                                   clang::Rewriter &TheRewriter) {
  std::string condStr = ASTNode2Str(cond, TheRewriter);
  int cbid = HandleConditionCoverage(cond, condStr);
  //	std::string varName = "b_" + std::to_string(bid) + "_" +
  //std::to_string(condId);
  // std::string modifiedExpr = condition->expressionStr;
  // assert(itr != BitmapHelper::mcdcConditionDescInDecision.end());
  std::map<int, std::string>::iterator itr =
      BitmapHelper::mcdcConditionDescInDecision.find(bid);
  std::string oriDescStr = itr->second + "#" + condStr;
  BitmapHelper::mcdcConditionDescInDecision[bid] = oriDescStr;
  //	std::string mcdc_a_vect = "BitmapCov::mcdcBitmap[" + std::to_string(bid)
  //+ "]"; 	flatCode += "int last_pos = " + mcdc_a_vect + ".size() - 1;\n";
  //	flatCode += mcdc_a_vect + "[last_pos] = " + mcdc_a_vect + "[last_pos] |
  //(((int)" + varName + ") << " + std::to_string(condId) + ");\n";
  //	AddCodeToModifyMCDCLast(flatCode, bid, varName, condId);
//  std::string fExpr = "BitmapCov::CondAndMCDCRecord(" + condStr + ", " +
                      std::to_string(cbid) + ", " + std::to_string(decCondId) +
                      ", " + std::to_string(bid) + ")";

  std::string preInsert = "BitmapCov::CondAndMCDCRecord(";
  std::string postInsert = ", " + std::to_string(cbid) + ", " +
                           std::to_string(decCondId) + ", " +
                           std::to_string(bid) + ")";

  TheRewriter.InsertText(cond->getBeginLoc(), preInsert, true, true);
  TheRewriter.InsertText(cond->getEndLoc().getLocWithOffset(1), postInsert,
                         true, true);

  decCondId++;
}

void HandleConditionExpression(
    const int bid, clang::Stmt * condition, 
                            int &decCondId, clang::Rewriter &TheRewriter) {
  /*
  comment = true;
  mcdc computation:
  test case1:     0010;F;
  test case2:     0000;T;
  xor:            0010;1;
  Cond1:          0010;

  ...
  Cond2:          0001;
  Cond1 or Cond2: 0011 -> Coverage Info.
  Storage: int;
  Number of Conditions < 31;
  */
  bool condIsNonLeaf = JudgeIsNonLeafCond(condition);
  //  std::string opPre = "";
//  std::string opPost = "";
//  bool trimOpPost = true;
  /*switch (condition->type) {
  case Token::Type::And: {
    opPost = InstrumentEnv::disableShortCircuit ? "&" : "&&";
    condIsNonLeaf = true;
    break;
  }
  case Token::Type::Or: {
    opPost = InstrumentEnv::disableShortCircuit ? "|" : "||";
    condIsNonLeaf = true;
    break;
  }
  case Token::Type::Not: {
    opPre = "!";
    condIsNonLeaf = true;
    break;
  }
  case Token::Type::Bracket: {
    opPre = "(";
    opPost = ")";
    trimOpPost = false;
    condIsNonLeaf = true;
    break;
  }
  default:
    break;
  }*/
//  std::string modifiedExpr = "";
  if (condIsNonLeaf) {
    for (auto it = condition->child_begin(); it != condition->child_end(); it++) {
      clang::Stmt * child = *it;
      HandleConditionExpression(bid, child, decCondId, TheRewriter);
    }
    /*std::vector<Expression *> childs = condition->childExpressions;
    for (Expression *child : childs) {
      modifiedExpr +=
          (opPre +
           HandleConditionExpression(bid, child, exprStrMap, decCondId) +
           opPost);
    }
    if (trimOpPost && opPost != "" && stringEndsWith(modifiedExpr, opPost)) {
      modifiedExpr =
          modifiedExpr.substr(0, modifiedExpr.length() - opPost.length());
    }*/
  } else {
//    const void *condAddr = static_cast<const void *>(condition);
//    std::string cbbStr = GetAddressString(condition);
//    bool exist = exprStrMap.find(cbbStr) != exprStrMap.end();
//    std::string rstr = (exist ? exprStrMap[cbbStr] : condition->expressionStr);
    // condAddr, 
    HandleLeafConditionExpression(bid, condition, decCondId, TheRewriter);
    //    modifiedExpr += HandleLeafConditionExpression(
//        bid, condAddr, condition->expressionStr, rstr, decCondId);
  }
  //	int cbid = HandleConditionCoverage(static_cast<const void*>(condition),
  //condition->expressionStr); 	modifiedExpr = "BitmapCov::CondRecord(" +
  //modifiedExpr + ", " + std::to_string(cbid) + ")";
//   return modifiedExpr;
}

/*void GetRootVarName(const void* block, std::string& rootVarName)
{
        std::string bbStr = GetAddressString(static_cast<const void*>(block));

        std::map<std::string, int>::iterator itr =
BitmapHelper::mcdcIndexMap.find(bbStr);
        // assert(itr != BitmapHelper::mcdcIndexMap.end());
        int bid = itr->second;
        rootVarName += "b_" + std::to_string(bid) + "_" + std::to_string(0);
}*/

// const void* block, 
void GenerateMCDCToRootExpression(clang::BinaryOperator * condition,
                                  clang::Rewriter & TheRewriter) {
  if (condition == nullptr) {
    return;
  }
  //  std::map<std::string, std::string> exprStrMap;

  int bid = BitmapHelper::mcdcBitmapCount;
  BitmapHelper::mcdcBitmapCount++;

  //	AddCodeToCreateNewMCDCLast(flatCode, bid);

  std::string bbStr =
      GetAddressString(condition); // block

  BitmapHelper::mcdcIndexMap[bbStr] = bid;
  BitmapHelper::mcdcConditionDescInDecision[bid] = "";
  int condId = 1;
  // exprStrMap, 
//  std::string modifiedExpr =
  HandleConditionExpression(bid, condition, condId, TheRewriter);
  int condNum = condId - 1;
  BitmapHelper::mcdcConditionNumInDecision[bid] = condNum;
  //	std::string rootVarName = "";
  //	GetRootVarName(block, rootVarName);
  //	flatCode += "bool " + rootVarName + " = " + modifiedExpr + ";\n";
  //	flatCode += "BitmapCov::mcdcBitmap[" + std::to_string(bid) + "] |=
  //(((int)" + rootVarName + ") << 0);\n"; 	AddCodeToModifyMCDCLast(flatCode,
  //bid, rootVarName, 0);
  int decid = HandleDecisionCoverage(condition, ASTNode2Str(condition, TheRewriter));

  std::string preInsert = "BitmapCov::CondAndMCDCRecord(";
  std::string postInsert = ", -" + std::to_string(decid + 1) + ", 0, " + std::to_string(bid) + ")";

  TheRewriter.InsertText(condition->getBeginLoc(), preInsert, 
                         true, true);
  TheRewriter.InsertText(condition->getEndLoc().getLocWithOffset(1), postInsert, 
                         true, true);
//  return fExpr;
}

/*std::string GenerateMCDCToOneCondExpression(const void *block,
                                            const std::string oriCondStr,
                                            const std::string condStr) {
  int bid = BitmapHelper::mcdcBitmapCount;
  BitmapHelper::mcdcBitmapCount++;

  //	AddCodeToCreateNewMCDCLast(flatCode, bid);

  std::string bbStr = GetAddressString(static_cast<const void *>(block));

  BitmapHelper::mcdcIndexMap[bbStr] = bid;
  BitmapHelper::mcdcConditionDescInDecision[bid] = "";
  int condId = 1;
  std::string modifiedExpr =
      HandleLeafConditionExpression(bid, block, oriCondStr, condStr, condId);
  int condNum = condId - 1;
  BitmapHelper::mcdcConditionNumInDecision[bid] = condNum;
  //	std::string rootVarName = "";
  //	GetRootVarName(block, rootVarName);
  //	flatCode += "bool " + rootVarName + " = " + modifiedExpr + ";\n";
  //	flatCode += "BitmapCov::mcdcBitmap[" + std::to_string(bid) + "] |=
  //(((int)" + rootVarName + ") << 0);\n"; 	AddCodeToModifyMCDCLast(flatCode,
  //bid, rootVarName, 0);
  int decid = HandleDecisionCoverage(block, condStr);
  std::string fExpr = "BitmapCov::CondAndMCDCRecord(" + modifiedExpr + ", -" +
                      std::to_string(decid + 1) + ", 0, " +
                      std::to_string(bid) + ")";
  return fExpr;
}*/

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
/*
class MyASTVisitor : public clang::RecursiveASTVisitor<MyASTVisitor> {
public:
  MyASTVisitor(clang::Rewriter &R) : TheRewriter(R) {}

  bool VisitStmt(clang::Stmt *s) {
    // Only care about If statements.
    if (clang::isa<clang::IfStmt>(s)) {
      clang::IfStmt *IfStatement = clang::cast<clang::IfStmt>(s);
      clang::Stmt *Then = IfStatement->getThen();

      TheRewriter.InsertText(Then->getBeginLoc(), "// the 'if' part\n", true,
                             true);

      clang::Stmt *Else = IfStatement->getElse();
      if (Else)
        TheRewriter.InsertText(Else->getBeginLoc(), "// the 'else' part\n",
                               true, true);
    }

    return true;
  }

  bool VisitFunctionDecl(clang::FunctionDecl *f) {
    // Only function definitions (with bodies), not declarations.
    if (f->hasBody()) {
      clang::Stmt *FuncBody = f->getBody();

      // Type name as string
      clang::QualType QT = f->getReturnType();
      std::string TypeStr = QT.getAsString();

      // Function name
      clang::DeclarationName DeclName = f->getNameInfo().getName();
      std::string FuncName = DeclName.getAsString();

      // Add comment before
      std::stringstream SSBefore;
      SSBefore << "// Begin function " << FuncName << " returning " << TypeStr
               << "\n";
      clang::SourceLocation ST = f->getSourceRange().getBegin();
      TheRewriter.InsertText(ST, SSBefore.str(), true, true);

      // And after
      std::stringstream SSAfter;
      SSAfter << "\n// End function " << FuncName;
      ST = FuncBody->getEndLoc().getLocWithOffset(1);
      TheRewriter.InsertText(ST, SSAfter.str(), true, true);
    }

    return true;
  }

private:
  clang::Rewriter &TheRewriter;
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public clang::ASTConsumer {
public:
  MyASTConsumer(clang::Rewriter &R) : Visitor(R) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
  virtual bool HandleTopLevelDecl(clang::DeclGroupRef DR) {
    for (clang::DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b)
      // Traverse the declaration using our AST visitor.
      Visitor.TraverseDecl(*b);
    return true;
  }

private:
  MyASTVisitor Visitor;
};
*/

static llvm::cl::OptionCategory ToolingSampleCategory("Tooling Sample");

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
class MyASTVisitor : public clang::RecursiveASTVisitor<MyASTVisitor> {
public:
  MyASTVisitor(clang::Rewriter &R) : TheRewriter(R) {}

  bool VisitStmt(clang::Stmt *s) {
    // Only care about If statements.
    /*if (clang::isa<clang::IfStmt>(s)) {
      clang::IfStmt *IfStatement = clang::cast<clang::IfStmt>(s);
      clang::Stmt *Then = IfStatement->getThen();
      
      TheRewriter.InsertText(Then->getBeginLoc(), "// the 'if' part\n", true,
                             true);

      clang::Stmt *Else = IfStatement->getElse();
      if (Else)
        TheRewriter.InsertText(Else->getBeginLoc(), "// the 'else' part\n",
                               true, true);
    }*/
    
    // handle exprs: BinaryOperator or ConditionalOperator, there is no need to handle CXXOperatorCallExpr, because CXXOperatorCallExpr is actually call_expr, it must not be primitive a < b. 
    if (clang::isa<clang::BinaryOperator>(s)) {
      clang::BinaryOperator *binaryOp =
          clang::cast<clang::BinaryOperator>(s);
      
      clang::BinaryOperator::Opcode op = binaryOp->getOpcode();

      clang::Expr *lhs = binaryOp->getLHS();
      clang::Expr *rhs = binaryOp->getRHS();

      switch (op) {
        case clang::BinaryOperator::Opcode::BO_LT:// "<"
        case clang::BinaryOperator::Opcode::BO_GT:// ">"
        case clang::BinaryOperator::Opcode::BO_LE:// "<="
        case clang::BinaryOperator::Opcode::BO_GE:// ">="
        case clang::BinaryOperator::Opcode::BO_EQ:// "=="
        case clang::BinaryOperator::Opcode::BO_NE:// "!="
          TheRewriter.InsertText(lhs->getBeginLoc(), "TraceManager::curr->Record(, ",
            true, true);
          TheRewriter.InsertText(lhs->getEndLoc().getLocWithOffset(1),
                                 ", 0)", true, true);
          TheRewriter.InsertText(rhs->getBeginLoc(), "TraceManager::curr->Record(, ",
            true, true);
          TheRewriter.InsertText(rhs->getEndLoc().getLocWithOffset(1),
                                 ", 1)", true, true);
        break;
      }
    }

    // handle stmts: WhileStmt or ForStmt or DoStmt
    clang::Stmt *body = nullptr; 
    if (clang::isa<clang::WhileStmt>(s)) {
      clang::WhileStmt *whileStmt = clang::cast<clang::WhileStmt>(s);
      body = whileStmt->getBody();
    }
    if (clang::isa<clang::ForStmt>(s)) {
      clang::ForStmt *forStmt = clang::cast<clang::ForStmt>(s);
      body = forStmt->getBody();
    }
    if (clang::isa<clang::DoStmt>(s)) {
      clang::DoStmt *doStmt = clang::cast<clang::DoStmt>(s);
      body = doStmt->getBody();
    }
    if (body != nullptr) {
      int id = RegistBitmapIDFromAddress(body, BitmapHelper::blockIndexMap,
                                         BitmapHelper::blockBitmapCount, "");
      if (clang::isa<clang::BlockExpr>(body)) {
        TheRewriter.InsertText(
            body->getBeginLoc(),
            "BlockTracerT btt(" + std::to_string(id) + ");\n", true, true);
      } else {
        TheRewriter.InsertText(
            body->getBeginLoc(),
            "{\nBlockTracerT btt(" + std::to_string(id) + ");\n", true, true);
        TheRewriter.InsertText(body->getEndLoc().getLocWithOffset(1), "}\n",
                               true, true);
      }
    }

    // handle switch: SwitchStmt (only needs to record expr in switch), case values should be stored in other meta structures. 

    return true;
  }

  bool dataTraverseStmtPre(clang::Stmt *s) {
    IsBinCondResult is_bc_res = JudgeIsBinaryBoolCondition(s);
    long long sp = (long long) s;
    bool exist = handledMCDC.find(sp) != handledMCDC.end();
    if (!exist && is_bc_res.is_bc) {
      GenerateMCDCToRootExpression(is_bc_res.binaryOp, TheRewriter);
    }
    return true;
  }

  bool dataTraverseStmtPost(clang::Stmt *s) {
    return true;
  }

  bool VisitFunctionDecl(clang::FunctionDecl *f) {
    // Only function definitions (with bodies), not declarations.
    if (f->hasBody()) {
      clang::Stmt *FuncBody = f->getBody();

      // Type name as string
      clang::QualType QT = f->getReturnType();
      std::string TypeStr = QT.getAsString();

      std::string paramInfo = "";

      int paramSize = f->getNumParams();
      for (int i = 0; i < paramSize; i++) {
        clang::ParmVarDecl* pd = f->getParamDecl(i);

        std::string pdname = pd->getNameAsString();
        clang::QualType tp = pd->getOriginalType();

        paramInfo += std::to_string(i) + "=";

        const clang::Type* tptr = tp.getTypePtr();

        HandleVarType(pdname, tptr, paramInfo);

        paramInfo += "#";
        /*
        clang::QualType actual;

        if (tpPtr->()) {
          actual = tpPtr->getPointeeType();
        }

        if (actual.is()) {
          
        }
        tpPtr->getPointeeCXXRecordDecl();
        */
      }

      // Function name
      clang::DeclarationName DeclName = f->getNameInfo().getName();
      std::string FuncName = DeclName.getAsString();

      // Add comment before
      std::stringstream SSBefore;
      SSBefore << "// Begin function " << FuncName << " returning " << TypeStr
               << "// parameters: " << paramInfo << "\n";
      clang::SourceLocation ST = f->getSourceRange().getBegin();
      TheRewriter.InsertText(ST, SSBefore.str(), true, true);

      // And after
      std::stringstream SSAfter;
      SSAfter << "\n// End function " << FuncName;
      ST = FuncBody->getEndLoc().getLocWithOffset(1);
      TheRewriter.InsertText(ST, SSAfter.str(), true, true);
    }

    return true;
  }

  void HandleVarType(std::string vname, const clang::Type* tp, std::string& info) {
    // const clang::Type *tpPtr = tp.getTypePtr();
    const clang::Type* rtp = tp;
    if (tp->isArrayType() || tp->isAnyPointerType()) {
      rtp = tp->getPointeeOrArrayElementType();
    }
    std::string tpstr = clang::QualType(rtp, 0).getAsString();
    // clang::QualType::getAsString(rtp, 0, clang::PrintingPolicy{{}});
    // clang::TagDecl* td = rtp->getAsTagDecl();
    // std::string tpstr = td->getNameAsString();
    std::string cantype = rtp->getCanonicalTypeInternal().getAsString();
    info += "vname:" + vname + ",ptype:" + tpstr + ",cantype:" + cantype;
    if (rtp->isBuiltinType()) {
      info += ";";
    } else if (rtp->isStructureOrClassType()) {
      clang::CXXRecordDecl *tpCxxRd = rtp->getAsCXXRecordDecl();
      for (clang::RecordDecl::field_iterator jt = tpCxxRd->field_begin();
           jt != tpCxxRd->field_end(); ++jt) {
        std::string fdname = jt->getNameAsString();
        clang::QualType fieldType = jt->getType();
        const clang::Type* fieldtp = fieldType.getTypePtr();
        info += "&{";
        // std::cout << jt->getType().getAsString() << " " << jt->getNameAsString()
        //           << std::endl;
        HandleVarType(fdname, fieldtp, info);
        info += "};";
      }
    } else {
      info += "!warning! not builtin or struct type!";
    }
  }

private:
  clang::Rewriter &TheRewriter;
  std::set<long long> handledMCDC;
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public clang::ASTConsumer {
public:
  MyASTConsumer(clang::Rewriter &R) : Visitor(R) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
  bool HandleTopLevelDecl(clang::DeclGroupRef DR) override {
    for (clang::DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e;
         ++b) {
      // Traverse the declaration using our AST visitor.
      clang::Decl* decl = *b;
      clang::ASTContext& astContext = decl->getASTContext();
      bool isInMain = astContext.getSourceManager().isInMainFile(decl->getBeginLoc());
      if (isInMain) {
        std::cout << "visiting main decl:" << decl->getID() << "\n" << std::endl;
        Visitor.TraverseDecl(decl);
      }
      // (*b)->dump();
    }
    return true;
  }

private:
  MyASTVisitor Visitor;
};

// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public clang::ASTFrontendAction {
public:
  MyFrontendAction() {}
  void EndSourceFileAction() override {
    clang::SourceManager &SM = TheRewriter.getSourceMgr();
    llvm::errs() << "** EndSourceFileAction for: "
                 << SM.getFileEntryForID(SM.getMainFileID())->getName() << "\n";

    // Now emit the rewritten buffer.
    TheRewriter.getEditBuffer(SM.getMainFileID()).write(llvm::outs());
  }

  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &CI,
                    clang::StringRef file) override {
    llvm::errs() << "** Creating AST consumer for: " << file << "\n";
    TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return std::make_unique<MyASTConsumer>(TheRewriter);
  }

private:
  clang::Rewriter TheRewriter;
};

int main(int argc, const char **argv) {
  llvm::Expected<clang::tooling::CommonOptionsParser> &expectedOptionsParser =
      clang::tooling::CommonOptionsParser::create(argc, argv,
                                                  ToolingSampleCategory);
  clang::tooling::CommonOptionsParser & op =
      expectedOptionsParser.get();
  clang::tooling::ClangTool Tool(op.getCompilations(), op.getSourcePathList());
  return Tool.run(
      clang::tooling::newFrontendActionFactory<MyFrontendAction>().get());
}

/*
int main(int argc, char *argv[]) {
  if (argc != 2) {
    llvm::errs() << "Usage: rewritersample <filename>\n";
    return 1;
  }

  // CompilerInstance will hold the instance of the Clang compiler for us,
  // managing the various objects needed to run the compiler.
  CompilerInstance TheCompInst;
  TheCompInst.createDiagnostics();

  LangOptions &lo = TheCompInst.getLangOpts();
  lo.CPlusPlus = 1;

  // Initialize target info with the default triple for our platform.
  auto TO = std::make_shared<TargetOptions>();
  TO->Triple = llvm::sys::getDefaultTargetTriple();
  TargetInfo *TI =
      TargetInfo::CreateTargetInfo(TheCompInst.getDiagnostics(), TO);
  TheCompInst.setTarget(TI);

  TheCompInst.createFileManager();
  FileManager &FileMgr = TheCompInst.getFileManager();
  TheCompInst.createSourceManager(FileMgr);
  SourceManager &SourceMgr = TheCompInst.getSourceManager();
  TheCompInst.createPreprocessor(TU_Module);
  TheCompInst.createASTContext();

  // A Rewriter helps us manage the code rewriting task.
  Rewriter TheRewriter;
  TheRewriter.setSourceMgr(SourceMgr, TheCompInst.getLangOpts());

  // Set the main file handled by the source manager to the input file.
  // const FileEntry *FileIn = FileMgr.getFile(argv[1]);
  const llvm::ErrorOr<const clang::FileEntry *> FileIn =
      FileMgr.getFile(argv[1]);

  SourceMgr.setMainFileID(
      SourceMgr.createFileID(FileIn.get(), SourceLocation(), SrcMgr::C_User));
  TheCompInst.getDiagnosticClient().BeginSourceFile(
      TheCompInst.getLangOpts(), &TheCompInst.getPreprocessor());

  // Create an AST consumer instance which is going to get called by
  // ParseAST.
  MyASTConsumer TheConsumer(TheRewriter);

  // Parse the file to AST, registering our consumer as the AST consumer.
  ParseAST(TheCompInst.getPreprocessor(), &TheConsumer,
           TheCompInst.getASTContext());

  // At this point the rewriter's buffer should be full with the rewritten
  // file contents.
  const RewriteBuffer *RewriteBuf =
      TheRewriter.getRewriteBufferFor(SourceMgr.getMainFileID());
  llvm::outs() << std::string(RewriteBuf->begin(), RewriteBuf->end());

  return 0;
}
*/

/*
class cFindNamedClassVisitor
    : public clang::RecursiveASTVisitor<cFindNamedClassVisitor> {

public:
  explicit cFindNamedClassVisitor(clang::ASTContext *Context)
      : Context(Context) {}

  bool VisitCXXRecordDecl(clang::CXXRecordDecl *Declaration) {
    if (Declaration->getQualifiedNameAsString() == "n::m::C") {
      clang::FullSourceLoc FullLocation =
          Context->getFullLoc(Declaration->getBeginLoc());
      if (FullLocation.isValid())
        llvm::outs() << "Found declaration at "
                     << FullLocation.getSpellingLineNumber() << ":"
                     << FullLocation.getSpellingColumnNumber() << "\n";
    }
    return true;
  }

private:
  clang::ASTContext *Context;
};

class cFindNamedClassConsumer : public clang::ASTConsumer {

public:
  explicit cFindNamedClassConsumer(clang::ASTContext *Context)
      : Visitor(Context) {}

  virtual void HandleTranslationUnit(clang::ASTContext &Context) {
    // Traversing the translation unit decl via a RecursiveASTVisitor
    // will visit all nodes in the AST.
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
  }

private:
  // A RecursiveASTVisitor implementation.
  cFindNamedClassVisitor Visitor;
};

class cFindNamedClassAction : public clang::ASTFrontendAction {

public:
  virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    return std::unique_ptr<clang::ASTConsumer>(
        new cFindNamedClassConsumer(&Compiler.getASTContext()));
  }
};

static llvm::cl::OptionCategory MyToolCategory("my-tool options");

int main(int argc, const char **argv) {
  if (argc > 1) {
//    auto fa = clang::tooling::newFrontendActionFactory<cFindNamedClassAction>().get();
    llvm::Expected<clang::tooling::CommonOptionsParser>& expectedOptionsParser = 
        clang::tooling::CommonOptionsParser::create(argc, argv, MyToolCategory);
    clang::tooling::CommonOptionsParser& OptionsParser = expectedOptionsParser.get();
    // clang::tooling::CommonOptionsParser OptionsParser(argc, argv, MyToolCategory);
    clang::tooling::ClangTool Tool(OptionsParser.getCompilations(),
                                   OptionsParser.getSourcePathList());
    int result = Tool.run(
        clang::tooling::newFrontendActionFactory<cFindNamedClassAction>()
            .get());
    return result;
    // const std::unique_ptr<clang::FrontendAction> fa =
    //     std::unique_ptr<clang::ASTFrontendAction>(new cFindNamedClassAction());
    // clang::tooling::runToolOnCode(fa, argv[1]);
    // return 1;
  }
}
*/



