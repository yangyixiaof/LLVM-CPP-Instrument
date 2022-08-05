set(LLVM_LINK_COMPONENTS support)

add_clang_executable(yyx-cast
  CondInstrument.cpp
#  MyDiagnosticConsumer.cpp
#  CInfoUtil.cpp
#  CInfoMatcher.cpp
#  CEntityDeal.cpp
#  parserInitExpr.cpp
#  tinyxml/src/tinyxml/tinystr.cpp
#  tinyxml/src/tinyxml/tinyxml.cpp
#  tinyxml/src/tinyxml/tinyxmlerror.cpp
#  tinyxml/src/tinyxml/tinyxmlparser.cpp
  )

target_link_libraries(yyx-cast
  PRIVATE
  clangTooling
  clangBasic
  clangASTMatchers
  clangAST
  LLVMSupport
  clangFrontend
  )
