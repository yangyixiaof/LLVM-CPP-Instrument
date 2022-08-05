LLVM_14.0 CPP source code level instrumentation, the files in this repo should be put in llvm-project-llvmorg-14.0.0/clang-tools-extra/yyx-cast. 

The yyx-cast is the self-created directory. 

Remeber: at the end of ....../clang-tools-extra/CMakeLists.txt, add the code in the following double quotes: 
"add_subdirectory(yyx-cast)" 

This project can run on Windows in a stand alone way. This project is not depend on LLVM Pass which can only run on Linux. 

The instrumentation can insert code before or after some AST node or get the origin code corresponding to some AST node. 

I use cmake to generate visual studio project. 
In root llvm project directory, create new directory named "build". 
cd into build, and type the following command:


cmake -G "Visual Studio 16 2019" -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra;" -A x64 -Thost=x64 ..\llvm


Then, open .sln, in many projects of llvm, find sub-project yyx-cast, you can directly run yyx-cast as a stand alone application in visual studio. 

In LLVM_14.0 or later, on Windows platform, some files in other projects in whole llvm project have compilation errors. 
You should fix those errors mannually. 
The errors are mainly encoding errors or some files containing strange characters. 
If those files are unit-test files, just delete the code lines containing the unrecognized charaters. 

