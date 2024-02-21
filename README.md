## ParDiff

ParDiff is the implementation for our paper published in OOPSLA 2024:
 ParDiff: Practical Static Differential Analysis of Network Protocol Parsers
It aims to find logical bugs in network protocol implementations using static differential analysis. 

To use ParDiff, please prepare bitcode for two implementations under comparison:  target1.bc and target2.bc. Here we provide an example under pardiff/test.

## Build

Compiler
* gcc-11.2.0

Dependency:
* llvm-12.0.1
* z3-4.8.12 better use our copy

```bash
$  mkdir  build
$  cd  build
$  cmake  ..
$  make -j8
```

## Run with our example

```bash

./bin/pardiff ../test/target1.bc ../test/target2.bc -pardiff-entry=pardiff_main_message > diff.txt 2>&1