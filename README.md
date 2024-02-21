## ParDiff

ParDiff is the implementation for our paper published in OOPSLA 2024:
  
 ```
ParDiff: Practical Static Differential Analysis of Network Protocol Parsers
Mingwei Zheng, Qingkai Shi, Xuwei Liu, Xiangzhe Xu, Le Yu, Congyu Liu, Guannan Wei, Xiangyu Zhang
ACM SIGPLAN International Conference on Object-Oriented Programming Systems, Languages, and Applications (OOPSLA '24) 
```
It aims to find logical bugs in network protocol implementations using static differential analysis. 

## Input
To use ParDiff, please prepare bitcode for two implementations under comparison:  target1.bc and target2.bc. Here we provide an example under pardiff/tests.

To create your own test cases, please follow the steps below to get bitcode as input:

* The source code must be implemented in C and can be compiled using clang-12 and wllvm.
* Annotate the entry parsing function in the source code using the interfaces we provide below:
```
  void * pardiff_make_object(unsigned size);
  // This interface works as the C lib interface, malloc(), which allocates space in memory with a given size. 
  void * pardiff_make_message();
  // This interface creates a buffer of the networking data.
  unsigned pardiff_make_message_length();
  // This interface indicates the length of the input networking data
```
Here is an example how we do annotations on the [FRR/babeld parser](https://github.com/FRRouting/frr/blob/master/babeld/message.c#L402):
```bash
#include <stdint.h>
#include <stdio.h>
#include "config.h"
#include <stdlib.h>
#include "message.h"

void *pardiff_make_object(uint64_t size);

void *pardiff_make_message(void);

int pardiff_make_message_length(void);

int pardiff_main_message(){
    unsigned char *from = pardiff_make_object(sizeof(char));
    struct interface *ifp = pardiff_make_object(sizeof(struct interface));
    unsigned char *packet = pardiff_make_message();
    int len = pardiff_make_message_length();
    parse_packet(from, ifp,packet, len); 
    return 0; 
}
```
* After finishing the annotation, use Clang-12 and WLLVM to compile the software project and get a bitcode. See [WLLVM](https://github.com/travitch/whole-program-llvm) for more details on how to get a bitcode.

## Build

Compiler
* gcc-11.2.0

Dependency:
* llvm-12.0.1
* z3-4.8.12 better use our copy: [z3](https://github.com/zmw12306/z3) need to compile and install using cmake

```bash
$  mkdir  build
$  cd  build
$  cmake  ..
$  make -j8
```

## Run with our example

```bash

./bin/pardiff ../tests/target1.bc ../tests/target2.bc -pardiff-entry=pardiff_main_message > diff.txt 2>&1
