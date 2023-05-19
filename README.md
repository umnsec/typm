# TyPM: Type-based dependence analysis for program modularization

This is a prototype implementation of "type-based dependence
analysis" which is to determine which modules may pass a given type
of data to a target module. Unlike traditional dependence analysis
that uses data-flow analysis, TyPM uses type analysis, so is
highly scalable. A key observation is that a module can pass data to
another module through only two channels: global variable and
function argument. Both channels come with types; therefore, by
inspecting the global variables and function calls, we can identify
potential types of data flows between two modules, without tracking
into the internal data flows. This implementation also includes
techniques such as type recovery, typecasting analysis, type
elevation, indirect-call target resolving, etc. It also includes the
application of using TyPM to achieve scope-aware type matching for
indirect-call targets.

This implementation uses LLVM without opaque pointers---LLVM 15
(commit e758b77161a7). It has been tested with the O2 optimization
level. Note that there are a few false negatives observed, mainly
caused by hacky coding styles, LLVM type issues, and implementation
bugs. 


## How to use TyPM

### Build LLVM 
```sh 
	$ ./build-llvm.sh 
	# The tested LLVM is of commit e758b77161a7 
```

### Build TyPM 
```sh 
	# Build the analysis pass 
	# First update Makefile to make sure the path to the built LLVM is correct
	$ make 
	# Now, you can find the executable, `kanalyzer`, in `build/lib/`
```
 
### Prepare LLVM bitcode files of target programs

Please refer to https://github.com/umnsec/mlta

### Run TyPM
```sh
	# To analyze a list of bitcode files, put the absolute paths of the bitcode files in a file, say "bc.list", then run:
	$ ./build/lib/kalalyzer @bc.list
	# Results will be printed out`.
```

```sh
	# Options
	$ ./build/lib/kalalyzer
	# Note that, by default, the function-type matching is used as
	# the base, not MLTA 
```

### Configurations

Config options can be found in `Config.h`


## More details

[The TyPM paper (IEEE S&P'23)](https://www-users.cse.umn.edu/~kjlu/papers/typm.pdf)
```sh
@inproceedings{typm-sp23,
  title        = {{Practical Program Modularization with Type-Based Dependence Analysis}},
  author       = {Kangjie Lu},
  booktitle    = {Proceedings of the 44th IEEE Symposium on Security and Privacy (S\&P'23)},
  month        = May,
  year         = 2023,
  address      = {San Francisco, CA},
}
```
