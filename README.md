# Lamai

![lama](https://raw.githubusercontent.com/PLTools/Lama/be0b32f7b9c75e61eff377cd34d4f65ebeeca204/lama.svg) is a programming language developed by JetBrains Research for educational purposes as an exemplary language to introduce the domain of programming languages, compilers, and tools. (https://github.com/PLTools/Lama)  
Lamai is just an iterative interpreter of the Lama stack machine bytecode.  
## Usage
Lamai does not support any flags, only one argument - path to file with the Lama stack machine bytecode (`.bc` extension)
```console
~/lamai$ lamac -b test.lama 
~/lamai$ ./lamai test.bc
```
