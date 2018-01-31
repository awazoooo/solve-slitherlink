#!/usr/bin/env python
# -*- coding: utf-8 -*-
### ./solve-slitherlink.py (option) puzzle.txt とすると、パズルの結果をわかりやすく表示

import sys
import os

# 引数の個数
argc = len(sys.argv)
puzzle = None
option = None

# 引数が多かったり少なかったり
if argc not in range(2,4):
    if argc < 2:
        sys.stderr.write("more arguments are expected...\n")
    else:
    	sys.stderr.write("few arguments are expected...\n")
    sys.exit(1)
else:
    # optionなし
    if argc == 2:
        puzzle = sys.argv[1]
    # optionあり
    else:
        puzzle = sys.argv[2]
        option = sys.argv[1]

solve = "./assertmaker-slitherlink.py "        

if option is not None:
    solve += option + " " + puzzle
else:
    solve += puzzle

smt = "z3 output.rs > shelloutput"
shape = "./shape-slitherlink.py " + puzzle 

os.system(solve)
os.system(smt)
os.system(shape)
os.unlink("shelloutput")
os.unlink("output.rs")
os.unlink("info.txt")
