#!/usr/bin/env python
# -*- coding: utf-8 -*-
### 元のパズルを引数にとって，見やすく出力.

import sys
import math

# z3の出力
res = open("shelloutput",'r')

# Puzzleのサイズ(info.txtに記載)
tempSize = open("info.txt",'r')
size = tempSize.readline()
size = size.replace("puzzlesize=","")
size = size.split(",")
PUZZLESIZEI = int(size[0])
PUZZLESIZEJ = int(size[1])
tempSize.close()

# 元のパズル
originalPuzzle = open(sys.argv[1],'r')
# パズルの読み込み
puzzle = []
for line in originalPuzzle.readlines():
    for cell in line:
        if cell == '\n':
            continue
        else:
            puzzle.append(str(cell))
            
originalPuzzle.close()

# ノードの数
NODESIZEI = PUZZLESIZEI + 1
NODESIZEJ = PUZZLESIZEJ + 1
# 求まった解(ディクショナリ)
# (Int,Int)がキー,[h,v]が値
ansdict = {}
for i in range(NODESIZEI):
    for j in range(NODESIZEJ):
        ansdict[(i,j)] = [None,None]

line = res.readline()

# satかunsatかどうか -> とりあえずエラー処理は強制終了
if line.strip() == "unsat":
    print("This puzzle is unsat.")
    sys.exit()
elif line.strip() != "sat":
    print("input error")
    sys.exit()

# values といった文字が出るまで捨てる
while True:
    if res.readline().rstrip() == "values":
        break

# Z3の結果の読み取り部分
for i in range(2*NODESIZEI*NODESIZEJ - NODESIZEI - NODESIZEJ):
    line = res.readline().rstrip()
    line = line.replace("(","")
    line = line.replace(")","")
    line = line.split(" ")

    # 変数名
    name = line[0]

    # 値(Int)->- 1の場合もあるのでsplit
    value = None
    if len(line) < 3:
        value = line[1]
    else:
        value = "-" + line[2]

    # 変数名がvかhか
    direction = name[0]

    # ノード番号((行番号,列番号)のタプル)
    # (Int,Int)
    nodeKey = name[1:]

    keyList = nodeKey.split("_")
    index = (int(keyList[0]),int(keyList[1]))
    
    # 変換した出力を辞書に登録(h,v)-->未完
    if direction == "h":
        ansdict[index][0] = value
    elif direction == "v":
        ansdict[index][1] = value

res.close()        

# 奇数行の出力
def oddLineFormat(i):
    s = "+"
    for j in range(PUZZLESIZEJ):
        if ansdict[(i,j)][0] is None:
            s += "\n"
            return s
        elif (int)(ansdict[(i,j)][0]) == 0:
            s += "     +"
        else:
            s += "-----+"
    return s

# 偶数行の出力
def evenLineFormat(i):
    s = ""
    for j in range(PUZZLESIZEJ):
        if ansdict[(i,j)][1] is None:
            return ""
        elif (int)(ansdict[(i,j)][1]) == 0:
            s += "   "
            cell = puzzle[i*PUZZLESIZEJ+j]
            if cell == "E":
                s += "   "
            else:
                s += str(cell) + "  "
        else:
            s += "|  "
            cell = puzzle[i*PUZZLESIZEJ+j]
            if cell == "E":
                s += "   "
            else:
                s += str(cell) + "  "

    if (int)(ansdict[(i,PUZZLESIZEJ)][1]) == 0:
        s += " \n"
    else:
        s += "|\n"
    return s


# わかりやすく出力.
outputStr = ""
for i in range(PUZZLESIZEI+1):
    outputStr += oddLineFormat(i)
    outputStr += "\n"
    outputStr += evenLineFormat(i)

print outputStr

