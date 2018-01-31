#!/usr/bin/env python
# -*- coding: utf-8 -*-

### z3のスリザーリンク解法のための制約を記述
# option
# -0:全てのゼロの周りには線が存在しない制約を追加
# -3:全ての3のセルに接する線が存在する場合は、その線が接する点の対角にある点からセルに沿った線が引けるという制約を追加
# -a:-3が有効になっている時に用いる. -3の制約に加えて、対角にある点からは引いた線以外の線が接することはないという制約を追加->発表では3a制約を3'制約とした
# -o:-0が有効になっている時に用いる. -0の制約に加えて、端または角の0においては、もっと制約を追加->発表では0o制約を0'制約とした

import sys
import math

class SolverMaker:

    def template(self):
        ## お決まり文句を出力
        self.output.write(";;;written in program.\n\n")

        # smtの初期設定
        self.output.write(";settings\n")
        self.output.write("(set-option :produce-models true)\n\n")

    def vName(self,i,j):
        ## i_jを返すだけだが、便利なので作っておく
        return str(i) + "_" + str(j)

        
    def vdeclare(self):
        ## 変数の宣言部
        self.output.write(";declaring variables\n\n")
        
        # 2x2のパズルの時，変数のリスト(self.variablesList)は
        # [['v0_0','h0_0'],['v0_1'],
        # ['h1_0'],[]]となる．
        for i in range(self.NODESIZEI):
            for j in range(self.NODESIZEJ):
                vBase = self.vName(i,j)
                variableName = []
                if j != self.PUZZLESIZEJ:
                    hVal = "h" + vBase
                    variableName.append(hVal)
                    self.output.write("(declare-const {0} Int)\n".format(hVal))
                if i != self.PUZZLESIZEI:
                    vVal = "v" + vBase
                    variableName.append("v" + vBase)
                    self.output.write("(declare-const {0} Int)\n".format(vVal))
                self.variablesList.append(variableName)

        # 変数のリストをフラットに
        self.flattenVariablesList = self.flatten(self.variablesList)

        # 次数変数の宣言
        for i in range(self.NODESIZEI):
            for j in range(self.NODESIZEJ):
                vBase = self.vName(i,j)
                variableName = "d" + vBase
                self.degreeVariablesList.append(variableName)
                self.output.write("(declare-const {0} Int)\n".format(variableName))

        # 経路変数(route)
        for i in range(self.NODESIZEI):
            for j in range(self.NODESIZEJ):
                vBase = self.vName(i,j)
                variableName = "r" + vBase
                self.routeVariablesList.append(variableName)
                self.output.write("(declare-const {0} Int)\n".format(variableName))
                
        # 始点(かどうか判断する)変数(startpoint)
        for i in range(self.NODESIZEI):
            for j in range(self.NODESIZEJ):
                vBase = self.vName(i,j)
                variableName = "s" + vBase
                self.startVariablesList.append(variableName)
                self.output.write("(declare-const {0} Int)\n".format(variableName))


    def setEdgeVarDomain(self):
        ## 辺変数のdomainを定義
        self.output.write("\n\n;setting edge variables domain\n\n")
        # 変数は0,-1,1のどれか
        for edgeList in self.variablesList:
            for edge in edgeList:
                self.output.write("(assert (and (<= -1 {0}) (<= {0} 1)))\n".format(edge))

                
    def setInitValues(self):
        ## パズルの初期値による制約
        self.output.write("\n\n;setting initialize values\n\n")
        for i in range(self.PUZZLESIZEI):
            for j in range(self.PUZZLESIZEJ):
                cell = self.convertedPuzzle[self.PUZZLESIZEJ*i + j]
                if cell == -1:
                    continue
                # cellの数字が0の時はoptionによっては別の制約の与え方となる
                elif (cell == 0) and (self.option is not None) and ("0" in self.option):
                    self.zeroRule(i,j)
                    continue

                edgeList = []
                edgeList.append("h" + self.vName(i,j))
                edgeList.append("v" + self.vName(i,j))
                edgeList.append("h" + self.vName(i+1,j))
                edgeList.append("v" + self.vName(i,j+1))

                s = "(assert (= (+ (abs {0}) (abs {1}) (abs {2}) (abs {3})) {4}))\n"
                self.output.write(s.format(edgeList[0],edgeList[1],edgeList[2],edgeList[3],cell))

                
    def setDegreeVarDomain(self):
        ## 次数変数のdomainを定義
        self.output.write("\n\n;setting degree variables domain\n\n")
        for degree in self.degreeVariablesList:
            self.output.write("(assert (or (= {0} 0) (= {0} 2)))\n".format(degree))


    def crossConstraint(self):
        ## パズルの解に分岐や交差部分が無いようにする制約
        self.output.write("\n\n;there are no diverge and no intersection in each node\n\n")
        for i in range(self.NODESIZEI):
            for j in range(self.NODESIZEJ):
                if i == 0:
                    if j == 0:
                        s = "(assert (= {0} (+ (abs {1}) (abs {2}))))\n"
                        self.output.write(s.format(self.degreeVariablesList[self.NODESIZEJ*i + j],"h" + self.vName(i,j),"v" + self.vName(i,j)))
                        
                        s = "(assert (= (+ (- {0}) (- {1})) 0))\n"
                        self.output.write(s.format("h" + self.vName(i,j),"v" + self.vName(i,j)))
                        
                    elif j == self.PUZZLESIZEJ:
                        s = "(assert (= {0} (+ (abs {1}) (abs {2}))))\n"
                        self.output.write(s.format(self.degreeVariablesList[self.NODESIZEJ*i + j],"h" + self.vName(i,j-1),"v" + self.vName(i,j)))
                        
                        s = "(assert (= (+ {0} (- {1})) 0))\n"
                        self.output.write(s.format("h" + self.vName(i,j-1),"v" + self.vName(i,j)))                        
                        
                    else:
                        s = "(assert (= {0} (+ (abs {1}) (abs {2}) (abs {3}))))\n"
                        self.output.write(s.format(self.degreeVariablesList[self.NODESIZEJ*i + j],"h" + self.vName(i,j),"v" + self.vName(i,j),"h" + self.vName(i,j-1)))

                        s = "(assert (= (+ (- {0}) (- {1}) {2}) 0))\n"
                        self.output.write(s.format("h" + self.vName(i,j),"v" + self.vName(i,j),"h" + self.vName(i,j-1)))                                                

                elif j == 0:
                    if i == self.PUZZLESIZEI:
                        s = "(assert (= {0} (+ (abs {1}) (abs {2}))))\n"
                        self.output.write(s.format(self.degreeVariablesList[self.NODESIZEJ*i + j],"h" + self.vName(i,j),"v" + self.vName(i-1,j)))

                        s = "(assert (= (+ (- {0}) {1}) 0))\n"
                        self.output.write(s.format("h" + self.vName(i,j),"v" + self.vName(i-1,j)))                                                
                        
                    else:
                        s = "(assert (= {0} (+ (abs {1}) (abs {2}) (abs {3}))))\n"
                        self.output.write(s.format(self.degreeVariablesList[self.NODESIZEJ*i + j],"h" + self.vName(i,j),"v" + self.vName(i,j),"v" + self.vName(i-1,j)))

                        s = "(assert (= (+ (- {0}) (- {1}) {2}) 0))\n"
                        self.output.write(s.format("h" + self.vName(i,j),"v" + self.vName(i,j),"v" + self.vName(i-1,j)))                                                                        

                elif i == self.PUZZLESIZEI:
                    # print "(i,j) = " + "(" + str(i) + "," + str(j) + ")"
                    if j == self.PUZZLESIZEJ:
                        s = "(assert (= {0} (+ (abs {1}) (abs {2}))))\n"
                        self.output.write(s.format(self.degreeVariablesList[self.NODESIZEJ*i + j],"h" + self.vName(i,j-1),"v" + self.vName(i-1,j)))

                        s = "(assert (= (+ {0} {1}) 0))\n"
                        self.output.write(s.format("h" + self.vName(i,j-1),"v" + self.vName(i-1,j)))

                    else:
                        s = "(assert (= {0} (+ (abs {1}) (abs {2}) (abs {3}))))\n"
                        self.output.write(s.format(self.degreeVariablesList[self.NODESIZEJ*i + j],"h" + self.vName(i,j),"v" + self.vName(i-1,j),"h" + self.vName(i,j-1)))

                        s = "(assert (= (+ (- {0}) {1} {2}) 0))\n"
                        self.output.write(s.format("h" + self.vName(i,j),"v" + self.vName(i-1,j),"h" + self.vName(i,j-1)))                                                                        

                        
                elif j == self.PUZZLESIZEJ:
                    s = "(assert (= {0} (+ (abs {1}) (abs {2}) (abs {3}))))\n"
                    self.output.write(s.format(self.degreeVariablesList[self.NODESIZEJ*i + j],"v" + self.vName(i,j),"h" + self.vName(i,j-1),"v" + self.vName(i-1,j)))

                    s = "(assert (= (+ (- {0}) {1} {2}) 0))\n"
                    self.output.write(s.format("v" + self.vName(i,j),"h" + self.vName(i,j-1),"v" + self.vName(i-1,j)))                    

                else:
                    s = "(assert (= {0} (+ (abs {1}) (abs {2}) (abs {3}) (abs {4}))))\n"
                    self.output.write(s.format(self.degreeVariablesList[self.NODESIZEJ*i + j],"h" + self.vName(i,j),"v" + self.vName(i,j),"h" + self.vName(i,j-1),"v" + self.vName(i-1,j)))

                    s = "(assert (= (+ (- {0}) (- {1}) {2} {3}) 0))\n"
                    self.output.write(s.format("h" + self.vName(i,j),"v" + self.vName(i,j),"h" + self.vName(i,j-1),"v" + self.vName(i-1,j)))


    def setRouteVarDomain(self):
        ## 経路変数のdomainを定義
        self.output.write("\n\n;setting route variables domain\n\n")
        for routeNum in self.routeVariablesList:
            self.output.write("(assert (and (<= 0 {0}) (< {0} {1})))\n".format(routeNum,self.NODESIZEI*self.NODESIZEJ))
            
            
    def setStartVarDomain(self):
        ## 始点変数のdomainを定義
        self.output.write("\n\n;setting start variables domain\n\n")
        for s in self.startVariablesList:
            self.output.write("(assert (or (= {0} 0) (= {0} 1)))\n".format(s))

            
    def oneLoop(self):
        ## ループ(輪っか)がただ一つである、という制約
        # 必要な変数宣言
        self.setRouteVarDomain()
        self.setStartVarDomain()

        # iffの条件
        self.output.write("\n\n;setting route and startpoint constraint\n\n")
        for i in range(self.NODESIZEI):
            for j in range(self.NODESIZEJ):
                vbase = self.vName(i,j)
                s1 = "(assert (iff (> {0} 0) (> {1} 0)))\n"
                s2 = "(assert (iff (= {0} 1) (= {1} 1)))\n"
                self.output.write(s1.format("d" + vbase,"r" + vbase))
                self.output.write(s2.format("r" + vbase,"s" + vbase))

        # 始点の内、1になるのは1つのみ
        self.output.write("\n\n;only one startpoint is tagged 1\n")
        formatStr = ""
        for s in self.startVariablesList:
            formatStr += s
            formatStr += " "
        self.output.write("(assert (= (+ {0}) 1))\n".format(formatStr))
        self.setLoopNo()

        
    def setLoopNo(self):
        ## 各nodeへ入出するlineの制約
        self.output.write("\n\n;node number constraint for each node\n\n")
        s = "(assert (=> ({0} {1} 0) (or (> {2} {3}) (= {2} 1))))\n"
        for i in range(self.NODESIZEI):
            for j in range(self.NODESIZEJ):
                name = "h" + self.vName(i,j+1)
                if name in self.flattenVariablesList:
                    # nodeの右のline
                    self.output.write(s.format(">","h" + self.vName(i,j),"r" + self.vName(i,j+1),"r" + self.vName(i,j)))
                    self.output.write(s.format("<","h" + self.vName(i,j),"r" + self.vName(i,j),"r" + self.vName(i,j+1)))

                name = "v" + self.vName(i+1,j)
                if name in self.flattenVariablesList:
                    # nodeの下のline
                    self.output.write(s.format(">","v" + self.vName(i,j),"r" + self.vName(i+1,j),"r" + self.vName(i,j)))
                    self.output.write(s.format("<","v" + self.vName(i,j),"r" + self.vName(i,j),"r" + self.vName(i+1,j)))

                name = "h" + self.vName(i,j-1)
                if name in self.flattenVariablesList:
                    # nodeの左のline
                    self.output.write(s.format("<","h" + self.vName(i,j-1),"r" + self.vName(i,j-1),"r" + self.vName(i,j)))
                    self.output.write(s.format(">","h" + self.vName(i,j-1),"r" + self.vName(i,j),"r" + self.vName(i,j-1)))

                name = "v" + self.vName(i-1,j)
                if name in self.flattenVariablesList:
                    # nodeの上のline
                    self.output.write(s.format("<","v" + self.vName(i-1,j),"r" + self.vName(i-1,j),"r" + self.vName(i,j)))
                    self.output.write(s.format(">","v" + self.vName(i-1,j),"r" + self.vName(i,j),"r" + self.vName(i-1,j)))


                    
    def rule(self):
        ## パズルを解くために最低限の制約
        self.setEdgeVarDomain()
        self.setInitValues()
        self.setDegreeVarDomain()
        self.crossConstraint()
        self.oneLoop()
        # 3制約
        if (self.option is not None) and ("3" in self.option):
            self.edgeLineRule3()

            
    def zeroRule(self,i,j):
        ## ->0の周りにlineは無いというルール
        # optionで -0(ゼロ)を指定した時にsetInitValues()から呼ばれる
        self.output.write("\n;this is around zero rule\n")
        
        s = "(assert (and {0}))\n"
        aroundLineList = []
        aroundLineList.append("h" + self.vName(i,j))
        aroundLineList.append("h" + self.vName(i+1,j))
        aroundLineList.append("v" + self.vName(i,j))
        aroundLineList.append("v" + self.vName(i,j+1))
        
        # -o(英語小文字のオー)で指定した時のみ
        # 0のセルが端や角にあるときはもっと線が引けない場所を決められる
        if "o" in self.option:
            # 左が存在しないとき
            if ("h" + self.vName(i,j-1)) not in self.flattenVariablesList:
                # 上も存在しない時
                if ("v" + self.vName(i-1,j)) not in self.flattenVariablesList:
                    aroundLineList.append("h" + self.vName(i,j+1))
                    aroundLineList.append("v" + self.vName(i+1,j))
                # 下も存在しない時
                elif ("v" + self.vName(i+1,j)) not in self.flattenVariablesList:
                    aroundLineList.append("h" + self.vName(i+1,j+1))
                    aroundLineList.append("v" + self.vName(i-1,j))
                else:
                    aroundLineList.append("v" + self.vName(i-1,j))
                    aroundLineList.append("v" + self.vName(i+1,j))
                    
            # 上が存在しない時
            elif ("v" + self.vName(i-1,j)) not in self.flattenVariablesList:
                # 右も存在しない時
                if ("h" + self.vName(i,j+1)) not in self.flattenVariablesList:
                    aroundLineList.append("h" + self.vName(i,j-1))
                    aroundLineList.append("v" + self.vName(i+1,j+1))
                else:
                    aroundLineList.append("h" + self.vName(i,j-1))
                    aroundLineList.append("h" + self.vName(i,j+1))
                    
            # 右が存在しない時
            elif ("h" + self.vName(i,j+1)) not in self.flattenVariablesList:
                # 下も存在しない時
                if ("v" + self.vName(i+1,j)) not in self.flattenVariablesList:
                    aroundLineList.append("h" + self.vName(i+1,j-1))
                    aroundLineList.append("v" + self.vName(i-1,j+1))
                else:
                    aroundLineList.append("v" + self.vName(i-1,j+1))
                    aroundLineList.append("v" + self.vName(i+1,j+1))
                    
            # 下が存在しない時
            elif ("v" + self.vName(i+1,j)) not in self.flattenVariablesList:
                aroundLineList.append("h" + self.vName(i+1,j-1))
                aroundLineList.append("h" + self.vName(i+1,j+1))

        zeroStr = "(= {0} 0)"
        andStr = ""
        for line in aroundLineList:
            andStr += zeroStr.format(line) + " "
        self.output.write(s.format(andStr))
        self.output.write("\n")


    def edgeLineRule3(self):
        ## あるセルの角に隣接する線が引けるとき、そのセルの数字によって与えられる制約->完成?
        # optionで -3 を指定した時に有効(呼ばれる)
        self.output.write("\n\n;setting around three rule\n")
        # この場合はセルの数字が3の時
        for i in range(self.PUZZLESIZEI):
            for j in range(self.PUZZLESIZEJ):
                # とりあえずセルの数字が3の時のみを考える
                if not (self.convertedPuzzle[self.PUZZLESIZEJ*i+j] == 3):
                    continue

                # 3のセルの周りに引ける線
                s = "(assert (=> (= (abs {0}) 1) (and (= (abs {1}) 1) (= (abs {2}) 1))))\n"
                # 3のセルの周りに引いた線による引けない位置の線
                s2 = "(assert (=> (= (abs {0}) 1) (= {1} 0)))\n"
                
                # 上が存在する場合
                if ("v" + self.vName(i-1,j)) in self.flattenVariablesList:
                    # 左上の点にその上から線が存在する場合、セルに対してその対角にある点には、その点を点とする線が、セルに沿って2本存在する
                    vlist = []
                    vlist.append("v" + self.vName(i-1,j))
                    vlist.append("h" + self.vName(i+1,j))
                    vlist.append("v" + self.vName(i,j+1))
                    self.output.write(s.format(vlist[0],vlist[1],vlist[2]))
                    if "a" in self.option:
                        # 3のセルの周りに2本の線を引けた場合、その線が出る点の残りの辺に線は引かれない
                        # この場合は、点(i+1,j+1)から出る右方向と下方向の辺は引かれないことになる(存在すれば)
                        hname = "h" + self.vName(i+1,j+1)
                        vname = "v" + self.vName(i+1,j+1)
                        # 右方向の変数が存在
                        if hname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],hname))
                        # 下方向の変数が存在
                        if vname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],vname))
                    
                    # 右上の点について...
                    vlist = []
                    vlist.append("v" + self.vName(i-1,j+1))
                    vlist.append("h" + self.vName(i+1,j))
                    vlist.append("v" + self.vName(i,j))
                    self.output.write(s.format(vlist[0],vlist[1],vlist[2]))
                    if "a" in self.option:
                        hname = "h" + self.vName(i+1,j-1)
                        vname = "v" + self.vName(i+1,j)
                        # 左方向の変数が存在
                        if hname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],hname))
                        # 下方向の変数が存在
                        if vname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],vname))                        
                    
                # 左が存在する場合
                if ("h" + self.vName(i,j-1)) in self.flattenVariablesList:
                    # 左上の点について...
                    vlist = []
                    vlist.append("h" + self.vName(i,j-1))
                    vlist.append("h" + self.vName(i+1,j))
                    vlist.append("v" + self.vName(i,j+1))
                    self.output.write(s.format(vlist[0],vlist[1],vlist[2]))
                    if "a" in self.option:
                        hname = "h" + self.vName(i+1,j+1)
                        vname = "v" + self.vName(i+1,j+1)
                        # 右方向の変数が存在
                        if hname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],hname))
                        # 下方向の変数が存在
                        if vname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],vname))                                            

                    # 左下の点について...
                    vlist = []
                    vlist.append("h" + self.vName(i+1,j-1))
                    vlist.append("h" + self.vName(i,j))
                    vlist.append("v" + self.vName(i,j+1))
                    self.output.write(s.format(vlist[0],vlist[1],vlist[2]))
                    if "a" in self.option:
                        hname = "h" + self.vName(i,j+1)
                        vname = "v" + self.vName(i-1,j+1)
                        # 右方向の変数が存在
                        if hname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],hname))
                        # 上方向の変数が存在
                        if vname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],vname))                               
                    
                # 下が存在する場合
                if ("v" + self.vName(i+1,j)) in self.flattenVariablesList:
                    # 左下の点について...
                    vlist = []
                    vlist.append("v" + self.vName(i+1,j))
                    vlist.append("h" + self.vName(i,j))
                    vlist.append("v" + self.vName(i,j+1))
                    self.output.write(s.format(vlist[0],vlist[1],vlist[2]))
                    if "a" in self.option:
                        hname = "h" + self.vName(i,j+1)
                        vname = "v" + self.vName(i-1,j+1)
                        # 右方向の変数が存在
                        if hname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],hname))
                        # 上方向の変数が存在
                        if vname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],vname))                               
                    
                    # 右下の点について...
                    vlist = []
                    vlist.append("v" + self.vName(i+1,j+1))
                    vlist.append("h" + self.vName(i,j))
                    vlist.append("v" + self.vName(i,j))
                    self.output.write(s.format(vlist[0],vlist[1],vlist[2]))
                    if "a" in self.option:
                        hname = "h" + self.vName(i,j-1)
                        vname = "v" + self.vName(i-1,j)
                        # 左方向の変数が存在
                        if hname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],hname))
                        # 上方向の変数が存在
                        if vname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],vname))                            
                    
                # 右が存在する場合
                if ("h" + self.vName(i,j+1)) in self.flattenVariablesList:
                    # 右上の点について...
                    vlist = []
                    vlist.append("h" + self.vName(i,j+1))
                    vlist.append("h" + self.vName(i+1,j))
                    vlist.append("v" + self.vName(i,j))
                    self.output.write(s.format(vlist[0],vlist[1],vlist[2]))
                    if "a" in self.option:
                        hname = "h" + self.vName(i+1,j-1)
                        vname = "v" + self.vName(i+1,j)
                        # 左方向の変数が存在
                        if hname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],hname))
                        # 下方向の変数が存在
                        if vname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],vname))
                            
                    # 右下の点について...
                    vlist = []
                    vlist.append("h" + self.vName(i+1,j+1))
                    vlist.append("h" + self.vName(i,j))
                    vlist.append("v" + self.vName(i,j))
                    self.output.write(s.format(vlist[0],vlist[1],vlist[2]))
                    if "a" in self.option:
                        hname = "h" + self.vName(i,j-1)
                        vname = "v" + self.vName(i-1,j)
                        # 左方向の変数が存在
                        if hname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],hname))
                        # 上方向の変数が存在
                        if vname in self.flattenVariablesList:
                            self.output.write(s2.format(vlist[0],vname))                                
                    

    def end(self):
        ## satかunsatか
        self.output.write("\n(check-sat)\n")
        self.output.write("(get-model)\n")
        self.output.write('(echo "values")\n')
        # get-value() in all vartical and horizonal variables
        for l in self.variablesList:
            for vName in l:
                self.output.write("(get-value ({0}))\n".format(vName))
                
        self.output.close()
        # z3形式の出力ファイルの先頭にPUZZLESIZEを記述
        # n x mのサイズだったら先頭にn,mを追加
        f = open("info.txt","w")
        f.write("puzzlesize={0},{1}\n".format(self.PUZZLESIZEI,self.PUZZLESIZEJ))
        f.close()

        
    def readPuzzle(self,puzzle):
        ## パズルの読み込み(Eを-1に変換するだけ)->全部Intの方が都合がいいため
        # formatは0,1,2,3,(4)と空のマスを表すE.
        # ついでにパズルの縦と横のサイズも計算
        iSize = 0
        jSize = 0
        for line in puzzle.readlines():
            iSize += 1
            jSize = 0
            for cell in line:
                if cell == '\n':
                    continue
                jSize += 1
                if cell == "E":
                    self.convertedPuzzle.append(-1)
                else:
                    self.convertedPuzzle.append(int(cell))

        self.PUZZLESIZEI = iSize
        self.PUZZLESIZEJ = jSize
        self.NODESIZEI = iSize + 1
        self.NODESIZEJ = jSize + 1


    def flatten(self,doubleNestedList):
        ## 2重のリストをフラットに
        return [e for inner_list in doubleNestedList for e in inner_list]

    
    def execute(self,puzzle):
        ## プログラムの実行
        self.template()
        self.readPuzzle(puzzle)
        self.vdeclare()
        self.rule()
        self.end()
        puzzle.close()

    
    def __init__(self):
        ## 自動作成したプログラムの出力先
        self.output = open("output.rs",'w')

        self.option = None
        puzzle = None
        argc = len(sys.argv)
        # optionがない場合
        if argc == 2:
            puzzle = open(sys.argv[1],'r')
        else:
            puzzle = open(sys.argv[2],'r')
            #ソルバーのoption
            self.option = sys.argv[1]

        # 変換後のパズル(E->-1)
        self.convertedPuzzle = []
        
        # Puzzleのサイズ(とりあえず0,readPuzzle()で設定)
        self.PUZZLESIZEI = 0
        self.PUZZLESIZEJ = 0

        # nodeのサイズ(上と同じでとりあえず0)
        self.NODESIZEI = 0
        self.NODESIZEJ = 0

        # 変数名のリスト
        self.variablesList = []

        # flattenな変数名のリスト
        self.flattenVariablesList = []

        # 次数変数名のリスト
        self.degreeVariablesList = []

        # 経路変数名のリスト
        self.routeVariablesList = []

        # 始点(かどうか判断する)変数名のリスト
        self.startVariablesList = []

        # プログラムの実行部分
        self.execute(puzzle)


if __name__ == '__main__':

    s = SolverMaker()
