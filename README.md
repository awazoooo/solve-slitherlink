### スリザーリンクを (SMTソルバを用いて) 解くプログラム
* z3pyは用いていない
<!-- 使い方がわからない -->

## 動作に必要な環境
・z3 (SMTソルバ)
・Python 2.7.12

## 使い方
./solver-slitherlink.py sample/slitherlink8.txt


入力は

```
E0E1EE1E
E3EE23E2
EE0EEEE0
E3EE0EEE
EEE3EE0E
1EEEE3EE
3E13EE3E
E0EE3E3E
```

のような形のテキストファイルとする(Eは空白セル)

<!-- chmod 755 *.py などして権限が必要...改善したい -->
<!-- z3をos.systemする必要あるから厳しい？ -->
