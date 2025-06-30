# 形式化方法 lab 6 实验小作业

- 棋盘更改后的复现

PB22111599 杨映川

## 1 更改后的棋盘

```c
Definition start : board
  := [ [Black | White | Black] |
       [White | White | White] | 
       [White | Black | Black] ].

Definition target : board
  := [ [Black | Black | Black] |
       [White | Black | White] |
       [Black | Black | White] ].
```

通过观察可以发现，一种解法为：start -> turn_row A -> turn_row B -> turn_col A -> turn_col C -> target

## 2 代码实现

```C
Lemma reachable : moves start target.
apply moves_step with (turn_col A (turn_row B (turn_row A start))).
- apply moves_step with (turn_row B (turn_row A start)).
    apply moves_step with (turn_row A start).
    apply move_moves.
    apply move_row.
  apply move_row.
apply move_col.
- replace target with (turn_col C (turn_col A (turn_row B (turn_row A start)))).
apply move_col.
reflexivity.
Qed.

```

仅修改了`Lemma reachable`的部分，借助预先发现的一条路径反推出证明

## 3 运行过程

![image-20250528213338872](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213338872.png)



![image-20250528213358860](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213358860.png)



![image-20250528213415953](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213415953.png)



![image-20250528213428084](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213428084.png)



![image-20250528213440726](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213440726.png)



![image-20250528213452079](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213452079.png)



![image-20250528213503460](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213503460.png)



![image-20250528213513630](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213513630.png)



![image-20250528213524190](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213524190.png)



![image-20250528213534866](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213534866.png)



![image-20250528213545818](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213545818.png)



![image-20250528213558245](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213558245.png)

![image-20250528213610125](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213610125.png)



![image-20250528213622071](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250528213622071.png)

## 4 完整代码

```c
Inductive color : Type := White | Black.
Inductive pos : Type := A | B | C.
Inductive triple M := Triple : M -> M -> M -> triple M.
Set Implicit Arguments.

Notation "[ x | y | z ]" := (Triple _ x y z).

Definition triple_x M (m:M) : triple M := [m | m | m].

Definition turn_color (c: color) : color :=
  match c with | White => Black | Black => White end.

Definition triple_map M f (t: triple M) : triple M:= 
match t with (Triple _ a b c) => [(f a)|(f b)|(f c)] end.

Definition triple_map_select M f p t : triple M := 
  match t with (Triple _ a b c) =>
    match p with | A => [ (f a) | b | c ] 
                 | B => [ a | (f b) | c ] 
                 | C => [ a | b | (f c) ]
    end 
  end.

Definition board := triple (triple color).

Definition start : board
  := [ [Black | White | Black] |
       [White | White | White] | 
       [White | Black | Black] ].

Definition target : board
  := [ [Black | Black | Black] |
       [White | Black | White] |
       [Black | Black | White] ].

Definition turn_row (p: pos) : board -> board := 
    triple_map_select (triple_map turn_color) p.

Definition turn_col (p: pos) : board -> board := 
    triple_map (triple_map_select turn_color p).

Definition move1 (b1 b2: board) : Prop :=
        (exists p : pos, b2=turn_row p b1)
     \/ (exists p : pos, b2=turn_col p b1).

Inductive move (b1:board) : board -> Prop :=
move_row : forall (p:pos), move b1 (turn_row p b1) | move_col : forall (p:pos), move b1 (turn_col p b1).

Inductive moves (b1:board): board -> Prop := 
  moves_init : moves b1 b1
| moves_step : forall b2 b3,
                 moves b1 b2 -> move b2 b3 -> moves b1 b3.

Lemma move_moves : forall b1 b2, move b1 b2 -> moves b1 b2.
intros. 
apply moves_step with b1.
apply moves_init.
assumption.
Qed.

Lemma reachable : moves start target.
apply moves_step with (turn_col A (turn_row B (turn_row A start))).
- apply moves_step with (turn_row B (turn_row A start)).
    apply moves_step with (turn_row A start).
    apply move_moves.
    apply move_row.
  apply move_row.
apply move_col.
- replace target with (turn_col C (turn_col A (turn_row B (turn_row A start)))).
apply move_col.
reflexivity.
Qed.


```



