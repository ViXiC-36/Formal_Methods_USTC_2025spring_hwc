Print nat.

Check nat_ind.

Print bool.
Check bool_ind.

Print prod.


Lemma inject_S : forall n m, S n = S m -> n = m.
Proof.
  intros n m H.
  injection H. intros. assumption.
Qed.


Lemma S_not_O : forall n, S n <> O.
Proof.
  intros n H.
  discriminate H.
Qed.

Lemma InductExample : (forall n m:nat, S n = S (S m) -> 0<>n).
Proof.
intros n m H.
injection H.
intro j.
intro k.
assert (0 = S m).
- transitivity n.
assumption.
assumption.
- discriminate H0.
Qed.

Print True.

Print False.
Check False_ind.

Print and.
Check and_ind.

Lemma and_example : forall A B : Prop, A /\ B -> A.
Proof.
  intros A B H.
  destruct H as [HA HB].  
  exact HA.  
Qed.

Theorem conj_example : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - exact HA.
  - exact HB.
Qed.

Print or.

Lemma disj_example : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  apply or_introl.
  exact HA.
Qed.



Definition is_zero (n : nat) : bool :=
  match n with
  | O => true
  | S _ => false
  end.


Definition double_plus_one (n : nat) : nat :=
  let double := n + n in
  double + 1.

Eval cbn in double_plus_one 2.


Definition get_first (p : nat * nat) : nat :=
  let (x, y) := p in x.

Definition get_first_match (p : nat * nat) : nat :=
  match p with
  | (x, y) => x
  end.

Eval cbn in get_first_match (1,2).


(*3.5 Fixpoint*)
Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => n * fact k
  end.

Eval cbn in fact 4.

(*
Fixpoint loop (n : nat) : nat := loop n.
*)

Fixpoint plus1 (n m:nat) : nat :=
match n with | O => m | S p => S (plus1 p m) end.

Eval cbn in plus1 3 2.


Fixpoint plus2 (n m:nat) : nat :=
match m with | O => n | S p => S (plus2 n p) end.

(*
Fixpoint test (b:bool) (n m:nat) : bool
  := match (n,m) with
 | (O,_) => true | (_,0) => false
 |(S p,S q)=> if b then test b p m else test b n q
end.
*)

Require Import List ZArith.
Open Scope Z_scope.
Open Scope list_scope.
Print list.

Fixpoint sum (l : list Z) : Z :=
  match l with nil => 0 | a::m => a + sum m end.
Eval cbn in sum (4::5::nil).

Fixpoint max (l : list Z) : Z := 
  match l with nil => 0
            | a::nil => a
            | a::m => let b:= max m in
                          if Zle_bool a b then b else a
  end.
Eval cbn in max (4::5::nil).

Print le.

Lemma two_le_four : le 2 4.
Proof.
  apply le_S.        (* show 2 <= 3 *)
  apply le_S.        (* show 2 <= 2 *)
  apply le_n.        (* done *)
Qed.


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
  := [ [White | White | Black] |
       [Black | White | White] | 
       [Black | Black | Black] ].

Definition target : board
:= [ [Black | Black | White] |
    [White | Black | Black] |
    [Black | Black | Black] ].

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
apply moves_step with (turn_row A start).
- apply move_moves.
apply move_row.
- replace target with (turn_row B (turn_row A start)).
apply move_row.
reflexivity.
Qed.

