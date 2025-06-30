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

