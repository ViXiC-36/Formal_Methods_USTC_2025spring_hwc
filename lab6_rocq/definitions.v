Section DefinitionExample.
Variable A : Type.
Variables x y : A.
Definition triple : A * A * A := (x,y,x). 
Check triple.
Print triple.
End DefinitionExample.





Definition square (x:nat) : nat := x * x.
Lemma square_3 : square 3 = 9.
Proof.
  unfold square.
  simpl.
  reflexivity.
Qed.



Definition mysix:=6.
Check mysix.
Print mysix.
Definition anothernat:= mysix+5*2.
Print anothernat.

(* Evaluate in strategy cbn*)
Eval cbn in anothernat.



Definition double (n : nat) := n + n.
Definition example := double (1 + 1).
Lemma comparestrategy : example =4.
Proof.
  unfold example.
  simpl.
  (*cbn or simpl or cbv*)
  cbv.
  reflexivity.
Qed.

Check fun x =>x+1.

Eval cbn in (fun x => x + 1) 2.

Definition add1 := fun (x : nat) => x + 1.

Compute add1 2.  (* Output: 3 *)

Print Libraries.
Require Import Arith.


Search plus.

Search [plus 0].

Search (~_ <->_).


Require Import ZArith. 
Open Scope Z_scope.

Search (Z->Z->bool).

Search Z.leb.

Require Import ZArith. 
Open Scope Z_scope.
Definition abs (n:Z) : Z := if Z.leb 0 n then n else -n.
Lemma abs_pos : forall n, 0 <= abs n.
intro n.
unfold abs.
assert (if Z.leb 0 n then 0 <= n else 0 > n).
- Search Z.leb. apply Zle_cases.
- destruct (Z.leb 0 n);auto with zarith.
Qed.

Require Import ZArith. 
Open Scope Z_scope.
Definition abs1 (n:Z) : Z := if Z.leb 0 n then n else -n.
Lemma abs_pos1 : forall n, 0 <= abs n.
intro n.
unfold abs.
assert (if Z.leb 0 n then 0 <= n else 0 > n).
- apply Zle_cases.
- destruct (Z.leb 0 n).
apply H.
Search [Z.lt Z.gt]. assert (n<0).  apply Z.gt_lt. assumption.
assert (n<=0).
Search [Z.lt Z.le]. apply Z.lt_le_incl. assumption.
Search [Z.le Z.opp]. apply Z.opp_nonneg_nonpos. assumption.
Qed.