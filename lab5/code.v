
Check nat.
Check S.
Check plus.
Check (3+2).
Check (1+2=3).

Lemma ex0: forall A B C:Prop,
(A -> B -> C) -> (A -> B) -> A -> C.
Proof.
intros. apply H.
- assumption.
- apply H0. assumption.
Qed.


Lemma ex1: forall A B C:Prop,
(A -> B -> C) -> (A -> B) -> A -> C.
Proof.
intro h1.
intro h2.
intro h3.
intro h4.
intro h5.
intro h6.
apply h4.
assumption.
apply h5.
assumption.
Qed.



Lemma ex2: forall A B C:Prop,
(A -> B -> C) -> (A -> B) -> A -> C.
Proof.
intros.
apply H.
assumption.
apply H0.
assumption.
Qed.


Lemma ex3: forall A B C:Prop,
(A -> B -> C) -> (A -> B) -> A -> C.
Proof.
auto.
Qed.

Section SectionExample.
Variables A B C: Prop.
Lemma ex4 : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
intros.
apply H.
assumption.
apply H0.
assumption.
Qed.
End SectionExample.

Section AdmitExample.
Variables A B C: Prop.
Lemma falselemma: (A -> B) -> C.
Proof.
Admitted.

Lemma falseconclusion: B -> C.
Proof.
intros.
apply falselemma.
intros.
exact H.
Qed.
End AdmitExample.




Section AndIntroExample.
Variables A B : Prop.
Lemma and_intro_ascii : A -> B -> A /\ B.
Proof.
  intros HA HB.
  split.
    exact HA.
    exact HB.
Qed.
End AndIntroExample.


Section AndElimExample.
Variables A B : Prop.
Lemma and_elim_ascii : A /\ B -> A.
Proof.
  intros H.
  destruct H as [HA HB].
  exact HA.
Qed.
End AndElimExample.

Section OrIntro.
Variables A B : Prop.
Lemma or_intro_left_example : A -> A \/ B.
Proof.
  intros HA.
  left.
  exact HA.
Qed.
End OrIntro.


Section OrElimExample.
Variables A B C : Prop.
Lemma or_elim_example : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
  intros H_or HA_to_C HB_to_C.
  destruct H_or as [HA | HB].
  - apply HA_to_C. exact HA.
  - apply HB_to_C. exact HB.
Qed.
End OrElimExample.

Section NotIntroExample.
Variables A : Prop.
Lemma not_intro_example : (A -> False) -> ~A.
Proof.
  intros H.
  exact H.
Qed.
End NotIntroExample.

Section NotElimExample.
Variable A : Prop.
Lemma not_elim_with_destruct : A -> ~A -> False.
Proof.
  intros HA HNA.
  destruct HNA.
  exact HA.
Qed.
End NotElimExample.



Section FalseElimExample.
Variable A : Prop.
Lemma false_elim_with_exfalso : A -> ~A -> forall B : Prop, B.
Proof.
  intros HA HNA B.
  exfalso.
  apply HNA. exact HA.
Qed.
End FalseElimExample.


Section ForallIntroExample.
Variable A : nat -> Prop.
Variable H : forall n : nat, A n.
Lemma forall_intro_example2 : forall n : nat, A n.
Proof.
  intros n.
  apply H.
Qed.
End ForallIntroExample.

Section ForallElimExample.
Variable A : nat -> Prop.
Lemma forall_elim_example : (forall n : nat, A n) -> A 0.
Proof.
  intros H.
  apply H.
Qed.
End ForallElimExample.

Section ExistsIntroExample.
Variable A : nat -> Prop.
Lemma exists_intro_example : A 0 -> exists n : nat, A n.
Proof.
  intros H.
  exists 0.
  exact H.
Qed.
End ExistsIntroExample.

Section ExistsElimExample.
Variable A : nat -> Prop.
Lemma exists_elim_example : (exists n : nat, A n) -> 
  forall P : Prop, (forall x, A x -> P) -> P.
Proof.
  intros Hexists P Hforall.
  destruct Hexists as [n HAn].
  apply Hforall with (x := n).
  exact HAn.
Qed.
End ExistsElimExample.

Section AssertExample.
Variables A B C : Prop.
Lemma assert_example : (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros H1 H2 HA.
  assert (HB : B).
  - apply H1. exact HA.
  - apply H2. exact HB.
Qed.
End AssertExample.

Require Import Classical.

Section Homework.
Variables A B : Prop.
Variable T : Type.
Variable  P : T -> Prop .

Lemma homework1: forall A, ~~~ A -> ~ A.
Proof.
  intros.
  intro H0.
  apply H.
  intro H1.
  apply H1.
  exact H0.
Qed.

Lemma homework2: A \/ B -> ~ (~ A /\ ~ B).
Proof.
  intro Hor.
  intro Hand.
  destruct Hor as [HA | HB].
  destruct Hand as [HNA HNB].
  apply HNA.
  exact HA.
  destruct Hand as [HNA HNB].
  apply HNB.
  exact HB.
Qed.

Lemma homework3: (~ exists x, P x) -> forall x, ~ P x.
Proof.
  intro HNexists.
  intro x0.
  intro HPx0.
  apply HNexists.
  exists x0.
  exact HPx0.
Qed.

Lemma homework4: A -> ~~A.
Proof.
  intro HA.
  intro HNA.
  apply HNA.
  exact HA.
Qed.

Lemma homework5: (A \/ ~A) -> (~~A -> A).
Proof.
  intro Hor.
  intro HNNA.
  destruct Hor as [HA | HNA].
  - exact HA.
  - exfalso. apply HNNA. exact HNA.
Qed.

End Homework.



