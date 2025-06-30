# 形式化方法 实验小作业5 ROCQ
PB22111599 杨映川

## Lemma homework1

```
Lemma homework1: forall A, ~~~ A -> ~ A.
Proof.
  intros.
  intro H0.
  apply H.
  intro H1.
  apply H1.
  exact H0.
Qed.
```



![alt text](image.png)

![alt text](image-1.png)

![alt text](image-2.png)

![alt text](image-3.png)

![alt text](image-4.png)

![alt text](image-5.png)

![alt text](image-6.png)

![alt text](image-7.png)

## Lemma homework2

```
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
```



![alt text](image-8.png)

![alt text](image-9.png)

![alt text](image-10.png)

![alt text](image-11.png)

![alt text](image-12.png)

![alt text](image-13.png)

![alt text](image-14.png)

![alt text](image-15.png)



![alt text](image-17.png)

![alt text](image-18.png)



## Lemma homework3

```
Lemma homework3: (~ exists x, P x) -> forall x, ~ P x.
Proof.
  intro HNexists.
  intro x0.
  intro HPx0.
  apply HNexists.
  exists x0.
  exact HPx0.
Qed.
```



![alt text](image-19.png)

![alt text](image-20.png)

![alt text](image-21.png)

![alt text](image-22.png)

![alt text](image-23.png)

![alt text](image-24.png)

![alt text](image-25.png)

![alt text](image-26.png)

## Lemma homework4

```
Lemma homework4: A -> ~~A.
Proof.
  intro HA.
  intro HNA.
  apply HNA.
  exact HA.
Qed.
```



![alt text](image-27.png)

![alt text](image-28.png)

![alt text](image-29.png)

![alt text](image-30.png)

![alt text](image-31.png)

![alt text](image-32.png)



## Lemma homework5

```
Lemma homework5: (A \/ ~A) -> (~~A -> A).
Proof.
  intro Hor.
  intro HNNA.
  destruct Hor as [HA | HNA].
  - exact HA.
  - exfalso. apply HNNA. exact HNA.
Qed.
```



![alt text](image-33.png)

![alt text](image-34.png)

![alt text](image-35.png)

![alt text](image-36.png)

![alt text](image-37.png)

![alt text](image-38.png)

![alt text](image-39.png)

![alt text](image-40.png)

![alt text](image-41.png)

![alt text](image-42.png)

![alt text](image-43.png)

