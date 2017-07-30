Definition propA1 : forall (A B C : Prop), (A->B)->(B->C)->(A->C)
 := fun A B C p q r => q (p r).

Definition propA2 : forall (A B : Prop), A->(A->B)->B
 := fun A B p q => q p.

Definition propA3 : forall (A B C : Prop), (A->B->C)->(B->A->C)
 := fun A B C p q r => (p r) q.

Definition propA4 : forall (P Q : Prop), (forall P : Prop, ((P -> Q) -> Q)) -> ((P -> Q) -> P) ->  P.
Proof.
intros.
apply H0.
intros.
apply (H (P->Q)).
apply (H P).
Qed.


Require Import Arith.
Require Import Omega.




Definition propB1 : forall (n : nat), n = n + 0.
Proof.
intros.
induction n.
reflexivity.
simpl.
f_equal.
apply IHn.
Qed.




Definition propB2 : forall (n:nat), exists m, (n=2*m \/ n=2*m+1).
Proof.
induction n.
exists 0.
left.
simpl.
reflexivity.
destruct IHn.
destruct H.
exists x.
right.
omega.
exists (x+1).
left.
omega.
Qed.




Definition propB3 : forall (n : nat), (exists m, n = 2 * m) \/ (exists m, n = 2 * m + 1).
Proof.
intros.
induction n.
left.
exists 0.
simpl.
reflexivity.
destruct IHn.
destruct H.
right.
exists x.
omega.
destruct H.
left.
exists (x+1).
omega.
Qed.





Fixpoint fib (n : nat) : nat
 := match n with
  | 0 => 0
  | 1 => 1
  | S n => fib n + fib (pred n)
 end.

Definition propB4 : forall (n : nat), (exists m, (fib 3*n) = 2*m).
Proof.
intros.
induction n.
exists 0.
simpl.
reflexivity.
inversion IHn.
exists (x+1).
simpl.
simpl in H.
omega.
Qed.

Definition propB5 : forall (n : nat), (n = 5)->((fib n) = n).
Proof.
intros.
replace n with 5.
simpl.
reflexivity.
Qed.


Print propB4.
(*
Definition propB6 : forall (n : nat), ~(n = 5)->~((fib n) = n).
Proof.
intros.
*)




(*
TODO: マッカーシーの91関数
TODO: 冪剰余アルゴリズム
*)

(*
Fixpoint ninety_one (n : nat) : nat
 := 
*)


(* Definition propB5 : forall (n : nat), (n ~= 5)->~

(*
Definition propB3 : forall (n m:nat), exists k, k*k = n*n + 2*n*m + m*m.
Proof.
induction n.
induction m.
exists 0.
simpl.
reflexivity.
destruct IHm.
exists (x+1).
simpl.
simpl in H.
*)

(*
Definition propB4 : forall (n m:nat), (n*n - 2*n*m + m*m = 0)->(n = m).
Proof.
intros.
*)

(*
Definition propB3 : forall (n m:nat), (n = m)->(n*n=m*m).
Proof.
intros.
replace m with n.
reflexivity.

Definition propB4 : forall (n m:nat), (n = m)->(n*n - 2*n*m + m*m = 0).
Proof.
intros.
replace m with n.
*)



