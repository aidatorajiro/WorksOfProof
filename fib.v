Require Import QArith.
Require Import Arith.
Require Import Omega.

(* RI x y = x + y√5 *)
Record ri : Set := RI { R : Q; I : Q }.

Definition RIred (r : ri) := RI (Qred (R r)) (Qred (I r)).

Definition RInegate (r : ri) := RI (0 - R r) (0 - I r).

Definition RIplus (r1 : ri) (r2 : ri) := RI (R r1 + R r2) (I r1 + I r2).

Definition RIminus (r1 : ri) (r2 : ri) := RIplus r1 (RInegate r2).

Definition RImult (r1 : ri) (r2 : ri) :=
  let w := R r1  in
  let x := I r1  in
  let y := R r2  in
  let z := I r2  in
  let a := 5 # 1 in
  RI (w * y + x * z * a) (w * z + x * y).

Fixpoint RIpower (r : ri) (n: nat) :=
  match n with
  | O => RI (1 # 1) (0 # 1)
  | S O => r
  | S n => RImult (RIpower r n) r
  end.

Notation "a ^ b" := (RIpower a b).
Notation "a * b" := (RImult  a b).
Notation "a + b" := (RIplus  a b).
Notation "a - b" := (RIminus a b).

Definition fib (n : nat) := RI 0 (1 # 5) * ((RI (1 # 2) (1 # 2)) ^ n - (RI (1 # 2) ((0 - 1) # 2)) ^ n).

Fixpoint fib' (n : nat) : nat
 := match n with
  | O => 0
  | S O => 1
  | S n => fib' n + fib' (pred n)
 end.



Definition prop : forall (n : nat), (Z.of_nat (fib' n)) # 1 = R (RIred (fib n)).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl in IHn.
simpl.
