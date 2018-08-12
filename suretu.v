Require Import Classical.

Proposition prop1 : forall (X : Type) (P : X -> X -> Prop) (f : nat -> X), (forall n : nat, P (f n) (f (n + 1))) -> (forall n : nat, P (f (n + 1)) (f (n + 2))).
Proof.
intros.
assert (H1 := H (n + 1)).
replace (n + 1 + 1) with (n + 2) in H1.
apply H1.
clear H1 H P f X.
induction n.
simpl.
reflexivity.
simpl.
auto.
Qed.

Proposition prop2 : ~(forall (X : Type) (P : X -> X -> Prop) (f : nat -> X), (forall n : nat, P (f (n + 1)) (f (n + 2))) -> (forall n : nat, P (f n) (f (n + 1)))).
intros.
intro.
assert (H0 := H (nat) (fun x y => x <> 0) (fun n => n)).
simpl in H0.
assert (forall n : nat, n + 1 <> 0).
simpl.
induction n.
simpl.
auto.
simpl.
auto.
assert (H2 := H0 H1).
assert (H3 := H2 0).
auto.
Qed.

Proposition prop3 : forall (X : Type) (P : X -> X -> Prop),
  (exists f : nat -> X, (forall n : nat, P (f n) (f (n + 1)))) ->
  (exists (f : X -> X), forall (y : X), ~(P (f y) y)) ->
  ~(forall f : nat -> X, (forall n : nat, P (f (n + 1)) (f (n + 2))) -> (forall n : nat, P (f n) (f (n + 1)))).
intros.
intro.
destruct H.
destruct H0.
assert (H2 := H1 (fun n => match n with
  | 0 => x0 (x 1)
  | _ => x n
  end)).
simpl in H2.
assert ((forall n : nat, P (x (n + 1)) (x (n + 2))) ->
  forall n : nat,
      P match n + 1 with
        | 0 => x0 (x 1)
        | S _ => x (n + 1)
        end match n + 2 with
            | 0 => x0 (x 1)
            | S _ => x (n + 2)
            end).
intro.
induction n.
simpl.
apply (H3 0).
simpl.
apply (H3 (S n)).
assert (H4 := H2 (H3 (prop1 X P x H)) 0).
simpl in H4.
apply (H0 (x 1)).
apply H4.
Qed.