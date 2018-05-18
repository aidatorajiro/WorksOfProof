Proposition prop1 : forall (X : Type) (f : nat -> X) (P : X -> X -> Prop), (forall n : nat, P (f n) (f (n + 1))) <-> (forall n : nat, P (f (n + 1)) (f (n + 2))).
Proof.
intros.
split.
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
intros.
assert (H1 := H (n - 1)).