Notation "[ a ] < [ b ]" := (forall (F : a -> b), exists (y : b), forall (x : a), F x <> y).
Notation "[ a ] > [ b ]" := ([b] < [a]).
Notation "[ a ] = [ b ]" := (~([a] < [b]) /\ ~([a] > [b])).

Proposition prop1 : forall (A : Type), [A] < [A -> bool].
Proof.
intros A F.
remember (fun n => negb (F n n)) as G.
exists G.
intros n H.
assert (F n n = G n).
replace (F n) with G.
reflexivity.
rewrite HeqG in H0.
destruct (F n n).
inversion H0.
inversion H0.
Qed.

Proposition prop2 : forall (A : Type), [A] = [A].
Proof.
intros A.
assert (~ [A]> [A]).
intro H.
assert (H0 := H (fun x => x)).
simpl in H0.
case H0.
intro x.
intro x0.
assert (H1 := x0 x).
congruence.
split.
apply H.
apply H.
Qed.

(*
Proposition prop3 : [nat * nat] = [nat].
Proof.
split.
intro H.
assert (H0 := H (fun t => fst t)).
case H0.
intros x H1.
simpl in H1.
assert (H2 := H1 (pair x x)).
simpl in H2.
congruence.
intro H.
assert (H0 := H (fun n => pair n n)).
case H0.
intros x H1.
assert (H2 := H1 (fst x)).
*)