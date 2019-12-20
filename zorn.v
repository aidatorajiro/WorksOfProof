Require Import Relations.
Require Import Ensembles.
Require Import ClassicalFacts.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.
Require Import ClassicalChoice.

Definition choice_cond :
    forall (A B : Type) (R : A->B->Prop) (P : A -> Prop),
   inhabited B ->
   (forall x : A, P x -> exists y : B, R x y) ->
    exists f : A->B, (forall x : A, P x -> R x (f x)).
Proof.
intro.
intro.
intro.
intro.
intro Bin.
intro.
apply (choice (fun (a : A) (b : B) => P a -> R a b)).
intro.
assert (H0 := H x).
case (classic (P x)).
intro.
destruct (H0 H1).
exists x0.
intro.
trivial.
intro.
destruct Bin.
exists X.
intro.
apply False_ind.
apply H1.
trivial.
Qed.

Definition zorn : forall
  (A : Type)
  (R : relation A)
  (Ord : order A R),
    (forall sub : Ensemble A,
      ((forall x y, sub x -> sub y -> R x y \/ R y x) ->
       (exists x, forall y, sub y -> R y x)))
    -> exists x, ~ (exists y, R x y /\ x <> y).
intro.
intro.
intro.
assert (refl := ord_refl A R Ord).
assert (trans := ord_trans A R Ord).
assert (anti := ord_antisym A R Ord).
unfold reflexive in refl.
unfold transitive in trans.
unfold antisymmetric in anti.
intro.

(* proof of inhabited A *)
assert (exists x : A, forall y : A, False -> R y x).
apply H.
intros.
apply False_ind.
trivial.
destruct H0.
clear H0.
rename x into inh.
rename H into Hsub.

(* change goal and hypothesis *)
apply NNPP.
intro.
assert (H0 := not_ex_all_not _ _ H).
simpl in H0.
assert (forall n : A, exists y : A, R n y /\ n <> y).
intro.
apply NNPP.
apply (H0 n).
clear H.
clear H0.
rename H1 into Hex.

(* find some excluded and larger element for all subsets *)
assert (forall sub : Ensemble A,
  (forall x y : A, sub x -> sub y -> R x y \/ R y x) ->
  exists g : A, forall z : A, sub z -> R z g /\ z <> g).
intros.
assert (H1 := Hsub sub H).
destruct H1.
assert (H1 := Hex x).
destruct H1.
destruct H1.
exists x0.
intros.
split.
apply (trans _ x _).
apply H0.
trivial.
trivial.
intro.
apply H2.
apply anti.
trivial.
apply H0.
rewrite <- H4.
trivial.
rename H into Hgre.
clear Hsub.

(* apply axiom of choice *)
assert (exists f : (Ensemble A)->A, (forall sub : Ensemble A,
  (forall x y : A, sub x -> sub y -> R x y \/ R y x) ->
  forall z : A, sub z -> R z (f sub) /\ z <> (f sub))).
apply (choice_cond (Ensemble A) A (fun (sub : Ensemble A) (x : A) =>
  forall z : A, sub z -> R z x /\ z <> x)).
exists.
trivial.
intros.
rename H into Hchn.
apply (Hgre x).
trivial.
destruct H.
rename H into Hfun.
rename x into f.
clear Hgre.


(* create an impossible ensemble *)
assert (exists e : Ensemble A -> A, forall w : Ensemble A, e w =
  f (fun a : A => exists v, RE v w /\ v <> w /\ a = e v)).






