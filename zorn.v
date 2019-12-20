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

Definition wellord (A : Type) (R : relation A) :=
  forall e : Ensemble A, (exists a, e a) ->
  (exists x, e x /\ forall y, e y -> R x y).

Definition wellord_ens (A : Type) (R : relation A) (E : Ensemble A) :=
  forall e : Ensemble A, Included _ e E -> (exists a, e a) ->
  (exists x, e x /\ forall y, e y -> R x y).

Definition transfinite_induction : forall
  (A : Type)
  (R : relation A)
  (anti : antisymmetric A R)
  (well : wellord A R)
  (P : A -> Prop),
  (forall (a : A), (forall (b : A), (R b a /\ b <> a) -> P b) -> P a)
  -> (forall c : A, P(c)).
Proof.
intros.
unfold antisymmetric in anti.
assert (~ (exists t, ~(P t))).
intro.
destruct H0.
rename x into t.
assert (well0 := well (fun x => ~(P x))).
simpl in well0.
assert (exists x : A, ~ P x /\ (forall y : A, ~ P y -> R x y)).
apply well0.
exists t.
trivial.
destruct H1.
destruct H1.
apply H1.
apply H.
intros.
destruct H3.
apply NNPP.
intro.
assert (H6 := H2 b H5).
apply H4.
apply anti.
trivial.
trivial.
assert (H1 := not_ex_all_not _ _ H0).
apply NNPP.
apply H1.
Qed.

Definition connex (A : Type) (R : relation A) (sub : Ensemble A) :=
  (forall x y : A, sub x -> sub y -> R x y \/ R y x).

Definition Big (A : Type) (R : relation A) (f : Ensemble A -> A) :=
  (fun s => exists sub : Ensemble A,
    wellord_ens A R sub /\
    (forall x, sub x -> x = f (fun t => sub t /\ R t x /\ t <> x)) /\
    sub s).

Definition zorn : forall
  (A : Type)
  (R : relation A)
  (Ord : order A R),
    (forall sub : Ensemble A,
      (connex A R sub ->
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
clear Ord.
intro.

(* proof of inhabited A *)
unfold connex in H.
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
  connex A R sub ->
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
  connex A R sub ->
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
clear Hex.

(* create some big ensemble, and proof that
   both [Big (f Big)] and [~ Big (f Big)]
   leads to a contradiction *)

(* First, prive Big is connex. *)
assert (connex A R (Big A R f)).
unfold Big.
unfold connex.
unfold wellord_ens.
unfold Included.
unfold In.
intros.
destruct H.
destruct H.
destruct H1.
destruct H0.
destruct H0.
destruct H3.
rename x0 into sub1.
rename x1 into sub2.
rename H into Hw1.
rename H0 into Hw2.
rename H1 into Hf1.
rename H3 into Hf2.
rename H2 into Hi1.
rename H4 into Hi2.

assert (exists m, sub1 m
  /\ forall y : A, sub1 y -> R m y).
assert (H := Hw1 sub1).
apply H.
intros.
trivial.
exists x.
trivial.
destruct H.
destruct H.
rename x0 into min1.
rename H into Hmin11.
rename H0 into Hmin12.

assert (exists m, sub2 m
  /\ forall y : A, sub2 y -> R m y).
assert (H := Hw2 sub2).
apply H.
intros.
trivial.
exists y.
trivial.
destruct H.
destruct H.
rename x0 into min2.
rename H into Hmin21.
rename H0 into Hmin22.

assert (Hfm1 := Hf1 min1 Hmin11).
assert (Hfm2 := Hf2 min2 Hmin21).
assert (min1 = min2).
rewrite Hfm2.
rewrite Hfm1.
apply f_equal.
apply Extensionality_Ensembles.
split.

intro.
intro.
destruct H.
destruct H0.
apply False_ind.
apply H1.
apply anti.
trivial.
apply Hmin12.
trivial.

intro.
intro.
destruct H.
destruct H0.
apply False_ind.
apply H1.
apply anti.
trivial.
apply Hmin22.
trivial.

clear Hfm1 Hfm2.

case (classic (R x y)).
intro.
left.
trivial.
intro.
right.



