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

(* connexity *)
Definition connex (A : Type) (R : relation A) (sub : Ensemble A) :=
  (forall x y : A, sub x -> sub y -> R x y \/ R y x).

(* every nonempty subset has least element *)
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

Definition Small (A : Type) (R : relation A)
  (f : Ensemble A -> A) (sub : Ensemble A) :=
    connex A R sub /\
    wellord_ens A R sub /\
    (forall x, sub x -> x = f (fun t => sub t /\ R t x /\ t <> x)).

Definition Big (A : Type) (R : relation A) (f : Ensemble A -> A) :=
  (fun s => exists sub : Ensemble A, Small _ R f sub /\ sub s).

Definition Seg (A : Type) (R : relation A)
  (sub : Ensemble A) (x : A) :=
    (fun t => sub t /\ R t x /\ t <> x).

Definition StrictUpperBoundFunc (A : Type) (R : relation A) (f : Ensemble A -> A) := 
  forall sub : Ensemble A,
       connex A R sub ->
       forall z : A, sub z -> R z (f sub) /\ z <> f sub.

Definition small_combine : forall
  (A : Type)
  (R : relation A)
  (Ord : order A R)
  (f : Ensemble A -> A)
  (bound : StrictUpperBoundFunc A R f)
  (sub1 : Ensemble A)
  (sub2 : Ensemble A)
  (Hsub1 : Small A R f sub1)
  (Hsub2 : Small A R f sub2),
    (Included _ sub1 sub2 /\ exists x, sub1 = Seg A R sub2 x) \/ 
    (Included _ sub2 sub1 /\ exists x, sub2 = Seg A R sub1 x).
Admitted.

Definition small_big : forall
  (A : Type)
  (R : relation A)
  (Ord : order A R)
  (f : Ensemble A -> A)
  (bound : StrictUpperBoundFunc A R f),
    Small A R f (Big A R f).
Admitted.

(*
assert (connex A R (Big A R f)).
unfold connex.
unfold Big.
intros.
destruct H.
destruct H0.
destruct H.
destruct H0.
rename x0 into subx.
rename x1 into suby.
assert (SC := small_combine A R Ord f Hfun subx suby H H0).
case SC.
intro.
destruct H3.
destruct H4.
destruct H0.
apply H0.
apply H3.
trivial.
trivial.
intro.
destruct H3.
destruct H4.
destruct H.
apply H.
trivial.
apply H3.
trivial.
*)

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
assert (exists f : (Ensemble A)->A, StrictUpperBoundFunc A R f).
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

(* create some big ensemble and use
   it to get a contradiction *)

(* First, prove Big is connex. *)
assert (H := small_big A R Ord f Hfun).
destruct H.
destruct H0.
rename H into Hcon.
rename H0 into Hwel.
rename H1 into Hbon.
assert (Hdec := Hfun (Big A R f) Hcon).

(* Second, proof Big (f Big) *)

(* connex *)
assert (Big A R f (f (Big A R f))).
unfold Big.
exists (fun t => Big A R f t \/ t = f (Big A R f)).
split.
split.
intro.
intros.
case H.
case H0.
intros.
apply Hcon.
trivial.
trivial.
intros.
left.
rewrite H1.
assert (H3 := Hdec x H2).
destruct H3.
trivial.
intro.
case H0.
intro.
right.
rewrite H1.
assert (H3 := Hdec y H2).
destruct H3.
trivial.
intro.
left.
rewrite H1.
rewrite H2.
apply refl.

(* wellord *)
split.
intro.
intros.
unfold Included in H.
unfold In in H.
case (classic (exists t, e t /\ Big A R f t)).
intro.
assert (exists x : A, (e x /\ Big A R f x) /\
  (forall y : A, e y /\ Big A R f y -> R x y)).
apply (Hwel).
intro.
intro.
destruct H2.
trivial.
trivial.
destruct H2.
destruct H2.
destruct H2.
exists x.
split.
trivial.
intros.
assert (H6 := H y H5).
case H6.
intro.
apply H3.
split.
trivial.
trivial.
intro.
assert (H8 := Hdec _ H4).
destruct H8.
rewrite H7.
trivial.

intro.
assert (forall t, e t -> t = f (Big A R f)).
intros.
assert (H3 := not_ex_all_not _ _ H1).
assert (H4 := not_and_or _ _ (H3 t)).
case H4.
intro.
contradiction.
intro.
assert (H6 := H t H2).
case H6.
intro.
contradiction.
intro.
auto.
destruct H0.
exists x.
split.
trivial.
intros.
rewrite (H2 _ H0).
rewrite (H2 _ H3).
auto.

(* bound condition *)
intros.
case H.
intro.
assert (H1 := Hbon x H0).
rewrite H1 at 1.
apply f_equal.
apply Extensionality_Ensembles.
split.
intro.
intro.
destruct H2.
destruct H3.
split.
left.
trivial.
split.
trivial.
trivial.

intro.
intro.
destruct H2.
destruct H3.
split.
assert (H5 := Hdec _ H0).
destruct H5.
assert (x0 <> f (Big A R f)).
intro.
rewrite H7 in H4.
rewrite H7 in H3.
apply H6.
apply anti.
trivial.
trivial.
case H2.
intro.
trivial.
intro.
contradiction.
split.
trivial.
trivial.

intros.
rewrite H0.
apply f_equal.
apply Extensionality_Ensembles.
split.
intro.
intro.
split.
left.
trivial.
apply Hdec.
trivial.
intro.
intro.
destruct H1.
destruct H2.
case H1.
intro.
trivial.
intro.
contradiction.
right.
reflexivity.

(* make a contradiction *)
assert (H0 := Hdec _ H).
destruct H0.
contradiction.
Qed.


(*
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
destruct H2.
destruct H0.
destruct H0.
destruct H4.
destruct H5.
rename x0 into sub1.
rename x1 into sub2.
rename H into Hcon1.
rename H1 into Hw1.
rename H0 into Hcon2.
rename H4 into Hw2.
rename H2 into Hf1.
rename H5 into Hf2.
rename H3 into Hi1.
rename H6 into Hi2.


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
rename H into Hsame.
rewrite <- Hsame in Hmin22.
assert (Hs1 := Hmin12 x Hi1).
assert (Hs2 := Hmin22 y Hi2).

case (classic (sub1 y)).
intro.
apply (Hcon1 _ _ Hi1 H).
intro.
rename H into Hnot.



assert (
  let e := (fun t => (~ sub1 t) /\ sub2 t)
  in exists x : A, e x /\ (forall y : A, e y -> R x y)).
apply Hw2.
intros.
destruct H.
trivial.
exists y.
split.
trivial.
trivial.
destruct H.
destruct H.
destruct H.
rename x0 into rem.
rename H into Hrem1.
rename H1 into Hrem2.
rename H0 into Hrem3.

assert (Included _ (fun t : A => sub1 t /\ R t rem /\ t <> rem) sub2).
intro.
unfold In.
intro.
destruct H.
destruct H0.
apply NNPP.
intro.


assert (
  let sub := (fun t => sub1 t /\ R t x)
  in forall z : A, sub z -> R z (f sub) /\ z <> f sub).
apply Hfun.
intro.
split.

*)
