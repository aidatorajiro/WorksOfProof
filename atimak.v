Require Import Ensembles.
Require Import ClassicalFacts.


Variable T:Type.

Record Ring : Type := mkRing {
  number : Ensemble T;
  plus : T -> T -> T;
  mult : T -> T -> T;
  zero : T;
  one : T;
  inv : T -> T;
  in_plus: forall a b, number a -> number b -> number (plus a b);
  in_mult: forall a b, number a -> number b -> number (mult a b);
  in_zero: number (zero);
  in_one: number (one);
  in_inv: forall a, number a -> number (inv a);
  plus_inv : forall n : T, number n
    -> plus n (inv n) = zero;
  plus_zero : forall n : T, number n
    -> plus n zero = n;
  plus_assoc : forall a b c, number a -> number b -> number c
    -> plus (plus a b) c = plus a (plus b c);
  plus_rev : forall a b, number a -> number b
    -> plus a b = plus b a;
  mult_assoc : forall a b c, number a -> number b -> number c
    -> mult (mult a b) c = mult a (mult b c);
  mult_dist : forall a b c, number a -> number b -> number c
    -> mult a (plus b c) = plus (mult a b) (mult a c);
  mult_rev : forall a b, number a -> number b
    -> mult a b = mult b a;
  mult_one : forall a, number a
    -> mult a one = a;
}.

Proposition prop_mult_zero : forall (X : Ring) x, (number X) x ->
  (mult X) x (zero X) = (zero X).
Proof.
intros.
assert (mult X (plus X (zero X) (zero X)) x = mult X (zero X) x).
rewrite (plus_zero X (zero X)).
reflexivity.
apply in_zero.
rewrite (mult_rev) in H0.
rewrite (mult_dist) in H0.
assert (plus X (plus X (mult X x (zero X))
  (mult X x (zero X))) (inv X (mult X x (zero X))) =
  plus X (mult X (zero X) x) (inv X (mult X (zero X) x))).
rewrite H0.
rewrite (mult_rev X x (zero X)).
reflexivity.
trivial.
apply in_zero.
rewrite (plus_assoc X (mult X x (zero X)) (mult X x (zero X))
  (inv X (mult X x (zero X)))) in H1.
rewrite (plus_inv X (mult X x (zero X))) in H1.
rewrite plus_zero in H1.
rewrite plus_inv in H1.
trivial.
apply in_mult.
apply in_zero.
trivial.
apply in_mult.
trivial.
apply in_zero.
apply in_mult.
trivial.
apply in_zero.
apply in_mult.
trivial.
apply in_zero.
apply in_mult.
trivial.
apply in_zero.
apply in_inv.
apply in_mult.
trivial.
trivial.
apply in_zero.
trivial.
apply in_zero.
apply in_zero.
apply in_plus.
apply in_zero.
apply in_zero.
trivial.
Qed.

Require Import Setoid.

Proposition prop_mult_inv : forall (X : Ring) x, number X x -> mult X x (inv X (one X)) = inv X x.
Proof.
intro.
intro.
intro Hin.
assert (H := prop_mult_zero X x).
rewrite <- (plus_inv X (one X)) in H at 1.
rewrite <- (plus_inv X x) in H.
rewrite mult_dist in H.
apply (f_equal (fun t => plus X (inv X x) t)) in H.
rewrite (mult_one) in H.
rewrite <- (plus_assoc) in H.
rewrite (plus_rev X (inv X x) x) in H.
rewrite plus_inv in H.
rewrite (plus_rev) in H.
rewrite (plus_zero) in H.
rewrite (plus_zero) in H.
trivial.
apply in_inv.
trivial.
apply in_mult.
trivial.
apply in_inv.
apply in_one.
apply in_zero.
apply in_mult.
trivial.
apply in_inv.
apply in_one.
trivial.
apply in_inv.
trivial.
trivial.
apply in_inv.
trivial.
trivial.
apply in_mult.
trivial.
apply in_inv.
apply in_one.
trivial.
trivial.
trivial.
apply in_one.
apply in_inv.
apply in_one.
trivial.
apply in_one.
Qed.

Definition principal_ideal := (fun (X : Ring) (x : T) =>
    (fun a => exists k : T, number X k /\ a = mult X k x)).

Definition ideal := (fun (X : Ring) (a : Ensemble T) (Pinc : Included _ a (number X)) =>
       (forall x y, a x        -> a y -> a (plus X x y))
    /\ (forall x y, number X x -> a y -> a (mult X x y))
    /\ Inhabited _ a).

Definition unit := (fun (X : Ring) (a : T) => exists b, number X b /\ mult X a b = one X).

Definition zerodiv := (fun (X : Ring) (a : T) => exists b, b <> zero X /\ mult X a b = zero X).

Definition integral_domain := (fun (X : Ring) => forall (a : T), number X a -> a <> zero X -> ~ (zerodiv X a)).

Fixpoint pow (X : Ring) (a : T) (n : nat) :=
  match n with
    | 0 => one X
    | S m => mult X (pow X a m) a
  end.

Definition nilpotent := (fun (X : Ring) (x : T) => exists (n : nat), pow X x n = zero X).

(*Definition injective := (fun (X : Type) (Y : Type) (F : X -> Y) => forall x y, F x = F y -> x = y).*)

Proposition principal_ideal_num : forall (X : Ring) x (P : number X x),
    Included _ (principal_ideal X x) (number X).
Proof.
intros.
intro.
unfold principal_ideal.
unfold In.
intro.
destruct H.
destruct H.
rewrite H0.
apply in_mult.
trivial.
trivial.
Qed.

Proposition principal_ideal_is_ideal : forall (X : Ring) x (P : number X x),
  ideal X (principal_ideal X x) (principal_ideal_num X x P).
Proof.
intro.
intro.
intro Hin.
unfold ideal.
constructor.
intros.
unfold principal_ideal.
unfold principal_ideal in H.
unfold principal_ideal in H0.
destruct H.
destruct H0.
exists (plus X x1 x2).
rewrite mult_rev.
rewrite mult_dist.
destruct H.
destruct H0.
rewrite H1.
rewrite H2.
rewrite (mult_rev X x1 x).
rewrite (mult_rev X x2 x).
split.
apply in_plus.
trivial.
trivial.
reflexivity.
trivial. trivial. trivial. trivial.
destruct H. destruct H0. trivial.
destruct H. destruct H0. trivial.
destruct H. destruct H0. trivial.
apply in_plus.
destruct H. destruct H0. trivial.
destruct H. destruct H0. trivial.
trivial.
split.
intros.
unfold principal_ideal in H0.
unfold principal_ideal.
destruct H0.
destruct H0.
exists (mult X x0 x1).
rewrite H1.
rewrite mult_assoc.
split.
apply in_mult.
trivial.
trivial.
reflexivity.
trivial.
trivial.
trivial.
exists x.
unfold In.
unfold principal_ideal.
exists (one X).
rewrite mult_rev.
rewrite mult_one.
split.
apply in_one.
reflexivity.
trivial.
apply in_one.
trivial.
Qed.

Proposition unit_principal_ideal_full_set : forall (X : Ring) (x : T) (P : number X x), (unit X x) <-> (principal_ideal X x) = number X.
Proof.
intros.
unfold principal_ideal.
split.
intros.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
destruct H0.
destruct H0.
rewrite H1.
apply in_mult. trivial. trivial.
unfold In.
intros.
destruct H.
destruct H.
exists (mult X x0 x1).
split.
apply in_mult. trivial. trivial.
rewrite (mult_assoc X x0 x1 x).
rewrite (mult_rev X x1 x).
rewrite H1.
rewrite mult_one.
reflexivity.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
intros.
unfold unit.
assert (number X (one X)).
apply in_one.
rewrite <- H in H0.
destruct H0.
destruct H0.
exists x0.
split.
trivial.
rewrite H1.
rewrite (mult_rev X _ _).
trivial.
trivial.
trivial.
Qed.

Proposition principal_ideal_included : forall (X : Ring)
  (a : Ensemble T) (t : T) (Pinc : Included _ a (number X)),
  ideal X a Pinc -> number X t -> a t -> Included _ (principal_ideal X t) a.
Proof.
intros.
unfold Included.
intros.
unfold In.
unfold In in H2.
unfold principal_ideal in H2.
destruct H2.
unfold ideal in H.
destruct H.
destruct H3.
destruct H2.
rewrite H5.
apply H3.
trivial.
trivial.
Qed.

Definition field := (fun (X : Ring) => one X <> zero X
  /\ forall x : T, number X x -> x <> zero X -> unit X x).

Definition homomorphism := (fun (X : Ring) (Y : Ring) (f : T -> T) =>
  (forall x, number X x -> number Y (f x)) /\
  (forall x y, number X x -> number X y -> f(plus X x y) = plus Y (f x) (f y)) /\
  (forall x y, number X x -> number X y -> f(mult X x y) = mult Y (f x) (f y)) /\
  (f(one X) = one Y)
).

Proposition prop_homomorphism_zero : forall (X : Ring) (Y : Ring) (F : T -> T),
  homomorphism X Y F -> F (zero X) = (zero Y).
Proof.
intros.
unfold homomorphism in H.
destruct H.
destruct H0.
destruct H1.
rename H into Hin.
rename H0 into H.
rename H1 into H0.
rename H2 into H1.
assert (H2 := H1).
rewrite <- (plus_zero X (one X)) in H2.
rewrite H in H2.
rewrite H1 in H2.
apply (f_equal (fun t => plus Y t (inv Y (one Y)))) in H2.
rewrite plus_inv in H2.
rewrite plus_rev in H2.
rewrite <- plus_assoc in H2.
rewrite (plus_rev Y (inv Y (one Y)) (one Y)) in H2.
rewrite plus_inv in H2.
rewrite plus_rev in H2.
rewrite plus_zero in H2.
apply H2.
rewrite plus_zero in H2.
rewrite H2.
apply in_zero.
apply Hin.
apply in_zero.
apply in_zero.
apply Hin.
apply in_zero.
apply in_one.
apply in_inv.
apply in_one.
apply in_one.
apply in_inv.
apply in_one.
apply in_one.
apply Hin.
apply in_zero.
apply in_plus.
apply in_one.
apply Hin.
apply in_zero.
apply in_inv.
apply in_one.
apply in_one.
apply in_one.
apply in_zero.
apply in_one.
Qed.

Definition kernel := (fun (X : Ring) (Y : Ring) (F : number X -> number Y) => (fun t => F t = zero)).

Arguments kernel {X Y}.

Proposition prop_hom_inv : forall (X : Ring) (Y : Ring) (F : number X -> number Y), homomorphism F -> forall t, inv (F t) = F (inv t).
Proof.
intros.
assert (HHom := H).
unfold homomorphism in H.
destruct H.
destruct H0.
assert (zero = plus (F t) (F (inv t))).
rewrite <- H.
rewrite plus_inv.
rewrite prop_homomorphism_zero.
reflexivity.
apply HHom.
apply (f_equal (fun v => plus v (inv (F t)))) in H2.
rewrite plus_rev in H2.
rewrite plus_zero in H2.
rewrite plus_assoc in H2.
rewrite plus_rev in H2 at 1.
rewrite plus_assoc in H2.
rewrite (plus_rev (inv (F t)) (F t)) in H2.
rewrite plus_inv in H2.
rewrite plus_zero in H2.
trivial.
Qed.

Proposition prop_1_2_a4 : forall (X : Ring) (Y : Ring) (F : number X -> number Y), homomorphism F -> kernel F = Singleton (number X) zero -> injective F.
Proof.
intros.
assert (HHom := H).
unfold injective.
intros.
unfold kernel in H0.
unfold homomorphism in H.
destruct H.
destruct H2.
apply (f_equal (fun t => plus t (inv (F y)))) in H1.
rewrite plus_inv in H1.
rewrite (prop_hom_inv) in H1.
rewrite <- H in H1.
assert (plus x (inv y) = zero).
assert ((fun t : number X => F t = zero) (plus x (inv y))).
trivial.
rewrite H0 in H4.
destruct H4.
reflexivity.
apply (f_equal (fun v => plus v y)) in H4.
rewrite plus_assoc in H4.
rewrite (plus_rev (inv y) y) in H4.
rewrite plus_inv in H4.
rewrite (plus_rev zero y) in H4.
rewrite plus_zero in H4.
rewrite plus_zero in H4.
trivial.
trivial.
Qed.

Definition ring_nonzero := (fun X => exists x : number X, x <> zero).
Definition ring_zero := (fun X => forall x : number X, x = zero).

Require Import Coq.Logic.Classical_Pred_Type.

Proposition no_empty_exists : forall (T : Type) (a : Ensemble T), a <> Empty_set _ -> exists l, a l.
intros.
apply not_all_not_ex.
intro.
apply H.
apply Extensionality_Ensembles.
red.
split.
intro.
intro.
apply False_ind.
apply ((H0 x) H1).
intro.
intro.
destruct H1.
Qed.

Proposition no_empty_no_singleton_element : forall (T : Type) (a : Ensemble T) (k : T), a <> Empty_set _ -> a <> Singleton _ k -> exists l, a l /\ l <> k.
intros.
apply not_all_not_ex.
intro.
assert (exists e, a e).
apply no_empty_exists.
trivial.
destruct H2.
apply H0.
apply Extensionality_Ensembles.
red.
split.
intro.
intro.
assert (H4 := H1 x0).
apply NNPP.
intro.
apply H4.
split.
trivial.
intro.
rewrite H6 in H5.
apply H5.
constructor.
intro.
intro.
rewrite H3 in H1.
case (classic (x = x0)).
intro.
rewrite H4 in H2.
trivial.
intro.
apply False_ind.
apply (H1 x).
auto.
Qed.

Proposition prop_1_2_1 : forall (X : Ring), field X -> forall (a :  Ensemble (number X)), ideal a -> (a = Singleton (number X) zero \/ a = Full_set (number X)).
Proof.
intros.
assert (ide := H0).
unfold ideal in H0.
unfold field in H.
destruct H.
unfold unit in H1.
case (classic (a = Singleton (number X) zero)).
intros.
left.
trivial.
intros.
right.
destruct H0.
destruct H3.
assert (a <> Empty_set _).
intro.
rewrite H5 in H4.
destruct H4.
destruct H4.
assert (H6 := no_empty_no_singleton_element H5 H2).
destruct H6.
destruct H6.
apply Extensionality_Ensembles.
red.
split.
intro.
intro.
constructor.
assert (principal_ideal x = Full_set (number X)).
apply unit_principal_ideal_full_set.
auto.
rewrite <- H8.
apply principal_ideal_included.
trivial.
trivial.
Qed.

Proposition prop_1_2_2 :  forall (X : Ring), (forall a : Ensemble(number X), ideal a -> (a = Singleton (number X) zero \/ a = Full_set (number X))) -> forall (Y : Ring) (F : number X -> number Y), (exists (t : number Y), t <> zero) -> homomorphism F -> injective F.
Proof.
intros.
assert (HomF := H1).
destruct H1.
destruct H2.
destruct H0.
assert (H5 := H (kernel F)).
assert (ideal (kernel F)).
unfold ideal.
constructor.
intros.
unfold kernel.
rewrite H1.
rewrite H4.
rewrite H6.
apply plus_zero.
split.
intros.
unfold kernel.
rewrite H2.
rewrite H4.
apply prop_mult_zero.
exists zero.
apply prop_homomorphism_zero.
apply HomF.
assert (H6 := H5 H4).
case H6.
intro.
apply (prop_1_2_a4).
trivial.
trivial.
unfold injective.
unfold kernel.
intros.
assert (Full_set (number X) one).
apply Full_intro.
rewrite <- H7 in H9.
rewrite H3 in H9.
rewrite <- (mult_one x) in H0.
rewrite H9 in H0.
rewrite prop_mult_zero in H0.
apply False_ind.
apply H0.
reflexivity.
Qed.

Proposition prop_one_eq_zero : forall (X : Ring), (one : number X) = zero -> ring_zero X.
Proof.
intros.
intro.
assert (mult x one = mult x one).
reflexivity.
rewrite H in H0 at 2.
rewrite mult_one in H0.
rewrite prop_mult_zero in H0.
trivial.
Qed.

Proposition prop_ring_zero_nonzero_contradiction : forall (X : Ring), ring_nonzero X -> ring_zero X -> False.
Proof.
intros.
destruct H.
assert (H1 := H0 x).
apply (H H1).
Qed.

Proposition prop_1_2_3 : forall (X : Ring), ring_nonzero X -> (forall (Y : Ring) (F : number X -> number Y), (ring_nonzero Y) -> homomorphism F -> injective F) -> field X.
Proof.
intros.
constructor.
intro.
assert (H2 := prop_one_eq_zero X H1).
apply (prop_ring_zero_nonzero_contradiction H H2).
intros.
unfold unit.
unfold injective in H0.
apply not_all_not_ex.
intro.
apply H1.




assert (H3 := H0 (quotient_ring X (principal_ideal x)) (fun x => mkQuot _ x)).
simpl in H3.
unfold principal_ideal in H3.
unfold ring_nonzero in H3.
unfold quotient_ring in H3.
simpl in H3.
apply H1.
apply H3.
clear H3.
exists (mkQuot _ x).
unfold quotient_zero.
intro.
assert (H4 := f_equal (fun t => deQuot t) H3).
simpl in H4.
contradiction.
unfold homomorphism.
simpl.
split.
intros.
reflexivity.
split.
intros.
reflexivity.
unfold quotient_one.
reflexivity.
