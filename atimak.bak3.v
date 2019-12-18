Require Import Ensembles.



Record Ring : Type := mkRing {
  number : Type;
  plus : number -> number -> number;
  mult : number -> number -> number;
  zero : number;
  one : number;
  inv : number -> number;
  plus_inv : forall n : number, plus n (inv n) = zero;
  plus_zero : forall n : number, plus n zero = n;
  plus_assoc : forall (a : number) (b : number) (c : number), plus (plus a b) c = plus a (plus b c);
  plus_rev : forall (a : number) (b : number), plus a b = plus b a;
  mult_assoc : forall (a : number) (b : number) (c : number), mult (mult a b) c = mult a (mult b c);
  mult_dist : forall (a : number) (b : number) (c : number), mult a (plus b c) = plus (mult a b) (mult a c);
  mult_rev : forall (a : number) (b : number), mult a b = mult b a;
  mult_one : forall (a : number), mult a one = a;
}.

Set Implicit Arguments.

Arguments plus {r}.
Arguments mult {r}.
Arguments zero {r}.
Arguments one {r}.
Arguments inv {r}.
Arguments plus_inv {r}.
Arguments plus_zero {r}.
Arguments plus_assoc {r}.
Arguments plus_rev {r}.
Arguments mult_assoc {r}.
Arguments mult_dist {r}.
Arguments mult_rev {r}.
Arguments mult_one {r}.

Proposition prop_mult_zero : forall (X : Ring) (x : number X), mult x zero = zero.
Proof.
intros.
assert (mult (plus zero zero) x = mult zero x).
rewrite (plus_zero zero).
reflexivity.
rewrite (mult_rev) in H.
rewrite (mult_dist) in H.
assert (plus (plus (mult x zero) (mult x zero)) (inv (mult x zero)) = plus (mult zero x) (inv (mult zero x))).
rewrite H.
rewrite (mult_rev x zero).
reflexivity.
rewrite (plus_assoc (mult x zero) (mult x zero) (inv (mult x zero))) in H0.
rewrite (plus_inv (mult x zero)) in H0.
rewrite (plus_zero) in H0.
rewrite plus_inv in H0.
trivial.
Qed.

Proposition prop_mult_inv : forall (X : Ring) (x : number X), mult x (inv one) = inv x.
Proof.
intros.
assert (H := prop_mult_zero X x).
rewrite <- (plus_inv one) in H at 1.
rewrite <- (plus_inv x) in H at 1.
rewrite mult_dist in H.
apply (f_equal (fun t => plus (inv x) t)) in H.
rewrite (mult_one) in H.
rewrite <- (plus_assoc) in H.
rewrite (plus_rev (inv x) x) in H.
rewrite plus_inv in H.
rewrite (plus_rev) in H.
rewrite (plus_zero) in H.
rewrite (plus_zero) in H.
trivial.
Qed.

Definition principal_ideal := (fun (X : Ring) (x : number X) => (fun a => exists k : number X, a = mult k x)).

Definition ideal := (fun (X : Ring) (a : Ensemble (number X)) => (forall x y, a x -> a y -> a (plus x y)) /\ (forall x y, a y -> a (mult x y)) /\ Inhabited (number X) a).

Definition unit := (fun (X : Ring) (a : number X) => exists b, mult a b = one).

Arguments principal_ideal {X}.
Arguments ideal {X}.
Arguments unit {X}.

Definition injective := (fun (X : Type) (Y : Type) (F : X -> Y) => forall x y, F x = F y -> x = y).

Definition reverse := (fun (X : Type) (Y : Type) (F : X -> Y) (G : Y -> X) => forall x, F (G x) = x).

Definition mapring_plus : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T),
  T -> T -> T
:= fun X T F G X0 X1 => G (plus (F X0) (F X1)).

Definition mapring_mult : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T),
  T -> T -> T
:= fun X T F G X0 X1 => G (mult (F X0) (F X1)).

Definition mapring_zero : forall (X : Ring) (T:Type) (G : number X -> T),
  T
:= fun X T G => G zero.

Definition mapring_one : forall (X : Ring) (T:Type) (G : number X -> T),
  T
:= fun X T G => G one.

Definition mapring_inv : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T),
  T -> T
:= fun X T F G X0 => G (inv (F X0)).

Arguments mapring_plus {X T}.
Arguments mapring_mult {X T}.
Arguments mapring_zero {X T}.
Arguments mapring_one {X T}.
Arguments mapring_inv {X T}.

Proposition mapring_plus_inv : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (rev : reverse F G) (n : T),
  mapring_plus F G n (mapring_inv F G n) = mapring_zero G.
Proof.
intros.
unfold mapring_plus.
unfold mapring_inv.
unfold mapring_zero.
unfold reverse in rev.
rewrite (rev (inv (F n))).
rewrite plus_inv.
reflexivity.
Qed.

Proposition mapring_plus_zero : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (rev1 : reverse F G) (rev2 : reverse G F) (n : T),
  mapring_plus F G n (mapring_zero G) = n.
Proof.
intros.
unfold mapring_plus.
unfold mapring_zero.
rewrite (rev1 zero).
rewrite plus_zero.
rewrite rev2.
reflexivity.
Qed.

Proposition mapring_plus_assoc : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (rev : reverse F G) (p : T) (q : T) (r : T),
  mapring_plus F G (mapring_plus F G p q) r = mapring_plus F G p (mapring_plus F G q r).
Proof.
intros.
unfold mapring_plus.
rewrite rev.
rewrite rev.
rewrite plus_assoc.
reflexivity.
Qed.

Proposition mapring_plus_rev : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (p : T) (q : T),
  mapring_plus F G p q = mapring_plus F G q p.
Proof.
intros.
unfold mapring_plus.
rewrite plus_rev.
reflexivity.
Qed.

Proposition mapring_mult_assoc : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (rev : reverse F G) (p : T) (q : T) (r : T),
  mapring_mult F G (mapring_mult F G p q) r = mapring_mult F G p (mapring_mult F G q r).
Proof.
intros.
unfold mapring_mult.
rewrite rev.
rewrite rev.
rewrite mult_assoc.
reflexivity.
Qed.

Proposition mapring_mult_dist : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (rev : reverse F G) (p : T) (q : T) (r : T),
  mapring_mult F G p (mapring_plus F G q r) = mapring_plus F G (mapring_mult F G p q) (mapring_mult F G p r).
Proof.
intros.
unfold mapring_mult.
unfold mapring_plus.
rewrite rev.
rewrite rev.
rewrite rev.
rewrite mult_dist.
reflexivity.
Qed.

Proposition mapring_mult_rev : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (p : T) (q : T),
  mapring_mult F G p q = mapring_mult F G q p.
Proof.
intros.
unfold mapring_mult.
rewrite mult_rev.
reflexivity.
Qed.

Proposition mapring_mult_one : forall (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (rev1 : reverse F G) (rev2 : reverse G F) (n : T),
  mapring_mult F G n (mapring_one G) = n.
Proof.
intros.
unfold mapring_mult.
unfold mapring_one.
rewrite rev1.
rewrite mult_one.
rewrite rev2.
reflexivity.
Qed.

Arguments mapring_plus_inv {X T}.
Arguments mapring_plus_zero {X T}.
Arguments mapring_plus_assoc {X T}.
Arguments mapring_plus_rev {X T}.
Arguments mapring_mult_assoc {X T}.
Arguments mapring_mult_dist {X T}.
Arguments mapring_mult_rev {X T}.
Arguments mapring_mult_one {X T}.

Definition mapring := (fun (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (rev1 : reverse F G) (rev2 : reverse G F) =>
  mkRing
  T
  (mapring_plus F G)
  (mapring_mult F G)
  (mapring_zero G)
  (mapring_one G)
  (mapring_inv F G)
  (mapring_plus_inv F G rev1)
  (mapring_plus_zero F G rev1 rev2)
  (mapring_plus_assoc F G rev1)
  (mapring_plus_rev F G)
  (mapring_mult_assoc F G rev1)
  (mapring_mult_dist F G rev1)
  (mapring_mult_rev F G)
  (mapring_mult_one F G rev1 rev2)
).

Definition mapring_wo_rev2 := (fun (X : Ring) (T:Type) (F : T -> number X) (G : number X -> T) (rev1 : reverse F G)
    (p_plus_zero : forall n, mapring_plus F G n (mapring_zero G) = n)
    (p_mult_one : forall n, mapring_mult F G n (mapring_one G) = n) =>
  mkRing
  T
  (mapring_plus F G)
  (mapring_mult F G)
  (mapring_zero G)
  (mapring_one G)
  (mapring_inv F G)
  (mapring_plus_inv F G rev1)
  (p_plus_zero)
  (mapring_plus_assoc F G rev1)
  (mapring_plus_rev F G)
  (mapring_mult_assoc F G rev1)
  (mapring_mult_dist F G rev1)
  (mapring_mult_rev F G)
  (p_mult_one)
).

Proposition principal_ideal_is_ideal : forall (X : Ring) (x : number X), ideal (principal_ideal x).
Proof.
intros.
unfold ideal.
constructor.
intros.
unfold principal_ideal.
unfold principal_ideal in H.
unfold principal_ideal in H0.
destruct H.
destruct H0.
exists (plus x1 x2).
rewrite mult_rev.
rewrite mult_dist.
rewrite H.
rewrite H0.
rewrite (mult_rev x1 x).
rewrite (mult_rev x2 x).
reflexivity.
split.
intros.
unfold principal_ideal in H.
unfold principal_ideal.
destruct H.
exists (mult x0 x1).
rewrite H.
rewrite mult_assoc.
reflexivity.
exists x.
exists one.
rewrite mult_rev.
rewrite mult_one.
trivial.
Qed.

Proposition unit_principal_ideal_full_set : forall {X : Ring} (x : number X), (exists y, mult x y = one) <-> (principal_ideal x) = Full_set (number X).
Proof.
intros.
split.
intros.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
unfold In.
apply Full_intro.
intros.
unfold In.
destruct H.
unfold In in H0.
exists (mult x0 x1).
rewrite (mult_assoc x0 x1 x).
rewrite (mult_rev x1 x).
rewrite H.
rewrite mult_one.
reflexivity.
intros.
assert ((Full_set (number X)) one).
apply Full_intro.
rewrite <- H in H0.
destruct H0.
exists x0.
rewrite mult_rev in H0.
rewrite H0.
reflexivity.
Qed.

Proposition principal_ideal_included : forall (X : Ring) (a :  Ensemble (number X)) (t :  number X), ideal a -> a t -> Included (number X) (principal_ideal t) a.
Proof.
intros.
unfold Included.
intros.
unfold In.
unfold In in H1.
unfold principal_ideal in H1.
destruct H1.
unfold ideal in H.
destruct H.
destruct H2.
assert (H4 := H2 x0 t H0).
rewrite <- H1 in H4.
trivial.
Qed.

Definition field := (fun (X : Ring) => (one : number X) <> zero /\ forall x : number X, x <> zero -> unit x).

Definition homomorphism := (fun (X : Ring) (Y : Ring) (f : number X -> number Y) =>
  (forall (x : number X) (y : number X), f(plus x y) = plus (f x) (f y)) /\
  (forall (x : number X) (y : number X), f(mult x y) = mult (f x) (f y)) /\
  (f(one) = one)
).

Arguments homomorphism {X} {Y}.

Proposition prop_homomorphism_zero : forall (X : Ring) (Y : Ring) (F : number X -> number Y), homomorphism F -> F zero = zero.
Proof.
intros.
unfold homomorphism in H.
destruct H.
destruct H0.
assert (H2 := H1).
rewrite <- (plus_zero one) in H2.
rewrite H in H2.
rewrite H1 in H2.
apply (f_equal (fun t => plus t (inv one))) in H2.
rewrite plus_inv in H2.
rewrite plus_rev in H2.
rewrite <- plus_assoc in H2.
rewrite (plus_rev (inv one) one) in H2.
rewrite plus_inv in H2.
rewrite plus_rev in H2.
rewrite plus_zero in H2.
trivial.
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
