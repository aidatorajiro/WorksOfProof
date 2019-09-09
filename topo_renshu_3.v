Require Import Ensembles.
Require Import Finite_sets.
Require Import ClassicalChoice.
Require Import Classical_Pred_Type.
Require Import Classical_Prop.

Arguments In {U}.
Arguments Included {U}.
Arguments Singleton {U}.
Arguments Union {U}.
Arguments Add {U}.
Arguments Intersection {U}.
Arguments Couple {U}.
Arguments Triple {U}.
Arguments Complement {U}.
Arguments Setminus {U}.
Arguments Subtract {U}.
Arguments Disjoint {U}.
Arguments Inhabited {U}.
Arguments Strict_Included {U}.
Arguments Same_set {U}.
Arguments Extensionality_Ensembles {U}.
Arguments Empty_set {U}.
Arguments Full_set {U}.

Set Implicit Arguments.

Inductive invertible {X Y:Type} (f:X->Y) : Prop :=
  | intro_invertible: forall g:Y->X,
  (forall x:X, g (f x) = x) -> (forall y:Y, f (g y) = y) ->
  invertible f.

Inductive FiniteT : Type -> Prop :=
  | empty_finite: FiniteT False
  | add_finite: forall T:Type, FiniteT T -> FiniteT (option T)
  | bij_finite: forall (X Y:Type) (f:X->Y), FiniteT X ->
    invertible f -> FiniteT Y.

Section Families.

Variable T:Type.
Definition Family := Ensemble (Ensemble T).
Variable F:Family.

Inductive FamilyUnion: Ensemble T :=
  | family_union_intro: forall (S:Ensemble T) (x:T),
    In F S -> In S x -> In FamilyUnion x.

Inductive FamilyIntersection: Ensemble T :=
  | family_intersection_intro: forall x:T,
    (forall S:Ensemble T, In F S -> In S x) ->
    In FamilyIntersection x.

End Families.

Section FamiliesFact.

Variable T:Type.

Lemma empty_family_union: FamilyUnion (@Empty_set (Ensemble T)) =
                          Empty_set.
Proof.
apply Extensionality_Ensembles.
unfold Same_set.
constructor.
unfold Included.
intros.
destruct H.
destruct H.
unfold Included.
intros.
destruct H.
Qed.

End FamiliesFact.

Section IndexedFamilies.

Variable A T:Type.
Definition IndexedFamily := A -> Ensemble T.
Variable F:IndexedFamily.

Inductive IndexedUnion : Ensemble T :=
  | indexed_union_intro: forall (a:A) (x:T),
    In (F a) x -> In IndexedUnion x.

Inductive IndexedIntersection : Ensemble T :=
  | indexed_intersection_intro: forall (x:T),
    (forall a:A, In (F a) x) -> In IndexedIntersection x.

End IndexedFamilies.

Record TopologicalSpace : Type := {
  point_set : Type;
  open : Ensemble point_set -> Prop;
  open_family_union : forall F : Family point_set,
    (forall S : Ensemble point_set, In F S -> open S) ->
    open (FamilyUnion F);
  open_intersection2: forall U V:Ensemble point_set,
    open U -> open V -> open (Intersection U V);
  open_full : open Full_set
}.

Arguments open {t}.
Arguments open_family_union {t}.
Arguments open_intersection2 {t}.


Lemma open_empty: forall X:TopologicalSpace,
  open (@Empty_set (point_set X)).
Proof.
intro.
induction X.
assert (forall S : Ensemble point_set0, In Empty_set S -> False).
intros.
destruct H.
assert (H0 := open_family_union0 Empty_set (fun x y => False_ind (open0 x) (H x y))).
rewrite <- empty_family_union.
apply H0.
Qed.

Lemma open_union2: forall {X:TopologicalSpace}
  (U V:Ensemble (point_set X)), open U -> open V -> open (Union U V).
Proof.
intros.
assert (Union U V = FamilyUnion (Couple U V)).
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
induction H1.
apply (family_union_intro (Couple U V) U).
intuition.
apply H1.
apply (family_union_intro (Couple U V) V).
intuition.
apply H1.
intros.
induction H1.
induction H1.
intuition.
intuition.
rewrite H1.
apply open_family_union.
intros.
induction H2.
trivial.
trivial.
Qed.

Lemma indexed_union_to_family_union: forall {A T:Type}  (F:IndexedFamily A T),
    IndexedUnion F = FamilyUnion (fun u => exists a:A, F a = u).
intros.
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
induction H.
apply (family_union_intro (fun u : Ensemble T => exists a0 : A, F a0 = u) (F a)).
exists a.
reflexivity.
trivial.
intros.
induction H.
destruct H.
apply (indexed_union_intro F x0).
rewrite H.
trivial.
Qed.

Lemma open_indexed_union: forall {X:TopologicalSpace} {A:Type}
  (F:IndexedFamily A (point_set X)),
  (forall a:A, open (F a)) -> open (IndexedUnion F).
Proof.
intros.
rewrite indexed_union_to_family_union.
apply open_family_union.
intros.
destruct H0.
rewrite <- H0.
apply (H x).
Qed.

Lemma open_finite_indexed_intersection:
  forall {X:TopologicalSpace} {A:Type}
    (F:IndexedFamily A (point_set X)),
    FiniteT A -> (forall a:A, open (F a)) ->
    open (IndexedIntersection F).
Proof.
intros.
induction H.
assert (IndexedIntersection F = Full_set).
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
apply Full_intro.
intros.
constructor.
intro.
contradiction.
rewrite H.
apply open_full.
assert(IndexedIntersection F = Intersection (F None) (IndexedIntersection (fun x : T => F (Some x)))).
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
induction H1.
apply Intersection_intro.
apply H1.
constructor.
intros.
apply H1.
intros.
induction H1.
induction H2.
constructor.
intro.
induction a.
apply H2.
apply H1.
rewrite H1.
apply open_intersection2.
apply H0.
apply (IHFiniteT (fun x => F (Some x)) (fun x => H0 (Some (x)))).
induction H1.
assert(IndexedIntersection F = IndexedIntersection (fun x : X0 => F (f x))).
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
induction H3.
constructor.
intro.
apply H3.
intros.
induction H3.
constructor.
intro.
assert (H4 := H3 (g a)).
rewrite (H2 a) in H4.
trivial.
rewrite H3.
apply IHFiniteT.
intros.
apply H0.
Qed.

Set Asymmetric Patterns.

Definition compact (X:TopologicalSpace) :=
  forall C:Family (point_set X),
    (forall U:Ensemble (point_set X), In C U -> open U) ->
    FamilyUnion C = Full_set ->
    exists C':Family (point_set X),
      Finite _ C' /\ Included C' C /\
      FamilyUnion C' = Full_set.

(*
Lemma sig_index_finite:
  forall (A B : Type) (x : Family B), (Finite (Ensemble B) x) -> forall (f : {e | In x e} -> A), Finite A (fun i => exists e, f e = i).
intros.
induction H.
assert ((fun i : A => exists e : {e : Ensemble B | In Empty_set e}, f e = i) = Empty_set).
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
unfold In in H.
destruct H.
destruct x0.
contradiction.
intros.
contradiction.
rewrite H.
apply Empty_is_finite.

assert (In (Add A0 x) x).
apply Union_intror.
apply In_singleton.

assert (forall e, In A0 e -> In (Add A0 x) e).
intros.
apply Union_introl.
apply H2.

set (f' := (fun e : {e : Ensemble B | In A0 e} => f (exist (fun e => In (Add A0 x) e) (proj1_sig e) (H2 (proj1_sig e) (proj2_sig e))))).
assert ((fun i : A => exists e : {e : Ensemble B | In (Add A0 x) e}, f e = i)
   = Add (fun i : A => exists e : {e : Ensemble B | In A0 e}, f' e = i)
      (f (exist (fun e => In (Add A0 x) e) x H1))).
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
unfold In in H3.
destruct H3.
destruct x1.
destruct a.
apply Union_introl.
unfold In.
exists (exist (fun e => A0 e) x1 i).
unfold f'.
simpl.
*)

Lemma compactness_on_indexed_covers:
  forall (X:TopologicalSpace) (A:Type) (C:IndexedFamily A (point_set X)),
    compact X ->
    (forall a:A, open (C a)) -> IndexedUnion C = Full_set ->
  exists A':Ensemble A, Finite _ A' /\
    IndexedUnion (fun a':{a':A | In A' a'} => C (proj1_sig a')) = Full_set.
Proof.
intros.
unfold compact in H.
unfold Included in H.
rewrite (indexed_union_to_family_union C) in H1.

assert (exists C' : Family (point_set X),
      Finite (Ensemble (point_set X)) C' /\ Included C' (fun u : Ensemble (point_set X) => exists a : A, C a = u) /\ FamilyUnion C' = Full_set).
apply H.
intros.
destruct H2.
assert (H3 := H0 x).
rewrite H2 in H3.
apply H3.
apply H1.

destruct H2.
destruct H2.
destruct H3.
unfold Included in H3.
unfold In in H3.

clear H.
clear H0.

assert (exists f : Ensemble (point_set X) -> A, (forall e : Ensemble (point_set X), C (f e) = e)).
apply (choice (fun (e :  Ensemble (point_set X)) (i : A) => C i = e)).
intro.
destruct x0.
destruct (H3 x0).
apply i.
exists x1.
simpl.
apply H.
destruct H.

rename x0 into f.

exists (fun i => exists e, f e = i).
constructor.
