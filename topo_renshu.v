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

Definition closed {X:TopologicalSpace} (F:Ensemble (point_set X)) :=
  open (Ensembles.Complement F).

Lemma union_is_finite_strong:
  forall (U:Type) (A:Ensemble U),
        Finite U A -> forall x:U, Finite U (Add A x).
Proof.
intros.
assert(H0 := classic (In A x)).
destruct H0.
assert (Add A x = A).
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
destruct H1.
apply H1.
destruct H1.
apply H0.
intros.
apply Union_introl.
apply H1.
rewrite H1.
apply H.
apply (Union_is_finite U A H x H0).
Qed.

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

set (H1 := (Union_intror (Ensemble B) A0 (Singleton x) x) (In_singleton (Ensemble B) x)).

set (H2 := (fun e h => Union_introl (Ensemble B) A0 (Singleton x) e h) : forall e, In A0 e -> In (Add A0 x) e).

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
apply H3.
unfold In.
apply Union_intror.
unfold In.
unfold H1.
destruct i.
rewrite H3.
apply In_singleton.
intros.

destruct H3.

destruct H3.
destruct x1.
unfold In.
set (H4 := Union_introl (Ensemble B) A0 (Singleton x) x1 i).
exists(exist (fun e => In (Add A0 x) e) x1 H4).
apply H3.

unfold In.
exists (exist (fun e : Ensemble B => In (Add A0 x) e) x H1).
destruct H3.
reflexivity.

rewrite H3.
apply union_is_finite_strong.
apply IHFinite.
Qed.

Lemma map_finite:
  forall (X Y : Type) (A : Ensemble X) (F : X -> Y), Finite X A -> Finite Y (fun x => exists e : {e | In A e}, x = F (proj1_sig e)).
Proof.
intros.
induction H.
assert ((fun x : Y => exists e : {e : X | In Empty_set e}, x = F (proj1_sig e)) = Empty_set).
apply Extensionality_Ensembles; constructor; red; intros.
destruct H.
destruct x0.
contradiction.
contradiction.
rewrite H.
constructor.

assert ((fun x0 : Y => exists e : {e : X | In (Add A x) e}, x0 = F (proj1_sig e))
  = Add (fun x0 : Y => exists e : {e : X | In A e}, x0 = F (proj1_sig e)) (F x)).
apply Extensionality_Ensembles; constructor; red; intros.
destruct H1.
destruct x1.
destruct i.
unfold proj1_sig in H1.
left.
exists (exist _ x1 i).
rewrite H1; reflexivity.
unfold proj1_sig in H1.
right.
induction i.
induction H1.
constructor.

induction H1.
destruct H1.
destruct x1.
assert (In (Add A x) x1).
left.
apply i.
exists (exist _ x1 H2).
rewrite H1.
reflexivity.
assert (In (Add A x) x).
right.
constructor.
exists (exist _ x H2).
induction H1; reflexivity.

rewrite H1.
apply union_is_finite_strong.
apply IHFinite.
Qed.

Lemma singleton_is_finite:
  forall (X : Type) (a : X), Finite X (Singleton a).
Proof.
intros.
assert (Singleton a = Add Empty_set a).
apply Extensionality_Ensembles; constructor; red; intros.
right.
apply H.
destruct H.
contradiction.
apply H.
rewrite H.
constructor.
constructor.
intro.
contradiction.
Qed.

Lemma prop_finite:
  forall (X : Type) (A : Ensemble X) (P : X -> Prop), Finite X A -> Finite X (fun x => P x /\ exists e : {e | In A e}, x = proj1_sig e).
intros.
induction H.
assert ((fun x => P x /\ (exists e : {e : X | In Empty_set e}, x = proj1_sig e)) = Empty_set).
apply Extensionality_Ensembles; constructor; red; intros.
destruct H.
destruct H0.
destruct x0.
contradiction.
contradiction.
rewrite H.
constructor.

destruct (classic (P x)).

assert ((fun x0 : X => P x0 /\ (exists e : {e : X | In (Add A x) e}, x0 = proj1_sig e))
  = Add (fun x0 : X =>P x0 /\ (exists e : {e : X | In A e}, x0 = proj1_sig e)) x).
apply Extensionality_Ensembles; constructor; red; intros.
destruct H2.
destruct H3.
destruct x1.
destruct i.
left.
constructor.
trivial.
exists (exist _ x1 i).
rewrite H3; reflexivity.
right.
rewrite i; rewrite H3; reflexivity.
destruct H2.
destruct H2.
destruct H3.
constructor.
trivial.
destruct x1.
assert (In (Add A x) x1).
left; apply i.
exists (exist _ x1 H4).
rewrite H3; reflexivity.
destruct H2.
red.
constructor.
trivial.
assert (In (Add A x) x).
right; constructor.
exists (exist _ x H2); reflexivity.
rewrite H2.
apply union_is_finite_strong.
apply IHFinite.

assert ((fun x0 : X => P x0 /\ (exists e : {e : X | In (Add A x) e}, x0 = proj1_sig e))
  = (fun x0 : X =>P x0 /\ (exists e : {e : X | In A e}, x0 = proj1_sig e))).
apply Extensionality_Ensembles; constructor; red; intros.
destruct H2.
destruct H3.
destruct x1.
destruct i.
constructor.
trivial.
exists (exist _ x1 i).
rewrite H3; reflexivity.
destruct i.
rewrite H3 in H2; simpl in H2.
contradiction.
destruct H2.
constructor.
trivial.
destruct H3.
destruct x1.
unfold proj1_sig in H3.
destruct H3.
assert (In (Add A x) x0).
left; trivial.
exists (exist _ x0 H3); reflexivity.
rewrite H2; apply IHFinite.
Qed.

Lemma intersection_complement_complement_union:
  forall (T : Type)(A : Family T), FamilyIntersection (fun x => exists e : {e | In A e}, x = Complement (proj1_sig e)) = Complement (FamilyUnion A).
intros.
apply Extensionality_Ensembles; constructor; red; intros.
destruct H.
intro.
destruct H0.
assert(In (Complement S) x).
apply H.
exists (exist _ S H0).
simpl.
reflexivity.
contradiction.
constructor.
intros.
destruct H0.
destruct x0.
simpl in H0.
rewrite H0.
intro.
apply H.
exists x0.
trivial.
trivial.
Qed.

Lemma complement_full_set_equal_empty_set :
  forall (A : Type), Complement Full_set = (Empty_set : Ensemble A).
intros.
apply Extensionality_Ensembles; constructor; red; intros.
unfold Complement in H.
unfold In in H.
destruct H.
constructor.
contradiction.
Qed.

Lemma complement_empty_set_equal_full_set :
  forall (A : Type), Complement Empty_set = (Full_set : Ensemble A).
intros.
apply Extensionality_Ensembles; constructor; red; intros.
constructor.
intro.
contradiction.
Qed.

Lemma complement_complement_x_equal_x :
  forall (A : Type) (x : Ensemble A), Complement (Complement x) = x.
Proof.
intros.
apply Extensionality_Ensembles; constructor; red; intros.
unfold Complement in H.
unfold In in H.
apply (NNPP _ H).
assert (~ ~ In x x0); intro; contradiction.
Qed.

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

assert (exists f : {e : Ensemble (point_set X) | In x e} -> A, (forall e : {e : Ensemble (point_set X) | In x e}, C (f e) = proj1_sig e)).
apply (choice (fun (e :  {e : Ensemble (point_set X) | In x e}) (i : A) => C i = proj1_sig e)).
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

apply sig_index_finite.
apply H2.

apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
rewrite <- H1.
destruct H0.
destruct a.
unfold proj1_sig in H0.
apply (family_union_intro (fun u : Ensemble (point_set X) => exists a : A, C a = u) (C x1)).
unfold In.
exists x1.
reflexivity.
apply H0.
intros.

unfold In.
rewrite <- H4 in H0.
destruct H0.
set (eS := exist (fun e => In x e) S H0).
set (fS := f (eS)).
assert (exists e, f e = fS).
exists (eS).
trivial.
exists (exist (fun a' => exists e, f e = a') fS H6).
unfold In.
unfold proj1_sig.
unfold fS.
rewrite (H eS).
unfold eS.
unfold proj1_sig.
apply H5.
Qed.


Lemma compact_finite_nonempty_closed_intersection:
  forall X:TopologicalSpace, compact X ->
  forall F:Family (point_set X),
    (forall G:Ensemble (point_set X), In F G -> closed G) ->
    (forall F':Family (point_set X), Finite _ F' -> Included F' F ->
     Inhabited (FamilyIntersection F')) ->
    Inhabited (FamilyIntersection F).
Proof.
intros X Hcompact F  Hclosed Hinhabited.
set (Fc := (fun x => exists e : {e | In F e}, x = Complement (proj1_sig e))).
assert (FamilyUnion Fc <> Full_set).
intro.
rename H into union_full.
unfold compact in Hcompact.

assert (exists C' : Family (point_set X),
             Finite (Ensemble (point_set X)) C' /\
             Included C' Fc /\ FamilyUnion C' = Full_set).
apply Hcompact.
intros.
destruct H.
destruct x.
rewrite H.
apply (Hclosed x i).
apply union_full.
destruct H.
destruct H.
destruct H0.
rename x into Fc'.
rename H into Finite_Fc'.
rename H0 into Included_Fc'.
rename H1 into Full_Fc'.
set (F' := (fun x => exists e : {e | In Fc' e}, x = Complement (proj1_sig e))).
assert (Finite_F' : Finite _ F').
apply map_finite.
trivial.
assert (Included F' F).
intro.
intro.
destruct H.
destruct x0.
simpl in H.
assert (H0 := Included_Fc' _ i).
destruct H0.
destruct x1.
simpl in H0.
rewrite H0 in H.
rewrite (complement_complement_x_equal_x) in H.
rewrite H.
apply i0.
rename H into Included_F'.
assert (H := Hinhabited _ Finite_F' Included_F').
unfold F' in H.
rewrite intersection_complement_complement_union in H.
rewrite Full_Fc' in H.
rewrite complement_full_set_equal_empty_set in H.
destruct H.
contradiction.

apply NNPP.
intro.
assert (FamilyIntersection F = Empty_set).
apply Extensionality_Ensembles; constructor; red; intros.
assert (Inhabited (FamilyIntersection F)).
exists x.
trivial.
contradiction.
contradiction.

apply H.
rewrite <- complement_empty_set_equal_full_set.
rewrite <- H1.


assert (~ (exists x, forall S, In F S -> In S x)).

assert (FamilyUnion Fc = Full_set).
apply Extensionality_Ensembles; constructor; red; intros.
constructor.

rewrite <- complement_empty_set_equal_full_set.
rewrite <- H1.
apply Extensionality_Ensembles; constructor; red; intros.
intro.
rewrite H1 in  H3.
contradiction.
unfold In, Complement  in H2.
apply NNPP.
intro.
apply H2.
constructor.
intros.
destruct H3.
exists (Complement S).
unfold Fc.
unfold In.
exists (exist _ S H4).
simpl.
reflexivity.
