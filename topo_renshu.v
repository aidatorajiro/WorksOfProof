Require Import Ensembles.

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

Lemma open_indexed_union: forall {X:TopologicalSpace} {A:Type}
  (F:IndexedFamily A (point_set X)),
  (forall a:A, open (F a)) -> open (IndexedUnion F).
Proof.
intros.
assert (IndexedUnion F = FamilyUnion (fun u => exists a:A, F a = u)).
apply Extensionality_Ensembles.
unfold Same_set.
unfold Included.
constructor.
intros.
induction H0.
apply (family_union_intro (fun u : Ensemble (point_set X) => exists a0 : A, F a0 = u) (F a)).
exists a.
reflexivity.
trivial.
intros.
induction H0.
destruct H0.
apply (indexed_union_intro F x0).
rewrite H0.
trivial.
rewrite H0.
apply open_family_union.
intros.
destruct H1.
rewrite <- H1.
apply (H x).
Qed.