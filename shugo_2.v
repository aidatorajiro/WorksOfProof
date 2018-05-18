Require Import Bool.

Notation "[ a ] < [ b ]" := (forall (F : a -> b), exists (y : b), forall (x : a), F x <> y).
Notation "[ a ] > [ b ]" := ([b] < [a]).
Notation "[ a ] = [ b ]" := (~([a] < [b]) /\ ~([a] > [b])).

Definition lemma1 : forall (A : Type)(B : Type)(F : A -> B)(G : A -> B), F = G -> forall (x : A), F x = G x
 := fun A B F G H x => f_equal (fun a : A -> B => a x) H.

Definition prop1 : forall (A : Type), [A] < [A -> bool] :=
  fun (A : Type) (F : A -> A -> bool) =>
    let AbP  := fun y => forall (x : A), F x <> y in
    let diag := fun x => negb (F x x) in
    ex_intro AbP diag (fun x H =>
      no_fixpoint_negb (F x x)
      (eq_sym (f_equal (fun a => a x) H))
    ).

Definition prop2 : forall (A : Type), [A] = [A] :=
  fun A =>
    let id : A -> A := (fun a => a) in
    let P : ~([A] < [A]) := (fun x =>
      match x id with
        | ex_intro _ y H => (H y) (eq_refl y)
      end
    ) in
    conj P P.