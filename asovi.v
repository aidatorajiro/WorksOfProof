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

Definition Blockchain : TopologicalSpace := {
  
}.

Definition compact (X:TopologicalSpace) :=
  forall C:Family (point_set X),
    (forall U:Ensemble (point_set X), In C U -> open U) ->
    FamilyUnion C = Full_set ->
    exists C':Family (point_set X),
      Finite _ C' /\ Included C' C /\
      FamilyUnion C' = Full_set.