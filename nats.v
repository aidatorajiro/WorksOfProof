Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Compute (minustwo 4).

Example test_oddb1: oddb 1 = true
 := eq_refl.

Example test_oddb2: oddb 4 = false
 := eq_refl.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Notation "x + y" := (plus x y)
  (at level 50, left associativity)
  : nat_scope.
Notation "x - y" := (minus x y)
  (at level 50, left associativity)
  : nat_scope.
Notation "x * y" := (mult x y)
  (at level 40, left associativity)
  : nat_scope.

Compute (6 * 7).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
    | O => true
    | S m' => false
    end
  | S n' => match m with
    | O => false
    | S m' => beq_nat n' m'
    end
  end.

Compute beq_nat 8 8.

Proposition prop1 : forall x : nat, beq_nat x x = true.
intro.
simpl.
induction x.
simpl.
reflexivity.
simpl.
apply IHx.
Qed.

Proposition prop2 : forall x y : nat, x = y <-> beq_nat x y = true.
intros.
split.
intros.
replace y with x.
apply prop1.
intros.
induction x.
assert (beq_nat 0 y = true -> 0 = y).
simpl.
case y.
reflexivity.
intros.
discriminate.
apply (H0 H).

Proposition prop3 : forall x : nat, beq_nat (x + 1) (1 + x) = true.
intro.
simpl.
induction x.
simpl.
reflexivity.
simpl.
apply IHx.
Qed.