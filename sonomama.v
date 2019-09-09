Definition prop1: forall (n: nat), n = S n -> False
 := fix Ffix (n : nat) : n = S n -> False :=
  match n with
    | O => (fun H => match H in (_ = b) return (match b with
      | O => True
      | S _ => False
    end) with
        | eq_refl => I
      end)
    | S k => (fun H => Ffix k (match H in (_ = b) return (match b with
      | O => k = O
      | S t => k = t
    end) with
        | eq_refl => eq_refl
      end))
  end.

Require Export Rdefinitions.
Require Export Raxioms.

Local Open Scope R_scope.

Lemma tstts : forall (a : R) (b : R) (c : R), -a < b - c < a <-> -a < c - b < a.
intros.
split.
intro.
split.
destruct H.
assert (-a + (b - c) < -a + a).
apply (Rplus_lt_compat_l).
trivial.
rewrite (Rplus_comm (-a) a) in H1.
rewrite Rplus_opp_r in H1.
assert (-(b - c) + (- a + (b - c)) < -(b - c) + 0).
apply Rplus_lt_compat_l.
apply H1.
assert (- (b - c) + (- a + (b - c)) = -a).
rewrite <- Rplus_assoc.
rewrite (Rplus_comm (- (b - c))).
rewrite Rplus_assoc.
rewrite (Rplus_comm (- (b - c))).
rewrite Rplus_opp_r.
rewrite (Rplus_comm (-a)).
rewrite (Rplus_0_l).
reflexivity.
assert (- (b - c) + 0 = c - b).
unfold Rminus.
rewrite (Rplus_comm (b) (-c)).
rewrite (Rplus_comm _ 0).
rewrite (Rplus_0_l).

Definition limit (S : nat -> R) (alp : R) := forall (eps : R), eps > 0 -> exists (n : nat), forall (N : nat), (n < N)%nat -> -eps < S n - alp < eps.

Compute (gt 1 2).