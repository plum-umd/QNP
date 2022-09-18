Require Import Psatz Reals.
Require Import Interval.Tactic.
Local Open Scope R_scope.

Lemma exp_lt_pow4 :
  forall n : nat, exp (INR n) <= 2^(n * 2).
Proof.
  induction n. simpl. interval.
  replace (INR (S n)) with (1 + INR n) by (destruct n; simpl; lra).
  rewrite exp_plus.
  replace ((S n) * 2)%nat with (2 + n * 2)%nat by lia.
  rewrite pow_add. replace (2^2) with 4 by (simpl; lra).
  assert (exp 1 <= 4) by (specialize exp_le_3 as G; lra).
  assert (0 < exp 1) by apply exp_pos.
  assert (0 < exp (INR n)) by apply exp_pos.
  nra.
Qed.

Lemma log_bound :
  forall n, (0 < n)%nat -> INR (Nat.log2 n) <= 2 * ln (INR n).
Proof.
  intros. rewrite <- ln_exp with (x := INR (Nat.log2 n)).
  specialize exp_lt_pow4 with (n := Nat.log2 n) as G.
  rewrite pow_mult in G.
  assert (2 ^ Nat.log2 n <= INR n).
  { replace 2 with (INR 2) by easy.
    rewrite <- pow_INR. apply le_INR.
    specialize (Nat.log2_spec n H) as T.
    easy.
  }
  assert (0 < 2 ^ Nat.log2 n).
  { replace 2 with (INR 2) by easy.
    rewrite <- pow_INR. apply lt_0_INR.
    assert (2 <> 0)%nat by easy.
    specialize (Nat.pow_nonzero _ (Nat.log2 n) H1) as T.
    lia.
  }
  replace 2 with (INR 2) by easy.
  rewrite <- Rcomplements.ln_pow by (apply lt_0_INR; easy).
  apply Rcomplements.ln_le. apply exp_pos.
  replace (INR n ^ 2) with (INR n * INR n) by (simpl; lra).
  replace ((2 ^ Nat.log2 n) ^ 2) with ((2 ^ Nat.log2 n) * (2 ^ Nat.log2 n)) in G by (simpl; lra).
  assert (2 ^ Nat.log2 n * 2 ^ Nat.log2 n <= INR n * INR n) by nra.
  lra.
Qed.
