(* Bound for Harmonic Series *)

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Psatz Misc Prod.
Require Import Reals.

Local Open Scope R_scope.
Local Coercion INR : nat >-> R.

Definition Rsum (start len : nat) (f : nat -> R) : R :=
  match len with
  | O => 0
  | S n => sum_f_R0 (fun i => f (start + i)%nat) n
  end.

Lemma Rsum_eq_bounded :
  forall start len f1 f2,
    (forall i, (start <= i < start + len)%nat -> f1 i = f2 i) -> Rsum start len f1 = Rsum start len f2.
Proof.
  intros. 
  induction len; simpl.
  reflexivity.
  destruct len; simpl.
  apply H. lia.
  simpl in IHlen. rewrite IHlen. 
  rewrite H by lia. easy.
  intros. apply H; lia.
Qed.

Lemma Rsum_extend_len :
  forall start len f,
    Rsum start (S len) f = Rsum start len f + f (start + len)%nat.
Proof.
  intros. destruct len. simpl. lra.
  simpl. lra.
Qed.

Lemma Rsum_extend_start :
  forall len start f,
    Rsum start (S len) f = Rsum (S start) len f + f (start)%nat.
Proof.
  induction len; intros. simpl. rewrite Nat.add_0_r. lra.
  rewrite Rsum_extend_len.
  rewrite IHlen. rewrite Rsum_extend_len. replace (start + S len)%nat with (S start + len)%nat by lia. lra.
Qed.

Lemma fold_left_Rplus_accum :
  forall l r,
    fold_left Rplus l r = r + fold_left Rplus l 0.
Proof.
  induction l; intros. simpl. lra.
  simpl. rewrite IHl. symmetry. rewrite IHl. lra.
Qed.

Lemma Rsum_fold_left_Rplus :
  forall len start f,
    Rsum start len f = fold_left Rplus (map f (seq start len)) 0.
Proof.
  induction len; intros. easy.
  rewrite Rsum_extend_start. rewrite IHlen. simpl.
  symmetry. rewrite fold_left_Rplus_accum. lra.
Qed.

Lemma Rsum_ub :
  forall len start f1 f2,
    (forall i, (start <= i < start + len)%nat -> f1 i <= f2 i) -> Rsum start len f1 <= Rsum start len f2.
Proof.
  induction len; intros. simpl. lra.
  do 2 rewrite Rsum_extend_len.
  assert (∀ i : nat, (start ≤ i < start + len)%nat → f1 i <= f2 i) by (intros; apply H; lia).
  specialize (IHlen start f1 f2 H0).
  assert (f1 (start + len)%nat <= f2 (start + len)%nat) by (apply H; lia).
  lra.
Qed.

Lemma Rsum_extend_len_ge :
  forall len' len start f,
    (forall i, (start + len <= i < start + len + len')%nat -> 0 <= f i) -> Rsum start len f <= Rsum start (len + len') f.
Proof.
  induction len'; intros. rewrite Nat.add_0_r. lra.
  replace (len + S len')%nat with (S (len + len'))%nat by lia.
  assert (∀ i : nat, start + len ≤ i < start + len + len' → 0 <= f i) by (intros; apply H; lia).
  specialize (IHlen' len start f H0).
  rewrite Rsum_extend_len.
  assert (0 <= f (start + (len + len'))%nat) by (apply H; lia).
  lra.
Qed.

Lemma Rsum_constant :
  forall len start f r,
    (forall i, (start <= i < start + len)%nat -> f i = r) -> Rsum start len f = r * len.
Proof.
  induction len; intros. simpl. lra.
  assert (∀ i : nat, (start ≤ i < start + len)%nat → f i = r) by (intros; apply H; lia).
  specialize (IHlen start f r H0).
  rewrite Rsum_extend_len.
  assert (f (start + len)%nat = r) by (apply H; lia).
  replace (INR (S len)) with (len + 1) by (destruct len; simpl; lra).
  lra.
Qed.

Lemma INR_inv_pos :
  forall n, (n <> 0)%nat -> 0 < / n.
Proof.
  intros. apply Rinv_0_lt_compat. replace 0 with (INR O) by easy. apply lt_INR. lia.
Qed.

Lemma INR_inv_lt :
  forall n m, (0 < n <= m)%nat -> / m <= / n.
Proof.
  intros.
  assert (0 < n) by (replace 0 with (INR O) by easy; apply lt_INR; lia).
  assert (n <= m) by (apply le_INR; lia).
  apply Rinv_le_contravar; easy.
Qed.

Lemma Rinv_1div :
  forall r, 1 / r = / r.
Proof.
  intros. unfold Rdiv. apply Rmult_1_l.
Qed.

Lemma Rsum_break :
  forall len2 start len1 f,
    Rsum start (len1 + len2)%nat f = Rsum start len1 f + Rsum (start + len1)%nat len2 f.
Proof.
  induction len2; intros. simpl. rewrite Nat.add_0_r. lra.
  replace (len1 + S len2)%nat with (S (len1 + len2))%nat by lia.
  do 2 rewrite Rsum_extend_len. rewrite IHlen2. replace (start + (len1 + len2))%nat with (start + len1 + len2)%nat by lia. lra.
Qed.

Fixpoint RsumP2 n f :=
  match n with
  | O => 0
  | S n' => RsumP2 n' f + Rsum (2^n')%nat (2^n')%nat f
  end.

Lemma RsumP2_Rsum :
  forall n f,
    RsumP2 n f = Rsum 1 (2^n - 1)%nat f.
Proof.
  induction n; intros. easy.
  simpl. rewrite IHn. replace (2 ^ n + (2 ^ n + 0) - 1)%nat with ((2^n - 1) + 2^n)%nat by lia.
  rewrite Rsum_break. assert (2^n <> 0)%nat by (apply Nat.pow_nonzero; easy).
  replace (1 + (2 ^ n - 1))%nat with (2^n)%nat by lia. easy.
Qed.

Lemma RsumP2_log2_inv :
  forall n, RsumP2 n (fun x : nat => 1 / (2 ^ Nat.log2 x)%nat) = n.
Proof.
  induction n. easy.
  simpl. rewrite IHn.
  assert (2^n <> 0)%nat by (apply Nat.pow_nonzero; easy).
  assert (Rsum (2 ^ n) (2 ^ n) (fun x : nat => 1 / (2 ^ Nat.log2 x)%nat) = Rsum (2 ^ n) (2 ^ n) (fun x : nat => 1 / (2^n)%nat)).
  { apply Rsum_eq_bounded. intros.
    assert (0 < i)%nat by lia.
    destruct H0 as [Hl Hr].
    apply Nat.log2_le_mono in Hl. rewrite Nat.log2_pow2 in Hl by lia.
    replace (2 ^ n + 2 ^ n)%nat with (2 ^ (S n))%nat in Hr by (simpl; lia).
    apply Nat.log2_lt_pow2 in Hr. 2:easy.
    assert (Nat.log2 i = n) by lia. subst.
    easy.
  }
  assert (Rsum (2 ^ n) (2 ^ n) (fun x : nat => 1 / (2^n)%nat) = 1).
  { rewrite Rsum_constant with (r := 1 / (2^n)%nat). 2: intros; easy.
    field. replace 0 with (INR O) by easy. apply not_INR. easy.
  }
  rewrite H0, H1. destruct n; simpl; lra.
Qed.

Theorem harmonic_upper_bound :
  ∀ (n : nat), fold_left Rplus (map (λ (x : nat), 1 / x) (seq 1 n)) 0 <= 1 + Nat.log2 n.
Proof.
  intros. destruct n. simpl. lra. rename n into n'. remember (S n') as n.
  rewrite <- Rsum_fold_left_Rplus.
  assert (forall i : nat, (2^(Nat.log2 i) <> 0)%nat) by (intro; apply Nat.pow_nonzero; easy).
  assert (Rsum 1 n (fun x : nat => 1 / x) <= Rsum 1 n (fun x : nat => 1 / (2^Nat.log2 x)%nat)).
  { apply Rsum_ub. intros. do 2 rewrite Rinv_1div. apply INR_inv_lt.
    split. specialize (H i). lia.
    assert (0 < i)%nat by lia.
    specialize (Nat.log2_spec _ H1) as G. easy.
  }
  assert (Rsum 1 n (fun x : nat => 1 / (2^Nat.log2 x)%nat) <= Rsum 1 (2^(S (Nat.log2 n)) - 1)%nat (fun x : nat => 1 / (2^Nat.log2 x)%nat)).
  { assert (0 < n)%nat by lia.
    assert (n <= 2 ^ S (Nat.log2 n) - 1)%nat.
    specialize (Nat.log2_spec _ H1) as G. lia.
    replace (2 ^ S (Nat.log2 n) - 1)%nat with (n + (2 ^ S (Nat.log2 n) - 1 - n))%nat by lia.
    apply Rsum_extend_len_ge. intros.
    specialize (H i). 
    specialize (INR_inv_pos (2 ^ Nat.log2 i)%nat H) as G. rewrite Rinv_1div. lra.
  }
  specialize (RsumP2_Rsum (S (Nat.log2 n)) (fun x : nat => 1 / (2 ^ Nat.log2 x)%nat)) as G.
  assert (RsumP2 (S (Nat.log2 n)) (λ x : nat, 1 / (2 ^ Nat.log2 x)%nat) = 1 + Nat.log2 n).
  { rewrite RsumP2_log2_inv. simpl. destruct (Nat.log2 n); simpl; lra.
  }
  lra.
Qed.

Local Close Scope R_scope.
