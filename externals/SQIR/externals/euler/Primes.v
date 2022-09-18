(* We copied and modified this file from https://github.com/roglo/coq_euler_prod_form/blob/master/Primes.v *)

(* Prime numbers *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith SetoidList Permutation.
Require Import Misc.
Import List ListNotations.

Fixpoint prime_test cnt n d :=
  match cnt with
  | 0 => true
  | S c =>
      match n mod d with
      | 0 => n <=? d
      | S _ => prime_test c n (d + 1)
      end
  end.

Definition is_prime n :=
  match n with
  | 0 | 1 => false
  | S (S c) => prime_test c n 2
  end.

Definition prime p := is_prime p = true.

Theorem prime_test_false_exists_div_iff : ∀ n k,
  2 ≤ k
  → (∀ d, 2 ≤ d < k → n mod d ≠ 0)
  → prime_test (n - k) n k = false
  ↔ ∃ a b : nat, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b.
Proof.
intros * Hk Hd.
split.
-intros Hp.
 remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
 revert n k Hk Hd Hcnt Hp.
 induction cnt; intros; [ easy | ].
 cbn in Hp.
 remember (n mod k) as m eqn:Hm; symmetry in Hm.
 destruct m. {
   destruct k; [ easy | ].
   apply Nat.mod_divides in Hm; [ | easy ].
   destruct Hm as (m, Hm).
   destruct m; [ now rewrite Hm, Nat.mul_0_r in Hcnt | ].
   destruct k; [ flia Hk | ].
   destruct m. {
     now rewrite Hm, Nat.mul_1_r, Nat.sub_diag in Hcnt.
   }
   exists (S (S k)), (S (S m)).
   rewrite Hm.
   replace (S (S k) * S (S m)) with (S (S k) + k * m + k + 2 * m + 2) by flia.
   split; [ flia | ].
   split; [ flia | easy ].
 }
 destruct n; [ flia Hcnt | ].
 apply (IHcnt (S n) (k + 1)); [ flia Hk | | flia Hcnt | easy ].
 intros d Hdk.
 destruct (Nat.eq_dec d k) as [Hdk1| Hdk1]. {
   now intros H; rewrite <- Hdk1, H in Hm.
 }
 apply Hd; flia Hdk Hdk1.
-intros (a & b & Han & Hbn & Hnab).
 remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
 revert n a b k Hk Hd Hcnt Han Hbn Hnab.
 induction cnt; intros. {
   specialize (Hd a) as H1.
   assert (H : 2 ≤ a < k). {
     split. {
       destruct a; [ flia Hnab Han | ].
       destruct a; [ flia Hnab Han Hbn | flia ].
     }
     rewrite Hnab in Hcnt.
     apply Nat.sub_0_le in Hcnt.
     apply (Nat.lt_le_trans _ (a * b)); [ | easy ].
     destruct a; [ flia Han | ].
     destruct b; [ flia Hbn | ].
     destruct b; [ flia Hbn | flia ].
   }
   specialize (H1 H).
   exfalso; apply H1; rewrite Hnab, Nat.mul_comm.
   apply Nat.mod_mul; flia H.
 }
 cbn.
 remember (n mod k) as m eqn:Hm; symmetry in Hm.
 destruct m; [ apply Nat.leb_gt; flia Hcnt | ].
 apply (IHcnt _ a b); [ flia Hk | | flia Hcnt | easy | easy | easy ].
 intros d (H2d, Hdk).
 destruct (Nat.eq_dec d k) as [Hdk1| Hdk1]. {
   now intros H; rewrite <- Hdk1, H in Hm.
 }
 apply Hd.
 flia H2d Hdk Hdk1.
Qed.

Theorem not_prime_decomp : ∀ n, 2 ≤ n →
  ¬ prime n
  → ∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b.
Proof.
intros n Hn Hp.
apply Bool.not_true_iff_false in Hp.
unfold is_prime in Hp.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | ].
replace n with (S (S n) - 2) in Hp at 1 by flia.
apply (prime_test_false_exists_div_iff _ 2); [ easy | | easy ].
intros * H; flia H.
Qed.

Theorem not_prime_exists_div : ∀ n, 2 ≤ n →
  ¬ prime n
  → ∃ a, 2 ≤ a < n ∧ Nat.divide a n.
Proof.
intros n Hn Hp.
specialize (not_prime_decomp n Hn Hp) as (a & b & Ha & Hb & Hab).
exists a.
split; [ | now rewrite Hab; apply Nat.divide_mul_l ].
split; [ easy | ].
rewrite Hab, Nat.mul_comm.
destruct a; [ flia Ha | ].
destruct b; [ flia Hb | ].
destruct b; [ flia Hb | flia ].
Qed.

Theorem exist_prime_divisor : ∀ n, 2 ≤ n →
  ∃ d, prime d ∧ Nat.divide d n.
Proof.
intros * Hn.
induction n as (n, IHn) using (well_founded_ind lt_wf).
remember (is_prime n) as b eqn:Hb; symmetry in Hb.
destruct b; [ now exists n | ].
apply Bool.not_true_iff_false in Hb.
specialize (not_prime_exists_div n Hn Hb) as (a & Han & Hd).
specialize (IHn a (proj2 Han) (proj1 Han)) as H1.
destruct H1 as (d & Hpd & Hda).
exists d.
split; [ easy | ].
now transitivity a.
Qed.

Theorem Nat_le_divides_fact : ∀ n d, d ≤ n → Nat.divide (fact d) (fact n).
Proof.
intros * Hdn.
replace d with (n - (n - d)) by flia Hdn.
apply Nat_divide_fact_fact.
Qed.

Theorem Nat_fact_divides_small : ∀ n d,
  1 ≤ d ≤ n
  → fact n = fact n / d * d.
Proof.
intros * (Hd, Hdn).
specialize (Nat_le_divides_fact n d Hdn) as H1.
destruct H1 as (c, Hc).
rewrite Hc at 2.
destruct d; [ easy | ].
rewrite Nat_fact_succ.
rewrite (Nat.mul_comm (S d)).
rewrite Nat.mul_assoc.
rewrite Nat.div_mul; [ | easy ].
rewrite Hc, Nat_fact_succ.
now rewrite Nat.mul_assoc, Nat.mul_shuffle0.
Qed.

Lemma next_prime_bounded : ∀ n, ∃ m, n < m ≤ fact n + 1 ∧ prime m.
Proof.
intros.
specialize (exist_prime_divisor (fact n + 1)) as H1.
assert (H : 2 ≤ fact n + 1). {
  clear.
  induction n; [ easy | ].
  rewrite Nat_fact_succ.
  apply (Nat.le_trans _ (fact n + 1)); [ easy | ].
  apply Nat.add_le_mono_r.
  cbn; flia.
}
specialize (H1 H); clear H.
destruct H1 as (d & Hd & Hdn).
exists d.
split; [ | easy ].
split.
-destruct (lt_dec n d) as [Hnd| Hnd]; [ easy | ].
 apply Nat.nlt_ge in Hnd; exfalso.
 assert (Ht : Nat.divide d (fact n)). {
   exists (fact n / d).
   apply Nat_fact_divides_small.
   split; [ | easy ].
   destruct d; [ easy | flia ].
 }
 destruct Hdn as (z, Hz).
 destruct Ht as (t, Ht).
 rewrite Ht in Hz.
 apply Nat.add_sub_eq_l in Hz.
 rewrite <- Nat.mul_sub_distr_r in Hz.
 apply Nat.eq_mul_1 in Hz.
 now destruct Hz as (Hz, H); subst d.
-apply Nat.divide_pos_le; [ flia | easy ].
Qed.

Theorem infinitely_many_primes : ∀ n, ∃ m, m > n ∧ prime m.
Proof.
intros.
specialize (next_prime_bounded n) as (m & (Hnm & _) & Hp).
now exists m.
Qed.

Lemma prime_test_mod_ne_0 : ∀ n k,
  2 ≤ n
  → prime_test (n - k) n k = true
  → ∀ d, k ≤ d < n → n mod d ≠ 0.
Proof.
intros * Hn Hp d Hd.
remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
revert n k d Hn Hcnt Hp Hd.
induction cnt; intros; [ flia Hcnt Hd | ].
cbn in Hp.
remember (n mod k) as m eqn:Hm; symmetry in Hm.
destruct m; [ apply Nat.leb_le in Hp; flia Hp Hd | ].
destruct n; [ flia Hcnt | ].
destruct (Nat.eq_dec k d) as [Hkd| Hkd]. {
  now intros H; rewrite Hkd, H in Hm.
}
apply (IHcnt (S n) (k + 1)); [ easy | flia Hcnt | easy | flia Hd Hkd ].
Qed.

Theorem prime_only_divisors : ∀ p,
  prime p → ∀ a, Nat.divide a p → a = 1 ∨ a = p.
Proof.
intros * Hp a * Hap.
destruct (lt_dec p 2) as [Hp2| Hp2]. {
  destruct p; [ easy | ].
  destruct p; [ easy | flia Hp2 ].
}
apply Nat.nlt_ge in Hp2.
destruct (zerop a) as [Ha| Ha]. {
  subst a.
  apply Nat.divide_0_l in Hap; flia Hap Hp2.
}
apply Nat.neq_0_lt_0 in Ha.
apply Nat.mod_divide in Hap; [ | easy ].
apply Nat.mod_divides in Hap; [ | easy ].
destruct Hap as (k, Hk).
symmetry in Hk.
destruct p; [ easy | ].
destruct p; [ easy | ].
specialize (prime_test_mod_ne_0 (S (S p)) 2 Hp2) as H1.
replace (S (S p) - 2) with p in H1 by flia.
specialize (H1 Hp).
destruct k; [ now rewrite Nat.mul_0_r in Hk | ].
destruct k; [ now rewrite Nat.mul_1_r in Hk; right | left ].
destruct a; [ easy | ].
destruct a; [ easy | exfalso ].
specialize (H1 (S (S k))) as H2.
assert (H : 2 ≤ S (S k) < S (S p)). {
  split; [ flia Hp2 | flia Hk ].
}
specialize (H2 H); clear H.
apply H2; rewrite <- Hk.
now rewrite Nat.mod_mul.
Qed.

Theorem prime_prop : ∀ p, prime p → ∀ i, 2 ≤ i ≤ p - 1 → ¬ Nat.divide i p.
Proof.
intros * Hp i Hi Hdiv.
specialize (prime_only_divisors p Hp i Hdiv) as H1.
flia Hi H1.
Qed.

Theorem eq_primes_gcd_1 : ∀ a b,
  prime a → prime b → a ≠ b → Nat.gcd a b = 1.
Proof.
intros p q Hp Hq Hpq.
specialize (prime_only_divisors _ Hp) as Hpp.
specialize (prime_only_divisors _ Hq) as Hqp.
specialize (Hpp (Nat.gcd p q) (Nat.gcd_divide_l _ _)) as H1.
specialize (Hqp (Nat.gcd p q) (Nat.gcd_divide_r _ _)) as H2.
destruct H1 as [H1| H1]; [ easy | ].
destruct H2 as [H2| H2]; [ easy | ].
now rewrite H1 in H2.
Qed.

Fixpoint prime_decomp_aux cnt n d :=
  match cnt with
  | 0 => []
  | S c =>
      match n mod d with
      | 0 => d :: prime_decomp_aux c (n / d) d
      | _ => prime_decomp_aux c n (S d)
      end
  end.

Definition prime_decomp n :=
  match n with
  | 0 | 1 => []
  | _ => prime_decomp_aux n n 2
  end.

Lemma prime_decomp_aux_of_prime_test : ∀ n k,
  2 ≤ n
  → prime_test (n - 2) (k + n) (k + 2) = true
  → prime_decomp_aux n (k + n) (k + 2) = [k + n].
Proof.
intros * Hn Hpn.
destruct n; [ easy | ].
destruct n; [ flia Hn | clear Hn ].
replace (S (S n) - 2) with n in Hpn by flia.
revert k Hpn.
induction n; intros. {
  cbn - [ "/" "mod" ].
  rewrite Nat.mod_same; [ | flia ].
  rewrite Nat.div_same; [ | flia ].
  rewrite Nat.mod_1_l; [ easy | flia ].
}
remember (S (S n)) as sn.
cbn - [ "/" "mod" ].
cbn - [ "/" "mod" ] in Hpn.
remember ((k + S sn) mod (k + 2)) as b eqn:Hb; symmetry in Hb.
destruct b; [ apply Nat.leb_le in Hpn; flia Heqsn Hpn | ].
replace (k + S sn) with (S k + sn) in Hpn |-* by flia.
replace (S (k + 2)) with (S k + 2) by flia.
replace (k + 2 + 1) with (S k + 2) in Hpn by flia.
now apply IHn.
Qed.

Theorem prime_neq_0 : ∀ p, prime p → p ≠ 0.
Proof. now intros * Hp H; subst p. Qed.

Theorem prime_ge_2 : ∀ n, prime n → 2 ≤ n.
Proof.
intros * Hp.
destruct n; [ easy | ].
destruct n; [ easy | flia ].
Qed.

Theorem prime_decomp_of_prime : ∀ n, prime n → prime_decomp n = [n].
Proof.
intros * Hpn.
specialize (prime_ge_2 _ Hpn) as Hn.
unfold prime, is_prime in Hpn.
unfold prime_decomp.
replace n with (S (S (n - 2))) in Hpn at 1 by flia Hn.
replace n with (S (S (n - 2))) at 1 by flia Hn.
replace n with (0 + n) in Hpn at 2 by flia.
replace 2 with (0 + 2) in Hpn at 2 by flia.
now apply prime_decomp_aux_of_prime_test in Hpn; [ | easy ].
Qed.

Lemma prime_decomp_aux_le : ∀ cnt n d d',
  d ≤ d' → HdRel le d (prime_decomp_aux cnt n d').
Proof.
intros * Hdd.
revert n d d' Hdd.
induction cnt; intros; [ constructor | cbn ].
destruct (n mod d') as [| Hnd]; [ now constructor | ].
apply IHcnt, (le_trans _ d'); [ easy | ].
apply Nat.le_succ_diag_r.
Qed.

Lemma Sorted_prime_decomp_aux : ∀ cnt n d,
  Sorted le (prime_decomp_aux cnt n d).
Proof.
intros.
revert n d.
induction cnt; intros; [ constructor | cbn ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b. {
  constructor; [ apply IHcnt | ].
  now apply prime_decomp_aux_le.
}
apply IHcnt.
Qed.

Theorem Sorted_prime_decomp : ∀ n, Sorted le (prime_decomp n).
Proof.
intros.
destruct n; [ constructor | ].
cbn - [ "/" "mod" ].
destruct n; [ constructor | ].
destruct (S (S n) mod 2) as [| b]. {
  constructor; [ apply Sorted_prime_decomp_aux | ].
  now apply prime_decomp_aux_le.
}
apply Sorted_prime_decomp_aux.
Qed.

Lemma in_prime_decomp_aux_le : ∀ cnt n d d',
  d' ∈ prime_decomp_aux cnt n d
  → d ≤ d'.
Proof.
intros * Hd'.
revert n d d' Hd'.
induction cnt; intros; [ easy | ].
cbn in Hd'.
destruct (n mod d) as [| b]. {
  destruct Hd' as [Hd'| Hd']; [ now subst d' | ].
  now apply (IHcnt (n / d)).
}
transitivity (S d); [ apply Nat.le_succ_diag_r | now apply (IHcnt n) ].
Qed.

Theorem in_prime_decomp_ge_2 : ∀ n d,
  d ∈ prime_decomp n
  → 2 ≤ d.
Proof.
intros * Hd.
destruct n; [ easy | ].
destruct n; [ easy | ].
unfold prime_decomp in Hd.
eapply in_prime_decomp_aux_le.
apply Hd.
Qed.

Theorem prime_decomp_param_ge_2 : ∀ n d,
  d ∈ prime_decomp n
  → 2 ≤ n.
Proof.
intros * Hd.
destruct n; [ easy | ].
destruct n; [ easy | flia ].
Qed.

Lemma in_prime_decomp_aux_divide : ∀ cnt n d p,
  d ≠ 0
  → p ∈ prime_decomp_aux cnt n d
  → Nat.divide p n.
Proof.
intros * Hdz Hp.
specialize (in_prime_decomp_aux_le cnt n d _ Hp) as Hdp.
assert (Hpz : p ≠ 0) by flia Hdz Hdp.
move Hpz before Hdz.
revert n d p Hdz Hp Hpz Hdp.
induction cnt; intros; [ easy | ].
cbn in Hp.
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b. {
  destruct Hp as [Hp| Hp]; [ now subst d; apply Nat.mod_divide | ].
  apply (Nat.divide_trans _ (n / d)). 2: {
    apply Nat.mod_divides in Hb; [ | easy ].
    destruct Hb as (c, Hc).
    rewrite Hc, Nat.mul_comm, Nat.div_mul; [ | easy ].
    apply Nat.divide_factor_l.
  }
  now apply (IHcnt _ d).
}
specialize (in_prime_decomp_aux_le _ _ _ _ Hp) as H1.
now apply (IHcnt _ (S d)).
Qed.

Theorem in_prime_decomp_divide : ∀ n d,
  d ∈ prime_decomp n → Nat.divide d n.
Proof.
intros * Hd.
assert (H2n : 2 ≤ n). {
  destruct n; [ easy | ].
  destruct n; [ easy | flia ].
}
specialize (in_prime_decomp_ge_2 n d Hd) as H2d.
move Hd at bottom.
unfold prime_decomp in Hd.
replace n with (S (S (n - 2))) in Hd by flia H2n.
replace (S (S (n - 2))) with n in Hd by flia H2n.
now apply in_prime_decomp_aux_divide in Hd.
Qed.

Theorem in_prime_decomp_le : ∀ n d : nat, d ∈ prime_decomp n → d ≤ n.
Proof.
intros * Hd.
apply Nat.divide_pos_le; [ | now apply in_prime_decomp_divide ].
destruct n; [ easy | flia ].
Qed.

Lemma prime_decomp_aux_at_1 : ∀ cnt d, 2 ≤ d → prime_decomp_aux cnt 1 d = [].
Proof.
intros * H2d.
destruct d; [ flia H2d | ].
destruct d; [ flia H2d | clear H2d ].
revert d.
induction cnt; intros; [ easy | cbn ].
destruct d; [ apply IHcnt | ].
replace (S d - d) with 1 by flia.
apply IHcnt.
Qed.

Lemma prime_decomp_aux_more_iter : ∀ k cnt n d,
  2 ≤ n
  → 2 ≤ d
  → n + 2 ≤ cnt + d
  → prime_decomp_aux cnt n d = prime_decomp_aux (cnt + k) n d.
Proof.
intros * H2n H2d Hnc.
revert n k d H2n H2d Hnc.
induction cnt; intros. {
  cbn in Hnc; cbn.
  revert d H2d Hnc.
  induction k; intros; [ easy | cbn ].
  rewrite Nat.mod_small; [ | flia Hnc ].
  destruct n; [ flia H2n | ].
  apply IHk; flia Hnc.
}
cbn - [ "/" "mod" ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b. {
  f_equal.
  apply Nat.mod_divides in Hb; [ | flia H2d ].
  destruct Hb as (b, Hb); rewrite Nat.mul_comm in Hb.
  rewrite Hb, Nat.div_mul; [ | flia H2d ].
  destruct (le_dec 2 b) as [H2b| H2b]. {
    apply IHcnt; [ easy | easy | ].
    transitivity (n + 1); [ | flia H2n Hnc ].
    rewrite Hb.
    destruct b; [ flia H2n Hb | ].
    destruct d; [ easy | ].
    destruct d; [ flia H2d | ].
    cbn; rewrite Nat.mul_comm; cbn.
    flia.
  }
  apply Nat.nle_gt in H2b.
  destruct b; [ cbn in Hb; subst n; flia H2n | ].
  destruct b; [ | flia H2b ].
  rewrite prime_decomp_aux_at_1; [ | easy ].
  now rewrite prime_decomp_aux_at_1.
}
apply IHcnt; [ easy | | flia Hnc ].
flia H2d Hnc.
Qed.

Lemma prime_test_more_iter : ∀ k cnt n d,
  2 ≤ n
  → n ≤ cnt + d
  → prime_test cnt n d = prime_test (cnt + k) n d.
Proof.
intros * H2n Hnc.
revert n k d H2n Hnc.
induction cnt; intros. {
  cbn in Hnc; cbn.
  revert d Hnc.
  induction k; intros; [ easy | cbn ].
  remember (n mod d) as b eqn:Hb; symmetry in Hb.
  destruct b; [ now symmetry; apply Nat.leb_le | ].
  destruct n; [ flia H2n | ].
  apply IHk; flia Hnc.
}
cbn - [ "/" "mod" ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
apply IHcnt; [ easy | flia Hnc ].
Qed.

Lemma hd_prime_decomp_aux_ge : ∀ cnt n d,
  2 ≤ d
  → 2 ≤ hd 2 (prime_decomp_aux cnt n d).
Proof.
intros * H2d.
revert d H2d.
induction cnt; intros; [ easy | cbn ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
apply IHcnt; flia H2d.
Qed.

Lemma prev_not_div_prime_test_true : ∀ cnt n d,
  2 ≤ n
  → 2 ≤ d
  → n ≤ cnt + d
  → (∀ e, 2 ≤ e < n → n mod e ≠ 0)
  → prime_test cnt n d = true.
Proof.
intros * H2n H2d Hcnt Hn.
revert n d H2n H2d Hcnt Hn.
induction cnt; intros; [ easy | cbn ].
remember (n mod d) as b1 eqn:Hb1; symmetry in Hb1.
destruct b1. {
  apply Nat.leb_le.
  apply Nat.mod_divides in Hb1; [ | flia H2d ].
  destruct Hb1 as (b1, Hb1).
  destruct b1; [ flia H2d Hb1 | ].
  destruct b1; [ flia Hb1 | ].
  specialize (Hn (S (S b1))) as H1.
  assert (H : 2 ≤ S (S b1) < n). {
    split; [ flia | ].
    rewrite Hb1; remember (S (S b1)) as b.
    destruct d; [ flia H2d | cbn ].
    destruct d; [ flia H2d | flia Heqb ].
  }
  specialize (H1 H).
  exfalso; apply H1; clear H1.
  rewrite Hb1.
  now apply Nat.mod_mul.
}
apply IHcnt; [ easy | flia H2d | flia Hcnt | easy ].
Qed.

Lemma hd_prime_decomp_aux_prime_test_true : ∀ cnt n b d,
  2 ≤ n
  → 2 ≤ d
  → n + 2 ≤ cnt + d
  → (∀ e : nat, 2 ≤ e < d → n mod e ≠ 0)
  → b = hd 2 (prime_decomp_aux cnt n d)
  → prime_test (b - 2) b 2 = true.
Proof.
intros * H2n H2d Hcnt Hnd Hb.
revert d H2d Hcnt Hnd Hb.
induction cnt; intros; [ now subst b | ].
cbn - [ "/" "mod" ] in Hb.
remember (n mod d) as b1 eqn:Hb1; symmetry in Hb1.
destruct b1. {
  cbn in Hb; subst b.
  apply Nat.mod_divides in Hb1; [ | flia H2d ].
  destruct Hb1 as (b1, Hb1).
  destruct b1; [ flia H2n Hb1 | ].
  destruct b1. {
    rewrite Nat.mul_1_r in Hb1; subst n.
    apply prev_not_div_prime_test_true; [ easy | easy | flia H2d | easy ].
  }
  apply prev_not_div_prime_test_true; [ easy | easy | flia H2n | ].
  intros e He.
  specialize (Hnd e He) as H1.
  intros H2; apply H1; clear H1.
  apply Nat.mod_divides in H2; [ | flia He ].
  destruct H2 as (b2, Hb2); rewrite Nat.mul_comm in Hb2.
  rewrite Hb1, Hb2, Nat.mul_shuffle0.
  apply Nat.mod_mul; flia He.
}
assert (H : ∀ e, 2 ≤ e < 1 + d → n mod e ≠ 0). {
  intros e He.
  destruct (Nat.eq_dec e d) as [Hed| Hed]. {
    now subst e; intros H; rewrite H in Hb1.
  }
  apply Hnd; flia He Hed.
}
move H before Hnd; clear Hnd; rename H into Hnd.
clear b1 Hb1.
replace (S cnt + d) with (cnt + S d) in Hcnt by flia.
apply (IHcnt (S d)); [ flia H2d | easy | easy | easy ].
Qed.

Theorem first_in_decomp_is_prime : ∀ n, prime (List.hd 2 (prime_decomp n)).
Proof.
intros.
unfold is_prime, prime_decomp.
destruct n; [ easy | ].
destruct n; [ easy | ].
assert (H2n : 2 ≤ S (S n)) by flia.
remember (S (S n)) as n'.
clear n Heqn'; rename n' into n.
specialize (hd_prime_decomp_aux_ge n n 2 (le_refl _)) as H2b.
unfold prime, is_prime.
remember (hd 2 (prime_decomp_aux n n 2)) as b eqn:Hb.
move b before n; move H2b before H2n.
replace b with (S (S (b - 2))) by flia H2b.
replace (S (S (b - 2))) with b by flia H2b.
apply (hd_prime_decomp_aux_prime_test_true n n b 2);
  [ easy | easy | easy | | easy ].
intros e He; flia He.
Qed.

Lemma prime_decomp_aux_not_nil : ∀ cnt n d,
  2 ≤ n
  → 2 ≤ d
  → n + 2 ≤ cnt + d
  → (∀ e : nat, 2 ≤ e < d → n mod e ≠ 0)
  → prime_decomp_aux cnt n d ≠ [].
Proof.
intros * H2n H2d Hcnt Hnd.
revert d H2d Hcnt Hnd.
induction cnt; intros. {
  assert (H : 2 ≤ n < d) by flia H2n Hcnt.
  specialize (Hnd n H); clear H.
  rewrite Nat.mod_same in Hnd; [ easy | flia H2n ].
}
cbn - [ "/" "mod" ].
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
rewrite Nat.add_succ_comm in Hcnt.
apply IHcnt; [ flia H2d | easy | ].
intros e He.
destruct (Nat.eq_dec e d) as [Hed| Hed]. {
  now subst e; intros H; rewrite H in Hb.
}
apply Hnd; flia He Hed.
Qed.

Theorem prime_decomp_nil_iff : ∀ n, prime_decomp n = [] ↔ n = 0 ∨ n = 1.
Proof.
intros.
split.
-intros Hn.
 unfold prime_decomp in Hn.
 destruct n; [ now left | ].
 destruct n; [ now right | exfalso ].
 revert Hn.
 apply prime_decomp_aux_not_nil; [ flia | easy | easy | ].
 intros e He; flia He.
-now intros [Hn| Hn]; subst n.
Qed.

Lemma prime_decomp_aux_cons_nil : ∀ cnt n d l,
  2 ≤ n
  → 2 ≤ d
  → n + 2 ≤ cnt + d
  → (∀ e, 2 ≤ e < d → n mod e ≠ 0)
  → prime_decomp_aux cnt n d = n :: l
  → l = [].
Proof.
intros * H2n H2d Hcnt Hdn Hnd.
revert d l H2d Hcnt Hdn Hnd.
induction cnt; intros; [ easy | ].
cbn in Hnd.
remember (n mod d) as b eqn:Hb; symmetry in Hb.
destruct b. {
  injection Hnd; clear Hnd; intros Hl Hd; subst d.
  rewrite Nat.div_same in Hl; [ | flia H2n ].
  now rewrite prime_decomp_aux_at_1 in Hl.
}
rewrite Nat.add_succ_comm in Hcnt.
apply (IHcnt (S d)); [ flia H2d | easy | | easy ].
intros e He.
destruct (Nat.eq_dec e d) as [Hed| Hed]. {
  now subst e; intros H; rewrite H in Hb.
}
apply Hdn; flia He Hed.
Qed.

Lemma prime_decomp_aux_cons : ∀ p b l n d cb cn,
  2 ≤ n
  → 2 ≤ b
  → 2 ≤ d
  → 2 ≤ p
  → b + 2 ≤ cb + d
  → n + 2 ≤ cn + d
  → n * p = b
  → prime_decomp_aux cb b d = p :: l
  → prime_decomp_aux cn n d = l.
Proof.
intros * H2n H2b H2d H2p Hcb Hcn Hb Hbp.
revert p b n d cn H2n H2b H2d H2p Hcb Hcn Hb Hbp.
induction cb; intros; [ easy | ].
cbn in Hbp.
remember (b mod d) as b1 eqn:Hb1; symmetry in Hb1.
destruct b1. {
  injection Hbp; clear Hbp; intros Hl Hp; subst d.
  rewrite <- Hb, Nat.div_mul in Hl; [ | flia H2b Hb ].
  rewrite (prime_decomp_aux_more_iter cn) in Hl; [ | easy | easy | ]. 2: {
    apply Nat.succ_le_mono.
    replace (S (cb + p)) with (S cb + p) by flia.
    transitivity (b + 2); [ | easy ].
    replace (S (n + 2)) with (S n + 2) by flia.
    apply Nat.add_le_mono_r.
    rewrite <- Hb.
    destruct p; [ flia H2p | ].
    destruct p; [ flia H2p | ].
    rewrite Nat.mul_comm; cbn.
    destruct n; [ easy | flia ].
  }
  rewrite Nat.add_comm in Hl.
  now rewrite (prime_decomp_aux_more_iter cb).
}
rewrite (prime_decomp_aux_more_iter 1); try easy.
rewrite Nat.add_1_r; cbn.
remember (n mod d) as b2 eqn:Hb2; symmetry in Hb2.
destruct b2. {
  apply Nat.mod_divides in Hb2; [ | flia H2d ].
  destruct Hb2 as (b2, Hb2).
  rewrite <- Hb, Hb2 in Hb1.
  rewrite <- Nat.mul_assoc, Nat.mul_comm in Hb1.
  rewrite Nat.mod_mul in Hb1; [ easy | flia H2d ].
}
rewrite Nat.add_succ_comm in Hcb.
apply (IHcb p b); try easy; [ flia H2d | flia Hcn ].
Qed.

Theorem prime_decomp_mul : ∀ n d l,
  2 ≤ d
  → prime_decomp (n * d) = d :: l
  → prime_decomp n = l.
Proof.
intros * H2d Hnd.
unfold prime_decomp in Hnd.
unfold prime_decomp.
destruct n; [ easy | ].
destruct n. {
  rewrite Nat.mul_1_l in Hnd.
  destruct d; [ easy | ].
  cbn - [ "/" "mod" ] in Hnd.
  destruct d; [ easy | ].
  remember (S (S d)) as d'.
  replace (S d) with (d' - 1) in Hnd by flia Heqd'.
  clear d Heqd'; rename d' into d; move H2d after Hnd.
  remember (d mod 2) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    remember (prime_decomp_aux _ _ _) as x.
    injection Hnd; clear Hnd; intros Hl Hd; subst x.
    now subst d.
  }
  symmetry.
  apply prime_decomp_aux_cons_nil in Hnd; [ easy | easy | flia | flia | ].
  intros e He H.
  replace e with 2 in H by flia He.
  now rewrite H in Hb.
}
assert (H2n : 2 ≤ S (S n)) by flia.
remember (S (S n)) as n'; clear n Heqn'; rename n' into n.
remember (n * d) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
destruct b; [ easy | ].
assert (H2b : 2 ≤ S (S b)) by flia.
remember (S (S b)) as b'; clear b Heqb'; rename b' into b.
move H2n after Hb; move H2b after Hb.
now apply (prime_decomp_aux_cons) with (n := n) (cn := n) in Hnd.
Qed.

Theorem prime_decomp_cons : ∀ n a l,
  prime_decomp n = a :: l
  → prime_decomp (n / a) = l.
Proof.
intros * Hl.
assert (Hap : prime a). {
  specialize (first_in_decomp_is_prime n) as H1.
  now rewrite Hl in H1.
}
assert (H2a : 2 ≤ a) by now apply prime_ge_2.
apply (prime_decomp_mul (n / a) a); [ easy | ].
specialize (in_prime_decomp_divide n a) as H1.
rewrite Hl in H1.
specialize (H1 (or_introl eq_refl)).
destruct H1 as (b, Hb).
rewrite Hb, Nat.div_mul; [ | flia H2a ].
now rewrite <- Hb.
Qed.

Theorem prime_decomp_inj : ∀ a b,
  a ≠ 0 → b ≠ 0 → prime_decomp a = prime_decomp b → a = b.
Proof.
intros * Ha0 Hb0 Hab.
remember (prime_decomp b) as l eqn:Hb; symmetry in Hb.
rename Hab into Ha; move Ha after Hb.
revert a b Ha0 Hb0 Ha Hb.
induction l as [| d]; intros. {
  apply prime_decomp_nil_iff in Ha.
  apply prime_decomp_nil_iff in Hb.
  destruct Ha as [Ha| Ha]; [ easy | ].
  destruct Hb as [Hb| Hb]; [ easy | ].
  now subst a b.
}
specialize (in_prime_decomp_divide a d) as Hda.
rewrite Ha in Hda; cbn in Hda.
specialize (Hda (or_introl (eq_refl _))) as (da, Hda).
specialize (in_prime_decomp_divide b d) as Hdb.
rewrite Hb in Hdb; cbn in Hdb.
specialize (Hdb (or_introl (eq_refl _))) as (db, Hdb).
move db before da.
rewrite Hda, Hdb; f_equal.
apply IHl.
-now intros H; rewrite H in Hda.
-now intros H; rewrite H in Hdb.
-rewrite Hda in Ha.
 apply (prime_decomp_mul _ d); [ | easy ].
 destruct d; [ flia Ha0 Hda | ].
 destruct d; [ | flia ].
 apply (in_prime_decomp_ge_2 b 1).
 now rewrite Hb; left.
-rewrite Hdb in Hb.
 apply (prime_decomp_mul _ d); [ | easy ].
 destruct d; [ flia Ha0 Hda | ].
 destruct d; [ | flia ].
 apply (in_prime_decomp_ge_2 a 1).
 now rewrite Ha; left.
Qed.

Theorem in_prime_decomp_is_prime : ∀ n d, d ∈ prime_decomp n → prime d.
Proof.
intros * Hdn.
specialize (In_nth (prime_decomp n) d 2 Hdn) as (i & Hilen & Hid).
clear Hdn; subst d.
revert n Hilen.
induction i; intros. {
  rewrite <- List_hd_nth_0.
  apply first_in_decomp_is_prime.
}
remember (prime_decomp n) as l eqn:Hl; symmetry in Hl.
destruct l as [| a l]; [ easy | ].
cbn in Hilen; cbn.
apply Nat.succ_lt_mono in Hilen.
specialize (prime_decomp_cons n a l Hl) as H1.
rewrite <- H1.
apply IHi.
now rewrite H1.
Qed.

Theorem prime_decomp_prod : ∀ n, n ≠ 0 →
  fold_left Nat.mul (prime_decomp n) 1 = n.
Proof.
intros * Hnz.
remember (prime_decomp n) as l eqn:Hl; symmetry in Hl.
revert n Hnz Hl.
induction l as [| a l]; intros. {
  now apply prime_decomp_nil_iff in Hl; destruct Hl.
}
remember 1 as one; cbn; subst one.
specialize (in_prime_decomp_divide n a) as H1.
rewrite Hl in H1; specialize (H1 (or_introl eq_refl)).
destruct H1 as (k, Hk).
rewrite Hk in Hl.
assert (H2a : 2 ≤ a). {
  apply (in_prime_decomp_ge_2 (k * a)).
  now rewrite Hl; left.
}
apply prime_decomp_mul in Hl; [ | easy ].
apply IHl in Hl; [ | now intros H; subst k ].
apply (Nat.mul_cancel_r _ _ a) in Hl; [ | flia H2a ].
rewrite Hk, <- Hl.
symmetry; apply List_fold_left_mul_assoc.
Qed.

Theorem eq_gcd_prime_small_1 : ∀ p n,
  prime p
  → 0 < n < p
  → Nat.gcd p n = 1.
Proof.
intros * Hp Hnp.
remember (Nat.gcd p n) as g eqn:Hg; symmetry in Hg.
destruct g; [ now apply Nat.gcd_eq_0 in Hg; rewrite (proj1 Hg) in Hp | ].
destruct g; [ easy | exfalso ].
specialize (Nat.gcd_divide_l p n) as H1.
rewrite Hg in H1.
destruct H1 as (d, Hd).
specialize (prime_only_divisors p Hp (S (S g))) as H1.
assert (H : Nat.divide (S (S g)) p). {
  rewrite Hd; apply Nat.divide_factor_r.
}
specialize (H1 H); clear H.
destruct H1 as [H1| H1]; [ easy | ].
destruct d; [ now rewrite Hd in Hp | ].
rewrite Hd in H1.
destruct d. {
  rewrite Nat.mul_1_l in Hd.
  rewrite <- Hd in Hg.
  specialize (Nat.gcd_divide_r p n) as H2.
  rewrite Hg in H2.
  destruct H2 as (d2, Hd2).
  destruct d2; [ rewrite Hd2 in Hnp; flia Hnp | ].
  rewrite Hd2 in Hnp; flia Hnp.
}
replace (S (S d)) with (1 + S d) in H1 by flia.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l in H1.
rewrite <- (Nat.add_0_r (S (S g))) in H1 at 1.
now apply Nat.add_cancel_l in H1.
Qed.

Theorem prime_divisor_in_decomp : ∀ n d,
  2 ≤ n
  → prime d
  → Nat.divide d n
  → d ∈ prime_decomp n.
Proof.
intros * H2n Hd Hdn.
unfold prime_decomp.
replace n with (S (S (n - 2))) at 1 by flia H2n.
assert (prime_divisor_in_decomp_aux : ∀ cnt n d p,
  2 ≤ n
  → 2 ≤ d
  → d ≤ p
  → n + 2 ≤ cnt + d
  → prime p
  → Nat.divide p n
  → p ∈ prime_decomp_aux cnt n d). {
  clear.
  intros * H2n H2d Hdp Hcnt Hp Hpn.
  revert n d p H2n H2d Hdp Hcnt Hp Hpn.
  induction cnt; intros. {
    cbn in Hcnt; cbn.
    destruct Hpn as (k, Hk); subst n.
    apply Nat.nlt_ge in Hcnt; apply Hcnt; clear Hcnt.
    destruct k; [ flia H2n | flia Hdp ].
  }
  cbn.
  remember (n mod d) as b eqn:Hb; symmetry in Hb.
  assert (Hdz : d ≠ 0) by flia H2d.
  destruct b. 2: {
    apply IHcnt; [ easy | flia H2d | | flia Hcnt | easy | easy ].
    destruct (Nat.eq_dec p d) as [Hpd| Hpd]; [ | flia Hdp Hpd ].
    subst d; exfalso.
    apply Nat.mod_divide in Hpn; [ | easy ].
    now rewrite Hpn in Hb.
  }
  destruct (Nat.eq_dec p d) as [Hpd| Hpd]; [ now left | right ].
  apply IHcnt; [ | easy | easy | | easy | ]. {
    apply Nat.mod_divide in Hb; [ | easy ].
    destruct Hb as (k, Hk).
    rewrite Hk, Nat.div_mul; [ | easy ].
    destruct k; [ flia H2n Hk | ].
    destruct k; [ exfalso | flia ].
    rewrite Nat.mul_1_l in Hk; subst n.
    destruct Hpn as (k, Hk).
    destruct k; [ easy | ].
    destruct k; [ rewrite Nat.mul_1_l in Hk; flia Hk Hpd | ].
    apply Nat.nlt_ge in Hdp; apply Hdp; clear Hdp.
    rewrite Hk; cbn.
    destruct p; [ now rewrite Nat.mul_0_r in Hk | flia ].
  } {
    transitivity (n + 1); [ | flia Hcnt ].
    apply Nat.mod_divide in Hb; [ | easy ].
    destruct Hb as (k, Hk).
    rewrite Hk.
    rewrite Nat.div_mul; [ | easy ].
    destruct d; [ easy | ].
    destruct d; [ flia H2d | ].
    destruct k; [ flia H2n Hk | flia ].
  }
  apply Nat.mod_divide in Hb; [ | easy ].
  destruct Hpn as (k, Hk).
  rewrite Hk in Hb.
  rewrite Nat.mul_comm in Hb.
  apply Nat.gauss in Hb. {
    destruct Hb as (k', Hk').
    subst n k.
    rewrite Nat.mul_shuffle0.
    rewrite Nat.div_mul; [ | easy ].
    apply Nat.divide_factor_r.
  }
  rewrite Nat.gcd_comm.
  apply eq_gcd_prime_small_1; [ easy | ].
  flia Hdz Hdp Hpd.
}
apply prime_divisor_in_decomp_aux; [ easy | easy | | easy | easy | easy ].
now apply prime_ge_2.
Qed.

Theorem prime_decomp_in_iff : ∀ n d,
  d ∈ prime_decomp n ↔ n ≠ 0 ∧ prime d ∧ Nat.divide d n.
Proof.
intros.
split; intros Hd. {
  split; [ now intros H; subst n | ].
  split; [ now apply in_prime_decomp_is_prime in Hd | ].
  now apply in_prime_decomp_divide in Hd.
} {
  destruct Hd as (Hn & Hd & Hdn).
  destruct (lt_dec n 2) as [Hn2| Hn2]. {
    destruct n; [ easy | ].
    destruct n; [ | flia Hn2 ].
    destruct Hdn as (k, Hk).
    symmetry in Hk.
    apply Nat.eq_mul_1 in Hk.
    now destruct Hk; subst d.
  }
  apply Nat.nlt_ge in Hn2.
  now apply prime_divisor_in_decomp.
}
Qed.

Theorem prime_divide_mul : ∀ p, prime p →
  ∀ a b, Nat.divide p (a * b) → Nat.divide p a ∨ Nat.divide p b.
Proof.
intros * Hp * Hab.
destruct (Nat.eq_dec p 0) as [Hzp| Hzp]; [ now subst p | ].
destruct (Nat.eq_dec (Nat.gcd p a) 1) as [Hpa| Hpa]. {
  specialize (Nat.gauss _ _ _ Hab) as H1.
  right; apply H1, Hpa.
} {
  left.
  apply Nat.mod_divide; [ easy | ].
  destruct (Nat.eq_dec (a mod p) 0) as [Ha| Ha]; [ easy | exfalso ].
  apply Hpa; clear Hpa.
  rewrite <- Nat.gcd_mod; [ | easy ].
  rewrite Nat.gcd_comm.
  apply eq_gcd_prime_small_1; [ easy | ].
  split; [ now apply Nat.neq_0_lt_0 | ].
  now apply Nat.mod_upper_bound.
}
Qed.

Theorem prime_divides_fact_ge : ∀ n m,
  prime n
  → Nat.divide n (fact m)
  → n ≤ m.
Proof.
intros * Hn Hnm.
induction m; intros. {
  destruct Hnm as (c, Hc).
  symmetry in Hc.
  apply Nat.eq_mul_1 in Hc.
  now rewrite (proj2 Hc) in Hn.
}
rewrite Nat_fact_succ in Hnm.
specialize (Nat.gauss _ _ _ Hnm) as H1.
apply Nat.nlt_ge; intros Hnsm.
assert (H : Nat.gcd n (S m) = 1). {
  apply eq_gcd_prime_small_1; [ easy | ].
  split; [ flia | easy ].
}
specialize (H1 H); clear H.
apply Nat.nle_gt in Hnsm; apply Hnsm.
transitivity m; [ | flia ].
apply IHm, H1.
Qed.

(* https://en.wikipedia.org/wiki/Factorial#Number_theory *)
Theorem Wilson_on_composite :
  ∀ n, 5 < n → ¬ prime n ↔ fact (n - 1) mod n = 0.
Proof.
intros * H5n.
split.
-intros Hn.
 specialize (not_prime_decomp n) as H1.
 assert (H : 2 ≤ n) by flia H5n.
 specialize (H1 H Hn) as (a & b & Ha & Hb & Hab); clear H.
 apply Nat.mod_divide; [ flia H5n | ].
 assert (Han : 0 < a ≤ n - 1). {
   rewrite Hab.
   destruct a; [ easy | ].
   split; [ flia | ].
   destruct b; [ easy | ].
   destruct a; [ flia Ha | ].
   destruct b; [ flia Hb | ].
   rewrite Nat.mul_comm; flia.
 }
 destruct (Nat.eq_dec a b) as [Haeb| Haeb]. {
   subst b; clear Hb.
   rewrite Hab at 1.
   remember (a * (a - 1)) as b eqn:Hb.
   apply (Nat.divide_trans _ (a * b)). {
     subst b.
     rewrite Nat.mul_assoc.
     apply Nat.divide_factor_l.
   }
   assert (Haa : a ≠ b). {
     intros H.
     rewrite <- (Nat.mul_1_r a) in H; subst b.
     apply Nat.mul_cancel_l in H; [ | flia Ha ].
     replace a with 2 in Hab by flia H.
     flia H5n Hab.
   }
   assert (Hbn : 0 < b ≤ n - 1). {
     rewrite Hb, Hab.
     split. {
       destruct a; [ easy | ].
       rewrite Nat.sub_succ, Nat.sub_0_r.
       destruct a; [ flia Ha | flia ].
     }
     rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
     apply Nat.sub_le_mono_l; flia Ha.
   }
   clear - Haa Han Hbn.
   remember (n - 1) as m; clear n Heqm.
   rename m into n; move n at top.
   destruct (lt_dec a b) as [Hab| Hab].
   -now apply Nat_divide_mul_fact.
   -assert (H : b < a) by flia Haa Hab.
    rewrite Nat.mul_comm.
    now apply Nat_divide_mul_fact.
 }
 rewrite Hab at 1.
 assert (Hbn : 0 < b ≤ n - 1). {
   rewrite Hab.
   destruct b; [ easy | ].
   split; [ flia | ].
   destruct a; [ easy | ].
   destruct b; [ flia Hb | ].
   destruct a; [ flia Ha | flia ].
 }
 destruct (lt_dec a b) as [Halb| Halb].
 +now apply Nat_divide_mul_fact.
 +assert (H : b < a) by flia Halb Haeb.
  rewrite Nat.mul_comm.
  now apply Nat_divide_mul_fact.
-intros Hn Hp.
 apply Nat.mod_divide in Hn; [ | flia H5n ].
 specialize (prime_divides_fact_ge _ _ Hp Hn) as H1.
 flia H5n H1.
Qed.

(* Questions
   - How to write a function "next_prime" computing the prime number
     after a given n ?
   - How to be able to test "Compute (next_prime n)" without having to
     give (and compute) a too big upper bound, like this famous n! + 1 ?
   - How to give an proved correct upper bound such that the proof is
     not too complicated ?
   Solution
     The function "next_prime" below.
   How does it work ?
     It first makes n iterations. Bertrand's Postulate claims that,
     inside these n iterations (up to 2n), a prime number is found.
     So we can do "Compute (next_prime n)" fast enough.
       If n iterations are reached, the function calls a function
     named "phony_prime_after", giving it n! + 1 as maximum number
     of iterations. It is proven that it is a sufficient upper
     bound. But, in practice, when testing "Compute (next_prime n)",
     this function is never called.
       So this computation remains fast and proven that it returns
     a prime number, with a short proof.
 *)

Fixpoint phony_prime_after niter n :=
  if is_prime n then n
  else
    match niter with
    | 0 => 0
    | S niter' => phony_prime_after niter' (n + 1)
    end.

Fixpoint prime_after_aux niter n :=
  if is_prime n then n
  else
    match niter with
    | 0 =>
        (* point never reached and phony_prime_after never called
           thanks to Bertrand's Postulate *)
        (* except, actually when n = 0, and then fact n + 1 = 2,
           not a big deal, fastly computed *)
        (* this code serves to prove that prime_after always
           answers a prime number, i.e. phony_prime_after never
           answers 0 *)
        (* something: after the iterations of the present function,
           the value of n is twice the value of the initial n,
           so we are actually searching the next prime number
           after 2n; no important, this code is just for proofs. *)
        phony_prime_after (fact n + 1) n
    | S niter' =>
        prime_after_aux niter' (n + 1)
    end.

Definition prime_after n := prime_after_aux n n.

(* "prime_after n" is indeed a prime *)

Lemma bounded_phony_prime_after : ∀ n p,
  n < p
  → prime p
  → prime (phony_prime_after (p - n) n).
Proof.
intros * Hnm Hm.
remember (p - n) as niter eqn:Hniter.
replace p with (niter + n) in * by flia Hniter Hnm.
clear p Hnm Hniter.
revert n Hm.
induction niter; intros. {
  cbn in Hm; cbn.
  remember (is_prime n) as b eqn:Hb; symmetry in Hb.
  destruct b; [ easy |].
  now apply Bool.not_true_iff_false in Hb.
}
cbn.
remember (is_prime n) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
apply IHniter.
now replace (S niter + n) with (niter + (n + 1)) in Hm by flia.
Qed.

Lemma phony_prime_after_is_prime : ∀ n,
  prime (phony_prime_after (fact n + 1) n).
Proof.
intros.
specialize (next_prime_bounded n) as (m & Hm & Hmp).
specialize (bounded_phony_prime_after n m (proj1 Hm) Hmp) as H1.
remember (fact n + 1) as niter1.
remember (m - n) as niter2.
assert (Hni : niter2 ≤ niter1). {
  subst niter1 niter2; flia Hm.
}
clear Hm Heqniter1 Heqniter2 Hmp.
move niter2 before niter1.
revert n niter2 H1 Hni.
induction niter1; intros. {
  now apply Nat.le_0_r in Hni; subst niter2.
}
cbn.
destruct niter2; cbn in H1; [ now destruct (is_prime n) | ].
apply Nat.succ_le_mono in Hni.
destruct (is_prime n); [ easy | ].
now apply IHniter1 in H1.
Qed.

Lemma prime_after_aux_is_prime : ∀ niter n,
  prime (prime_after_aux niter n).
Proof.
intros.
revert n.
induction niter; intros. {
  cbn - [ "/" ].
  remember (is_prime n) as b eqn:Hb; symmetry in Hb.
  destruct b; [ easy | ].
  apply phony_prime_after_is_prime.
}
cbn.
remember (is_prime n) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
apply IHniter.
Qed.

Theorem prime_after_is_prime : ∀ n, prime (prime_after n).
Proof.
intros.
apply prime_after_aux_is_prime.
Qed.

(* "prime_after n" is indeed after (greater or equal to) n *)

Lemma bounded_phony_prime_after_is_after : ∀ n p,
  n ≤ p
  → prime p
  → n ≤ phony_prime_after (p - n) n.
Proof.
intros * Hnm Hm.
remember (p - n) as niter eqn:Hniter.
replace p with (niter + n) in * by flia Hniter Hnm.
clear p Hnm Hniter.
revert n Hm.
induction niter; intros. {
  cbn in Hm; cbn.
  unfold prime in Hm.
  now destruct (is_prime n).
}
cbn.
destruct (is_prime n); [ easy | ].
transitivity (n + 1); [ flia | ].
apply IHniter.
now replace (S niter + n) with (niter + (n + 1)) in Hm by flia.
Qed.

Lemma phony_prime_after_is_after : ∀ n,
  n ≤ phony_prime_after (fact n + 1) n.
Proof.
intros.
specialize (next_prime_bounded n) as (m & Hm & Hmp).
specialize (bounded_phony_prime_after_is_after n m) as H1.
specialize (H1 (Nat.lt_le_incl _ _ (proj1 Hm)) Hmp).
etransitivity; [ apply H1 | ].
clear H1.
remember (m - n) as k eqn:Hk.
replace m with (n + k) in Hmp by flia Hk Hm.
replace (fact n + 1) with (k + (fact n + 1 - k)) by flia Hm Hk.
remember (fact n + 1 - k) as l eqn:Hl.
clear m Hm Hk Hl; move l before k.
revert n l Hmp.
induction k; intros; cbn. {
  rewrite Nat.add_0_r in Hmp.
  unfold prime in Hmp.
  now destruct l; cbn; destruct (is_prime n).
}
destruct (is_prime n); [ easy | ].
replace (n + S k) with (n + 1 + k) in Hmp by flia.
now apply IHk.
Qed.

Lemma prime_after_aux_is_after : ∀ niter n, n ≤ prime_after_aux niter n.
Proof.
intros.
revert n.
induction niter; intros; cbn. {
  destruct (is_prime n); [ easy | ].
  apply phony_prime_after_is_after.
}
destruct (is_prime n); [ easy | ].
transitivity (n + 1); [ flia | apply IHniter ].
Qed.

Theorem prime_after_is_after : ∀ n, n ≤ prime_after n.
Proof.
intros.
apply prime_after_aux_is_after.
Qed.

(* there is no prime between "n" and "next_prime n" *)

Lemma no_prime_before_phony_prime_after : ∀ n i,
  ¬ prime n
  → n ≤ i < phony_prime_after (fact n + 1) n
  → ¬ prime i.
Proof.
intros * Hb Hni.
specialize (next_prime_bounded n) as (p & Hp & Hpp).
specialize (phony_prime_after_is_prime n) as Hpq.
remember (phony_prime_after (fact n + 1) n) as q eqn:Hq.
clear p Hp Hpp.
remember (fact n + 1) as it eqn:Hit; clear Hit.
remember (i - n) as j eqn:Hj.
replace i with (n + j) in * by flia Hj Hni.
clear i Hj.
destruct Hni as (_, Hnj).
revert it q n Hb Hnj Hq Hpq.
induction j; intros; [ now rewrite Nat.add_0_r | ].
rewrite <- Nat.add_succ_comm in Hnj |-*.
apply Bool.not_true_iff_false in Hb.
destruct it; cbn in Hq. {
  destruct (is_prime n); [ easy | now subst q ].
}
rewrite Nat.add_1_r in Hq.
destruct (is_prime n); [ easy | clear Hb ].
destruct it. {
  remember (S n) as sn; cbn in Hq; subst sn.
  destruct (is_prime (S n)); subst q; [ flia Hnj | easy ].
}
remember (S n) as sn; cbn in Hq; subst sn.
remember (is_prime (S n)) as b eqn:Hb; symmetry in Hb.
destruct b; [ now subst q; flia Hnj | ].
eapply (IHj (S it)); [ | apply Hnj | | easy ]. {
  now apply Bool.not_true_iff_false in Hb.
}
now remember (S n) as sn; cbn; rewrite Hb.
Qed.

Theorem phony_prime_after_more_iter : ∀ k n niter,
  fact n + 1 ≤ niter
  → phony_prime_after niter n = phony_prime_after (niter + k) n.
Proof.
intros * Hnit.
specialize (next_prime_bounded n) as (p & Hnp & Hpp).
remember (p - n) as i eqn:Hi.
replace p with (n + i) in * by flia Hi Hnp.
clear Hi; destruct Hnp as (_, Hnp).
assert (Hni : i ≤ niter) by flia Hnit Hnp.
clear p Hnit Hnp.
revert i k n Hpp Hni.
induction niter; intros. {
  apply Nat.le_0_r in Hni.
  rewrite Hni, Nat.add_0_r in Hpp; cbn.
  unfold prime in Hpp.
  rewrite Hpp.
  now destruct k; cbn; rewrite Hpp.
}
cbn.
remember (is_prime n) as b eqn:Hb; symmetry in Hb.
destruct b; [ easy | ].
apply Bool.not_true_iff_false in Hb.
unfold prime in Hpp.
destruct i; [ now rewrite Nat.add_0_r in Hpp | ].
apply Nat.succ_le_mono in Hni.
replace (n + S i) with (n + 1 + i) in Hpp by flia.
now apply (IHniter i).
Qed.

Lemma no_prime_before_after_aux : ∀ niter n i,
  n ≤ i < prime_after_aux niter n → ¬ prime i.
Proof.
intros * Hni.
destruct niter. {
  cbn - [ "/" ] in Hni.
  remember (is_prime n) as b eqn:Hb; symmetry in Hb.
  destruct b; [ flia Hni | ].
  apply Bool.not_true_iff_false in Hb.
  now apply (no_prime_before_phony_prime_after n).
}
cbn in Hni.
remember (is_prime n) as b eqn:Hb; symmetry in Hb.
destruct b; [ flia Hni | ].
revert n i Hb Hni.
induction niter; intros. {
  cbn in Hni.
  remember (is_prime (n + 1)) as b eqn:Hb1; symmetry in Hb1.
  apply Bool.not_true_iff_false in Hb.
  destruct b; [ now replace i with n by flia Hni | ].
  apply (no_prime_before_phony_prime_after n); [ easy | ].
  split; [ easy | ].
  eapply lt_le_trans; [ apply Hni | ].
  rewrite (phony_prime_after_more_iter (fact (n + 1) - fact n + 1) n);
    [ | easy ].
  replace (fact n + 1 + (fact (n + 1) - fact n + 1)) with
      (S (fact (n + 1) + 1)). 2: {
    rewrite (Nat.add_1_r n).
    cbn; flia.
  }
  cbn.
  now destruct (is_prime n).
}
cbn in Hni.
remember (is_prime (n + 1)) as b1 eqn:Hb1; symmetry in Hb1.
apply Bool.not_true_iff_false in Hb.
destruct b1; [ now replace i with n by flia Hni | ].
destruct (Nat.eq_dec n i) as [Hni1| Hni1]; [ now subst i | ].
apply (IHniter (n + 1)); [ easy | ].
split; [ | easy ].
flia Hni Hni1.
Qed.

Theorem no_prime_before_after : ∀ n i,
  n ≤ i < prime_after n → ¬ prime i.
Proof.
intros * Hni.
now apply (no_prime_before_after_aux n n i).
Qed.

(* thanks to the code, 510! + 1 is not computed in this example;
   otherwise this would not answer *)

(*
Compute (prime_after 510).
*)

Theorem Nat_gcd_prime_fact_lt : ∀ p,
  prime p → ∀ k, k < p → Nat.gcd p (fact k) = 1.
Proof.
intros * Hp * Hkp.
induction k; [ apply Nat.gcd_1_r | ].
rewrite Nat_fact_succ.
apply Nat_gcd_1_mul_r; [ | apply IHk; flia Hkp ].
apply eq_gcd_prime_small_1; [ easy | flia Hkp ].
Qed.

(* nth prime *)

Fixpoint nth_prime_aux cnt n :=
  let p := prime_after n in
  match cnt with
  | 0 => p
  | S c => nth_prime_aux c (p + 1)
  end.

Definition nth_prime n := nth_prime_aux (n - 1) 0.

(*
Compute (nth_prime 30).
*)

(* slow but simple *)

Definition firstn_primes n := map nth_prime (seq 1 n).

(* fast but complicated *)

Fixpoint firstn_primes_loop n p :=
  match n with
  | 0 => []
  | S n' =>
      let p' := prime_after p in
      p' :: firstn_primes_loop n' (p' + 1)
  end.

Definition firstn_primes' n := firstn_primes_loop n 0.

(*
Time Compute (let n := 50 in firstn_primes n).
Time Compute (let n := 50 in firstn_primes' n).
Time Compute (let n := 100 in firstn_primes' n).
*)

(*
Time Compute (firstn_primes 100).   (* slow *)
Time Compute (firstn_primes' 100).  (* fast *)
*)

Notation "a ^ b" := (Nat.pow a b) : nat_scope.

(* binomial *)

Fixpoint binomial n k :=
  match k with
  | 0 => 1
  | S k' =>
      match n with
      | 0 => 0
      | S n' => binomial n' k' + binomial n' k
     end
  end.

Theorem binomial_succ_succ : ∀ n k,
  binomial (S n) (S k) = binomial n k + binomial n (S k).
Proof. easy. Qed.

Theorem binomial_succ_r : ∀ n k,
  binomial n (S k) =
    match n with
    | 0 => 0
    | S n' => binomial n' k + binomial n' (S k)
    end.
Proof.
intros.
now destruct n.
Qed.

Theorem binomial_lt : ∀ n k, n < k → binomial n k = 0.
Proof.
intros * Hnk.
revert k Hnk.
induction n; intros; [ now destruct k | cbn ].
destruct k; [ flia Hnk | ].
apply Nat.succ_lt_mono in Hnk.
rewrite IHn; [ | easy ].
rewrite Nat.add_0_l.
apply IHn; flia Hnk.
Qed.

Theorem binomial_succ_diag_r : ∀ n, binomial n (S n) = 0.
Proof.
intros.
apply binomial_lt; flia.
Qed.

Theorem binomial_0_r : ∀ n, binomial n 0 = 1.
Proof. now intros; destruct n. Qed.

Theorem binomial_diag : ∀ n, binomial n n = 1.
Proof.
intros.
induction n; [ easy | cbn ].
now rewrite IHn, binomial_succ_diag_r, Nat.add_0_r.
Qed.

(* Code by Ralph D. Jeffords at math.stackexchange.com *)

(* product of k consecutive numbers from n to n+k-1 *)
(* prod_consec (m,k) = m...(m+k-1) *)
Definition prod_consec k n := fact (n + k - 1) / fact (n - 1).

Lemma prod_consec_rec_formula : ∀ m k,
  2 ≤ m
  → 2 ≤ k
  → prod_consec k m = k * prod_consec (k - 1) m + prod_consec k (m - 1).
Proof.
intros * H2m H2k.
replace (prod_consec k m) with (prod_consec (k - 1) m * (k + (m - 1))). 2: {
  unfold prod_consec.
  replace (m + (k - 1) - 1) with (m + k - 2) by flia H2k.
  replace (m + k - 1) with (S (m + k - 2)) by flia H2m.
  rewrite Nat_fact_succ.
  replace (S (m + k - 2)) with (m + k - 1) by flia H2m.
  rewrite Nat.divide_div_mul_exact; [ | apply fact_neq_0 | ]. 2: {
    apply Nat_le_divides_fact; flia H2k.
  }
  rewrite Nat.mul_comm; f_equal; flia H2m.
}
rewrite Nat.mul_comm, Nat.mul_add_distr_r; f_equal.
unfold prod_consec.
replace (m - 1 - 1) with (m - 2) by flia H2m.
replace (m + (k - 1) - 1) with (m + k - 2) by flia H2k.
replace (m - 1 + k - 1) with (m + k - 2) by flia H2m.
specialize (Nat_le_divides_fact (m + k - 2) (m - 1)) as H1.
assert (H :  m - 1 ≤ m + k - 2) by flia H2k.
specialize (H1 H) as (c, Hc); clear H.
rewrite Hc, Nat.div_mul; [ | apply fact_neq_0 ].
replace (m - 1) with (S (m - 2)) by flia H2m.
rewrite Nat_fact_succ, Nat.mul_assoc.
rewrite Nat.div_mul; [ | apply fact_neq_0 ].
apply Nat.mul_comm.
Qed.

Theorem divide_fact_prod_consec : ∀ k m,
  1 ≤ m
  → 1 ≤ k
  → Nat.divide (fact k) (prod_consec k m).
Proof.
intros * H1m H1k.
remember (m + k) as n eqn:Hn.
assert (H : m + k ≤ n) by flia Hn.
clear Hn; rename H into Hn.
revert k m Hn H1m H1k.
induction n as (n, IHn) using lt_wf_rec; intros.
destruct (Nat.eq_dec n 2) as [Hn2| Hn2]. {
  replace m with 1 by flia Hn H1m H1k Hn2.
  replace k with 1 by flia Hn H1m H1k Hn2.
  apply Nat.divide_refl.
}
destruct (Nat.eq_dec m 1) as [Hm1| Hm1]. {
  subst m; unfold prod_consec.
  rewrite Nat.add_comm, Nat.add_sub, Nat.sub_diag.
  rewrite Nat.div_1_r.
  apply Nat.divide_refl.
}
destruct (Nat.eq_dec k 1) as [Hk1| Hk1]. {
  subst k; apply Nat.divide_1_l.
}
assert (H2m : 2 ≤ m) by flia H1m Hm1.
assert (H2k : 2 ≤ k) by flia H1k Hk1.
specialize (prod_consec_rec_formula m k H2m H2k) as H1.
assert (Hmn : m + (k - 1) < n) by flia Hn H2k.
assert (H1k1 : 1 ≤ k - 1) by flia H2k.
specialize (IHn (m + (k - 1)) Hmn (k - 1) m (le_refl _) H1m H1k1) as H2.
apply (Nat.mul_divide_mono_l _ _ k) in H2.
replace k with (S (k - 1)) in H2 at 1 by flia H1k.
rewrite <- Nat_fact_succ in H2.
replace (S (k - 1)) with k in H2 by flia H1k.
rewrite H1.
apply Nat.divide_add_r; [ easy | ].
apply (IHn (m - 1 + k)); [ flia Hn H2m | easy | flia H2m | easy ].
Qed.

Theorem fact_divides_fact_over_fact : ∀ k n,
  k ≤ n
  → Nat.divide (fact k) (fact n / fact (n - k)).
Proof.
intros * Hkn.
destruct (Nat.eq_dec k 0) as [Hkz| Hkz]. {
  subst k; apply Nat.divide_1_l.
}
specialize (divide_fact_prod_consec k (n - k + 1)) as H1.
unfold prod_consec in H1.
rewrite Nat.add_shuffle0 in H1.
do 2 rewrite Nat.add_sub in H1.
rewrite Nat.sub_add in H1; [ | easy ].
apply H1; [ flia Hkn | flia Hkz ].
Qed.

Theorem fact_fact_divides_fact : ∀ k n,
  k ≤ n
  → Nat.divide (fact k * fact (n - k)) (fact n).
Proof.
intros * Hkn.
specialize (fact_divides_fact_over_fact k n Hkn) as H1.
apply (Nat.mul_divide_cancel_r _ _ (fact (n - k))) in H1. 2: {
  apply fact_neq_0.
}
eapply Nat.divide_trans; [ apply H1 | ].
rewrite Nat.mul_comm.
rewrite <- (proj2 (Nat.div_exact _ _ (fact_neq_0 _))). 2: {
  apply Nat.mod_divide; [ apply fact_neq_0 | ].
  apply Nat_divide_fact_fact.
}
apply Nat.divide_refl.
Qed.

Theorem binomial_fact : ∀ n k,
  k ≤ n
  → binomial n k = fact n / (fact k * fact (n - k)).
Proof.
intros * Hkn.
revert k Hkn.
induction n; intros; [ now apply Nat.le_0_r in Hkn; subst k | ].
destruct k. {
  cbn; rewrite Nat.add_0_r.
  symmetry; apply Nat.div_same.
  intros H; apply Nat.eq_add_0 in H.
  destruct H as (H, _).
  now apply fact_neq_0 in H.
}
apply Nat.succ_le_mono in Hkn.
rewrite Nat.sub_succ.
rewrite binomial_succ_r.
rewrite IHn; [ | easy ].
destruct (Nat.eq_dec k n) as [Hken| Hken]. {
  rewrite Hken.
  rewrite Nat.sub_diag.
  rewrite Nat.mul_1_r, Nat.div_same; [ | apply fact_neq_0 ].
  rewrite Nat.mul_1_r, Nat.div_same; [ | apply fact_neq_0 ].
  now rewrite binomial_succ_diag_r, Nat.add_0_r.
}
assert (H : k < n) by flia Hkn Hken.
clear Hkn Hken; rename H into Hkn.
rewrite IHn; [ | flia Hkn ].
(* lemma to do, perhaps? *)
replace (n - k) with (S (n - S k)) by flia Hkn.
do 3 rewrite Nat_fact_succ.
replace (S (n - S k)) with (n - k) by flia Hkn.
rewrite (Nat.mul_comm (fact k)).
rewrite Nat.mul_shuffle0.
do 2 rewrite <- Nat.mul_assoc.
rewrite <- Nat.div_div; [ | flia Hkn | ]. 2: {
  apply Nat.neq_mul_0; split; apply fact_neq_0.
}
rewrite <- (Nat.div_div _ (S k)); [ | easy | ]. 2: {
  apply Nat.neq_mul_0; split; apply fact_neq_0.
}
rewrite Nat_add_div_same. 2: {
  replace (fact (n - S k)) with (fact (n - k) / (n - k)). 2: {
    replace (n - k) with (S (n - S k)) by flia Hkn.
    rewrite Nat_fact_succ.
    rewrite Nat.mul_comm, Nat.div_mul; [ easy | ].
    flia Hkn.
  }
  rewrite <- Nat.divide_div_mul_exact; [ | flia Hkn | ]. 2: {
    apply Nat_divide_small_fact; flia Hkn.
  }
  apply (Nat.mul_divide_cancel_l _ _ (n - k)); [ flia Hkn | ].
  rewrite <- Nat.divide_div_mul_exact; [ | flia Hkn | ]. 2: {
    apply (Nat.divide_trans _ (fact (n - k))). {
      apply Nat_divide_small_fact; flia Hkn.
    }
    apply Nat.divide_factor_r.
  }
  rewrite Nat.mul_comm, Nat.div_mul; [ | flia Hkn ].
  rewrite <- Nat.divide_div_mul_exact; [ | flia Hkn | ]. 2: {
    apply Nat_divide_small_fact; flia Hkn.
  }
  rewrite (Nat.mul_comm (n - k)), Nat.div_mul; [ | flia Hkn ].
  now apply fact_fact_divides_fact, Nat.lt_le_incl.
}
rewrite Nat.mul_shuffle1.
rewrite <- (Nat.div_div (S n * _)); cycle 1. {
  apply Nat.neq_mul_0; split; [ easy | flia Hkn ].
} {
  apply Nat.neq_mul_0; split; apply fact_neq_0.
}
f_equal.
(* lemma to do, perhaps? *)
rewrite <- (Nat.div_mul_cancel_l _ _ (S k)); [ | flia Hkn | easy ].
rewrite <- (Nat.div_mul_cancel_r (fact n) _ (n - k)); [ | easy | flia Hkn ].
rewrite Nat_add_div_same. 2: {
  apply Nat.mul_divide_cancel_l; [ easy | ].
  apply Nat_divide_small_fact; flia Hkn.
}
f_equal.
rewrite (Nat.mul_comm (fact n)), <- Nat.mul_add_distr_r.
f_equal.
flia Hkn.
Qed.

Theorem newton_binomial : ∀ n a b,
  (a + b) ^ n = Σ (k = 0, n), binomial n k * a ^ (n - k) * b ^ k.
Proof.
intros.
induction n; [ easy | ].
cbn - [ "-" binomial ].
rewrite IHn.
rewrite mul_summation_distr_l.
rewrite mul_add_distr_r_in_summation.
rewrite summation_add.
do 2 rewrite <- double_mul_assoc_in_summation.
rewrite power_shuffle1_in_summation.
rewrite power_shuffle2_in_summation.
symmetry.
rewrite summation_split_first; [ | flia ].
unfold binomial at 1.
rewrite Nat.mul_1_l, Nat.sub_0_r, Nat.pow_0_r, Nat.mul_1_r at 1.
rewrite summation_succ_succ.
cbn - [ "-" "^" ].
rewrite mul_assoc_in_summation.
rewrite mul_add_distr_r_in_summation.
rewrite summation_add.
rewrite Nat.add_assoc.
do 2 rewrite <- mul_assoc_in_summation.
rewrite Nat.add_shuffle0.
f_equal.
rewrite <- (summation_succ_succ 0 n (λ i, binomial n i * a ^ (S n - i) * b ^ i)).
rewrite summation_split_last; [ | flia | flia ].
replace (S n - 1) with n by flia.
rewrite binomial_succ_diag_r, Nat.mul_0_l, Nat.add_0_r.
symmetry.
rewrite summation_split_first; [ | flia ].
now rewrite binomial_0_r, Nat.mul_1_l, Nat.sub_0_r, Nat.pow_0_r, Nat.mul_1_r.
Qed.

Theorem binomial_prime : ∀ p k,
  prime p
  → 1 ≤ k ≤ p - 1
  → Nat.divide p (binomial p k).
Proof.
intros * Hp Hkp.
rewrite binomial_fact; [ | flia Hkp ].
assert (Hffz : fact k * fact (p - k) ≠ 0). {
  apply Nat.neq_mul_0; split; apply fact_neq_0.
}
apply (Nat.gauss _ (fact k * fact (p - k))). {
  rewrite <- (proj2 (Nat.div_exact _ _ Hffz)). 2: {
    apply Nat.mod_divide; [ easy | ].
    apply fact_fact_divides_fact; flia Hkp.
  }
  apply Nat_divide_small_fact; flia Hkp.
}
assert (Hjp : p - k ≤ p - 1) by flia Hkp.
remember (p - k) as j; move j before p.
clear Hffz Heqj; destruct Hkp as (_, Hkp).
move Hjp before Hkp; rewrite Nat.mul_comm.
(* lemma, perhaps? *)
revert j Hjp.
induction k; intros. {
  rewrite Nat.mul_1_r.
  clear Hkp.
  induction j; [ apply Nat.gcd_1_r | ].
  rewrite Nat_fact_succ.
  apply Nat_gcd_1_mul_r. {
    apply eq_gcd_prime_small_1; [ easy | flia Hjp ].
  }
  apply IHj; flia Hjp.
}
rewrite Nat_fact_succ, Nat.mul_comm, <- Nat.mul_assoc.
apply Nat_gcd_1_mul_r. {
  apply eq_gcd_prime_small_1; [ easy | flia Hkp ].
}
rewrite Nat.mul_comm.
apply IHk; [ flia Hkp | easy ].
Qed.

Theorem sum_power_prime_mod : ∀ p, prime p →
  ∀ a b, (a + b) ^ p mod p = (a ^ p + b ^ p) mod p.
Proof.
intros * Hp *.
rewrite newton_binomial.
rewrite summation_split_first; [ | flia ].
rewrite binomial_0_r, Nat.mul_1_l, Nat.sub_0_r, Nat.pow_0_r, Nat.mul_1_r.
specialize (prime_ge_2 p Hp) as H2p.
rewrite summation_split_last; [ | flia H2p | flia H2p ].
rewrite binomial_diag.
rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r, Nat.mul_1_l.
rewrite Nat.add_assoc, Nat.add_shuffle0.
symmetry.
remember (a ^ p + b ^ p) as x.
replace x with (x + 0) at 1 by flia.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | flia H2p ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | flia H2p ].
f_equal; f_equal; clear x Heqx; symmetry.
rewrite Nat.mod_0_l; [ | flia H2p ].
rewrite summation_mod_idemp.
rewrite all_0_summation_0. {
  rewrite Nat.mod_0_l; [ easy | flia H2p ].
}
intros i Hi.
specialize (binomial_prime _ _ Hp Hi) as (c, Hc).
rewrite Hc, (Nat.mul_comm c).
do 2 rewrite <- Nat.mul_assoc.
rewrite Nat.mul_comm.
apply Nat.mod_mul; flia H2p.
Qed.

Theorem smaller_than_prime_all_different_multiples : ∀ p,
  prime p
  → ∀ a, 1 ≤ a < p
  → ∀ i j, i < j < p → (i * a) mod p ≠ (j * a) mod p.
Proof.
intros * Hp * Hap * Hijp.
intros Haa; symmetry in Haa.
apply Nat_mul_mod_cancel_r in Haa. 2: {
  rewrite Nat.gcd_comm.
  now apply eq_gcd_prime_small_1.
}
rewrite Nat.mod_small in Haa; [ | easy ].
rewrite Nat.mod_small in Haa; [ | flia Hijp ].
flia Hijp Haa.
Qed.

Theorem fold_left_mul_map_mod : ∀ a b l,
  fold_left Nat.mul (map (λ i, i mod a) l) b mod a =
  fold_left Nat.mul l b mod a.
Proof.
intros.
destruct (Nat.eq_dec a 0) as [Haz| Haz].
subst a. simpl. try rewrite map_id. reflexivity.
induction l as [| c l]; [ easy | cbn ].
rewrite <- List_fold_left_mul_assoc.
rewrite Nat.mul_mod_idemp_r; [ | easy ].
rewrite <- Nat.mul_mod_idemp_l; [ | easy ].
rewrite IHl.
rewrite Nat.mul_mod_idemp_l; [ | easy ].
now rewrite List_fold_left_mul_assoc.
Qed.

Theorem fold_left_mul_map_mul : ∀ b c l,
  fold_left Nat.mul (map (λ a, a * b) l) c =
  fold_left Nat.mul l c * b ^ length l.
Proof.
intros.
induction l as [| a l]; [ now cbn; rewrite Nat.mul_1_r | cbn ].
do 2 rewrite <- List_fold_left_mul_assoc.
rewrite IHl; flia.
Qed.

Theorem fact_eq_fold_left : ∀ n,
  fact n = fold_left Nat.mul (seq 1 n) 1.
Proof.
induction n; intros; [ easy | ].
rewrite <- (Nat.add_1_r n) at 2.
rewrite seq_app.
rewrite fold_left_app.
now rewrite <- IHn, Nat_fact_succ, Nat.mul_comm.
Qed.

Theorem fermat_little : ∀ p,
  prime p → ∀ a, 1 ≤ a < p → a ^ (p - 1) mod p = 1.
Proof.
intros * Hp * Hap.
specialize (smaller_than_prime_all_different_multiples p Hp a Hap) as H1.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
assert
  (Hperm :
     Permutation (map (λ i, (i * a) mod p) (seq 1 (p - 1)))
       (seq 1 (p - 1))). {
  apply NoDup_Permutation_bis; try apply seq_NoDup; cycle 1. {
    now rewrite map_length, seq_length.
  } {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    apply in_seq in Hj.
    rewrite <- Hji.
    apply in_seq.
    replace (1 + (p - 1)) with p in Hj |-* by flia Hpz.
    split; [ | now apply Nat.mod_upper_bound ].
    apply Nat.neq_0_lt_0.
    intros Hi.
    apply Nat.mod_divide in Hi; [ | easy ].
    specialize (Nat.gauss _ _ _ Hi) as H2.
    assert (H : Nat.gcd p j = 1) by now apply eq_gcd_prime_small_1.
    specialize (H2 H); clear H.
    destruct H2 as (c, Hc).
    rewrite Hc in Hap.
    destruct c; [ easy | ].
    cbn in Hap; flia Hap.
  } {
    remember (λ i, (i * a) mod p) as f eqn:Hf.
    assert (H2 : ∀ i j, i < j < p → f i ≠ f j) by now rewrite Hf.
    assert
      (H : ∀ {A} start len (f : nat → A),
         (∀ i j, i < j < start + len → f i ≠ f j)
         → NoDup (map f (seq start len))). {
      clear; intros * Hij.
      remember (seq start len) as l eqn:Hl; symmetry in Hl.
      revert start len Hij Hl; induction l as [| i l]; intros; [ constructor | ].
      rewrite map_cons; constructor. {
        intros H1.
        apply in_map_iff in H1.
        destruct H1 as (j & Hji & Hj).
        destruct len; [ easy | cbn in Hl ].
        injection Hl; clear Hl; intros Hl Hb; subst i.
        specialize (Hij start j) as H1.
        assert (H : start < j < start + S len). {
          rewrite <- Hl in Hj.
          apply in_seq in Hj; flia Hj.
        }
        specialize (H1 H); clear H.
        now symmetry in Hji.
      }
      destruct len; [ easy | ].
      injection Hl; clear Hl; intros Hl Hi.
      apply (IHl (S start) len); [ | easy ].
      intros j k Hjk.
      apply Hij; flia Hjk.
    }
    apply H.
    now replace (1 + (p - 1)) with p by flia Hpz.
  }
}
remember (λ i : nat, (i * a) mod p) as f eqn:Hf.
remember (fold_left Nat.mul (map f (seq 1 (p - 1))) 1) as x eqn:Hx.
assert (Hx1 : x mod p = fact (p - 1) mod p). {
  subst x.
  erewrite Permutation_fold_mul; [ | apply Hperm ].
  f_equal.
  clear.
  (* lemma perhaps? *)
  remember (p - 1) as n; clear p Heqn.
  symmetry.
  apply fact_eq_fold_left.
}
assert (Hx2 : x mod p = (fact (p - 1) * a ^ (p - 1)) mod p). {
  subst x; rewrite Hf.
  rewrite <- (map_map (λ i, i * a) (λ j, j mod p)).
  rewrite fold_left_mul_map_mod.
  rewrite fold_left_mul_map_mul.
  rewrite seq_length.
  f_equal; f_equal.
  symmetry.
  apply fact_eq_fold_left.
}
rewrite Hx2 in Hx1.
rewrite <- (Nat.mul_1_r (fact _)) in Hx1 at 2.
apply Nat_mul_mod_cancel_l in Hx1. 2: {
  rewrite Nat.gcd_comm.
  apply Nat_gcd_prime_fact_lt; [ easy | flia Hpz ].
}
rewrite (Nat.mod_small 1) in Hx1; [ easy | flia Hap ].
Qed.

(* proof simpler than fermat_little; but could be a corollary *)
Theorem fermat_little_1 : ∀ p, prime p → ∀ a, a ^ p mod p = a mod p.
Proof.
intros * Hp *.
induction a. {
  rewrite Nat.pow_0_l; [ easy | ].
  now intros H; rewrite H in Hp.
}
rewrite <- Nat.add_1_r.
rewrite sum_power_prime_mod; [ | easy ].
rewrite Nat.pow_1_l.
rewrite <- Nat.add_mod_idemp_l; [ | now intros H; rewrite H in Hp ].
rewrite IHa.
rewrite Nat.add_mod_idemp_l; [ easy | now intros H; rewrite H in Hp ].
Qed.

(* inverse modulo (true when n is prime) *)

Definition inv_mod i n := Nat_pow_mod i (n - 2) n.

Theorem pow_mod_prime_ne_0 : ∀ i n p,
  prime p
  → 1 ≤ i < p
  → i ^ n mod p ≠ 0.
Proof.
intros * Hp Hip Hinp.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
apply Nat.mod_divide in Hinp; [ | easy ].
induction n. {
  cbn in Hinp.
  destruct Hinp as (c, Hc).
  symmetry in Hc.
  apply Nat.eq_mul_1 in Hc.
  now rewrite (proj2 Hc) in Hp.
}
cbn in Hinp.
specialize (Nat.gauss _ _ _ Hinp) as H1.
assert (H : Nat.gcd p i = 1) by now apply eq_gcd_prime_small_1.
specialize (H1 H); clear H.
apply IHn, H1.
Qed.

Theorem inv_mod_interv : ∀ p, prime p →
  ∀ i, 2 ≤ i ≤ p - 2 → 2 ≤ inv_mod i p ≤ p - 2.
Proof.
intros * Hp * Hip.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
unfold inv_mod.
rewrite Nat_pow_mod_is_pow_mod; [ | now intros H; subst p ].
split. {
  apply Nat.nlt_ge; intros Hi.
  remember (i ^ (p - 2) mod p) as j eqn:Hj; symmetry in Hj.
  destruct j. {
    revert Hj.
    apply pow_mod_prime_ne_0; [ easy | flia Hip ].
  }
  destruct j; [ clear Hi | flia Hi ].
  specialize (fermat_little p Hp i) as H1.
  assert (H : 1 ≤ i < p) by flia Hip.
  specialize (H1 H); clear H.
  replace (p - 1) with (S (p - 2)) in H1 by flia Hip.
  cbn in H1.
  rewrite <- Nat.mul_mod_idemp_r in H1; [ | easy ].
  rewrite Hj, Nat.mul_1_r in H1.
  rewrite Nat.mod_small in H1; [ flia Hip H1 | flia Hip ].
} {
  apply Nat.nlt_ge; intros Hi.
  remember (i ^ (p - 2) mod p) as j eqn:Hj; symmetry in Hj.
  replace j with (p - 1) in Hj. 2: {
    specialize (Nat.mod_upper_bound (i ^ (p - 2)) p Hpz) as H1.
    rewrite Hj in H1; flia Hi H1.
  }
  clear j Hi.
  specialize (fermat_little p Hp i) as H1.
  assert (H : 1 ≤ i < p) by flia Hip.
  specialize (H1 H); clear H.
  replace (p - 1) with (S (p - 2)) in H1 by flia Hip.
  cbn in H1.
  rewrite <- Nat.mul_mod_idemp_r in H1; [ | easy ].
  rewrite Hj in H1.
  replace 1 with (1 mod p) in H1 at 2; [ | rewrite Nat.mod_small; flia Hip ].
  apply Nat_eq_mod_sub_0 in H1.
  apply Nat.mod_divide in H1; [ | easy ].
  destruct H1 as (c, Hc).
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in Hc.
  rewrite <- Nat.sub_add_distr in Hc.
  assert (H : Nat.divide p (i + 1)). {
    exists (i - c).
    rewrite Nat.mul_sub_distr_r, <- Hc.
    rewrite Nat_sub_sub_distr. 2: {
      split; [ | easy ].
      destruct p; [ easy | ].
      rewrite Nat.mul_succ_r.
      destruct i; [ easy | ].
      destruct p; [ easy | flia ].
    }
    now rewrite Nat.sub_diag, Nat.add_0_l.
  }
  clear Hc; rename H into Hc.
  apply Nat.divide_pos_le in Hc; [ | flia ].
  flia Hip Hc.
}
Qed.

Theorem inv_mod_neq : ∀ p, prime p → ∀ i, 2 ≤ i ≤ p - 2 → inv_mod i p ≠ i.
Proof.
intros * Hp * Hip Hcon.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
unfold inv_mod in Hcon.
rewrite Nat_pow_mod_is_pow_mod in Hcon; [ | now intros H; subst p ].
specialize (fermat_little_1 p Hp i) as H1.
rewrite (Nat.mod_small i) in H1; [ | flia Hip ].
rewrite <- Hcon in H1 at 2.
apply Nat_eq_mod_sub_0 in H1.
replace p with (p - 2 + 2) in H1 at 1 by flia Hip.
rewrite <- (Nat.mul_1_r (_ ^ (p - 2))) in H1.
rewrite Nat.pow_add_r in H1.
rewrite <- Nat.mul_sub_distr_l in H1.
rewrite <- Nat.mul_mod_idemp_l in H1; [ | easy ].
rewrite Hcon in H1.
apply Nat.mod_divide in H1; [ | easy ].
specialize (Nat.gauss _ _ _ H1) as H2.
assert (H : Nat.gcd p i = 1). {
  apply eq_gcd_prime_small_1; [ easy | flia Hip ].
}
specialize (H2 H); clear H.
rewrite Nat_sqr_sub_1 in H2.
specialize (Nat.gauss _ _ _ H2) as H3.
assert (H : Nat.gcd p (i + 1) = 1). {
  apply eq_gcd_prime_small_1; [ easy | flia Hip ].
}
specialize (H3 H); clear H.
apply Nat.divide_pos_le in H3; [ flia Hip H3 | flia Hip ].
Qed.

Theorem mul_inv_diag_l_mod : ∀ p,
  prime p → ∀i, 1 ≤ i ≤ p - 1 → (inv_mod i p * i) mod p = 1.
Proof.
intros * Hp * Hip.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
unfold inv_mod.
rewrite Nat_pow_mod_is_pow_mod; [ | easy ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
replace i with (i ^ 1) at 2 by now rewrite Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
replace (p - 2 + 1) with (p - 1) by flia Hip.
apply fermat_little; [ easy | flia Hip ].
Qed.

Theorem mul_inv_diag_r_mod : ∀ p,
  prime p → ∀ i, 1 ≤ i ≤ p - 1 → (i * inv_mod i p) mod p = 1.
Proof. now intros; rewrite Nat.mul_comm; apply mul_inv_diag_l_mod. Qed.

Lemma eq_fold_left_mul_seq_2_prime_sub_3_1 : ∀ p,
  prime p
  → 3 ≤ p
  → fold_left Nat.mul (seq 2 (p - 3)) 1 mod p = 1.
Proof.
intros * Hp H3p.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
specialize (seq_NoDup (p - 3) 2) as Hnd.
remember (seq 2 (p - 3)) as l eqn:Hl.
assert
  (Hij : ∀ i, i ∈ l →
   ∃j, j ∈ l ∧ i ≠ j ∧ (i * j) mod p = 1 ∧
        ∀ k, k ∈ l → k ≠ i → (k * j) mod p ≠ 1). {
  intros i Hi.
  exists (inv_mod i p).
  subst l.
  apply in_seq in Hi.
  assert (H1 : inv_mod i p ∈ seq 2 (p - 3)). {
    apply in_seq.
    specialize (inv_mod_interv p Hp i) as H1.
    assert (H : 2 ≤ i ≤ p - 2) by flia Hi.
    specialize (H1 H); flia H1.
  }
  split; [ easy | ].
  assert (H2 : i ≠ inv_mod i p). {
    apply not_eq_sym.
    apply inv_mod_neq; [ easy | flia Hi ].
  }
  split; [ easy | ].
  assert (H3 : (i * inv_mod i p) mod p = 1). {
    apply mul_inv_diag_r_mod; [ easy | flia Hi ].
  }
  split; [ easy | ].
  intros k Hkl Hki Hk.
  apply Hki; clear Hki.
  rewrite <- H3 in Hk.
  destruct (Nat.eq_dec i k) as [Hink| Hink]; [ easy | ].
  destruct (le_dec i k) as [Hik| Hik]. {
    apply Nat_mul_mod_cancel_r in Hk. 2: {
      rewrite Nat.gcd_comm.
      apply in_seq in H1.
      apply eq_gcd_prime_small_1; [ easy | flia H1 ].
    }
    apply in_seq in Hkl.
    rewrite Nat.mod_small in Hk; [ | flia Hkl ].
    rewrite Nat.mod_small in Hk; [ easy | ].
    apply (le_lt_trans _ k); [ easy | flia Hkl ].
  }
  apply Nat.nle_gt in Hik.
  symmetry in Hk.
  apply Nat_eq_mod_sub_0 in Hk.
  rewrite <- Nat.mul_sub_distr_r in Hk.
  apply Nat.mod_divide in Hk; [ | easy ].
  specialize (Nat.gauss _ _ _ Hk) as H4.
  assert (H : Nat.gcd p (i - k) = 1). {
    apply eq_gcd_prime_small_1; [ easy | ].
    apply in_seq in Hkl.
    flia Hi Hkl Hink Hik.
  }
  specialize (H4 H); clear H.
  apply Nat.mod_divide in H4; [ | easy ].
  rewrite Nat.mod_small in H4. 2: {
    unfold inv_mod.
    rewrite Nat_pow_mod_is_pow_mod; [ | easy ].
    now apply Nat.mod_upper_bound.
  }
  rewrite H4 in H1.
  apply in_seq in H1; flia H1.
}
clear Hl.
remember (length l) as len eqn:Hlen; symmetry in Hlen.
revert l Hnd Hij Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len. {
  apply length_zero_iff_nil in Hlen.
  subst l; cbn; rewrite Nat.mod_1_l; flia H3p.
}
destruct l as [| a l]; [ easy | ].
specialize (Hij a (or_introl (eq_refl _))) as H1.
destruct H1 as (i2 & Hi2l & Hai2 & Hai2p & Hk).
destruct Hi2l as [Hi2l| Hi2l]; [ easy | ].
specialize (in_split i2 l Hi2l) as (l1 & l2 & Hll).
rewrite Hll.
cbn; rewrite Nat.add_0_r.
rewrite fold_left_app; cbn.
rewrite fold_left_mul_from_1.
rewrite Nat.mul_shuffle0, Nat.mul_comm.
rewrite fold_left_mul_from_1.
do 2 rewrite Nat.mul_assoc.
remember (i2 * 2) as x.
rewrite <- Nat.mul_assoc; subst x.
rewrite <- Nat.mul_mod_idemp_l; [ | flia H3p ].
rewrite (Nat.mul_comm i2).
rewrite Hai2p, Nat.mul_1_l.
rewrite Nat.mul_comm.
rewrite List_fold_left_mul_assoc, Nat.mul_1_l.
rewrite <- fold_left_app.
apply (IHlen (len - 1)); [ flia | | | ]. 3: {
  cbn in Hlen.
  apply Nat.succ_inj in Hlen.
  rewrite <- Hlen, Hll.
  do 2 rewrite app_length.
  cbn; flia.
} {
  apply NoDup_cons_iff in Hnd.
  destruct Hnd as (_, Hnd).
  rewrite Hll in Hnd.
  now apply NoDup_remove_1 in Hnd.
}
intros i Hi.
specialize (Hij i) as H1.
assert (H : i ∈ a :: l). {
  right; rewrite Hll.
  apply in_app_or in Hi.
  apply in_or_app.
  destruct Hi as [Hi| Hi]; [ now left | now right; right ].
}
specialize (H1 H); clear H.
destruct H1 as (j & Hjall & Hinj & Hijp & Hk').
exists j.
split. {
  destruct Hjall as [Hjall| Hjall]. {
    subst j; exfalso.
    specialize (Hk' i2) as H1.
    assert (H : i2 ∈ a :: l). {
      now rewrite Hll; right; apply in_or_app; right; left.
    }
    specialize (H1 H); clear H.
    assert (H : i2 ≠ i). {
      intros H; subst i2.
      move Hnd at bottom; move Hi at bottom.
      apply NoDup_cons_iff in Hnd.
      destruct Hnd as (_, Hnd).
      rewrite Hll in Hnd.
      now apply NoDup_remove_2 in Hnd.
    }
    specialize (H1 H).
    now rewrite Nat.mul_comm in H1.
  }
  rewrite Hll in Hjall.
  apply in_app_or in Hjall.
  apply in_or_app.
  destruct Hjall as [Hjall| Hjall]; [ now left | ].
  destruct Hjall as [Hjall| Hjall]; [ | now right ].
  subst j.
  destruct (Nat.eq_dec a i) as [Hai| Hai]. {
    subst i.
    move Hnd at bottom.
    apply NoDup_cons_iff in Hnd.
    destruct Hnd as (Hnd, _).
    exfalso; apply Hnd; clear Hnd.
    rewrite Hll.
    apply in_app_or in Hi.
    apply in_or_app.
    destruct Hi as [Hi| Hi]; [ now left | now right; right ].
  }
  now specialize (Hk' a (or_introl eq_refl) Hai) as H2.
}
split; [ easy | ].
split; [ easy | ].
intros k Hkll Hki.
apply Hk'; [ | easy ].
right.
rewrite Hll.
apply in_app_or in Hkll.
apply in_or_app.
destruct Hkll as [Hkll| Hkll]; [ now left | now right; right ].
Qed.

Theorem Wilson : ∀ n, 2 ≤ n → prime n ↔ fact (n - 1) mod n = n - 1.
Proof.
intros * H2n.
split.
-intros Hn.
 destruct (lt_dec n 3) as [H3n| H3n]. {
   now replace n with 2 by flia H2n H3n.
 }
 apply Nat.nlt_ge in H3n.
 replace (n - 1) with (S (n - 2)) at 1 by flia H3n.
 rewrite Nat_fact_succ.
 replace (S (n - 2)) with (n - 1) by flia H3n.
 rewrite <- Nat.mul_mod_idemp_r; [ | flia H3n ].
 enough (H : fact (n - 2) mod n = 1). {
   rewrite H, Nat.mul_1_r.
   apply Nat.mod_small; flia H3n.
 }
 rewrite fact_eq_fold_left.
 enough (H : fold_left Nat.mul (seq 2 (n - 3)) 1 mod n = 1). {
   replace (seq 1 (n - 2)) with (1 :: seq 2 (n - 3)). 2: {
     clear - H3n.
     destruct n; [ flia H3n | ].
     destruct n; [ flia H3n | ].
     destruct n; [ flia H3n | ].
     now cbn; rewrite Nat.sub_0_r.
   }
   easy.
 }
 (* now we must prove that the multiplication can be done by
    associating pairs of (a, b) in interval [2, n-2] such that
    a * b ≡ 1 (mod n). We not by Fermat's little theorem that
    a * a^(n-2) indeed equals 1 mod n. So b=a^(n-2) mod n. All
    these pairs are supposed to cover [2, n-2] *)
 now apply eq_fold_left_mul_seq_2_prime_sub_3_1.
-intros Hf.
 destruct (lt_dec 5 n) as [H5n| H5n]. {
   unfold prime.
   apply Bool.not_false_iff_true; intros H1.
   assert (H : ¬ prime n) by now unfold prime; rewrite H1.
   apply Wilson_on_composite in H; [ | easy ].
   rewrite H in Hf.
   flia Hf H5n.
 }
 apply Nat.nlt_ge in H5n.
 destruct n; [ easy | ].
 destruct n; [ flia H2n | ].
 destruct n; [ easy | ].
 destruct n; [ easy | ].
 destruct n; [ easy | ].
 destruct n; [ easy | flia H5n ].
Qed.

(* *)

Theorem inv_mod_prime_involutive : ∀ p,
  prime p
  → ∀ i, 2 ≤ i ≤ p - 2
  → inv_mod (inv_mod i p) p = i.
Proof.
intros * Hp * Hip.
assert (Hpz : p ≠ 0) by now intros H; rewrite H in Hp.
unfold inv_mod.
rewrite Nat_pow_mod_is_pow_mod; [ | now intros H; subst p ].
rewrite Nat_pow_mod_is_pow_mod; [ | now intros H; subst p ].
rewrite Nat_mod_pow_mod.
rewrite <- Nat.pow_mul_r.
rewrite <- Nat.pow_2_r.
rewrite Nat_sqr_sub; [ | flia Hip ].
rewrite Nat.mul_shuffle0.
replace (2 ^ 2) with 4 by easy.
replace (2 * 2) with 4 by easy.
rewrite Nat.pow_2_r.
rewrite Nat.add_sub_swap. 2: {
  apply Nat.mul_le_mono_r.
  flia Hip.
}
rewrite <- Nat.mul_sub_distr_r.
rewrite Nat.pow_add_r.
rewrite Nat.pow_mul_r.
rewrite <- Nat.mul_mod_idemp_l; [ | easy ].
rewrite <- Nat_mod_pow_mod.
rewrite fermat_little_1; [ | easy ].
rewrite Nat.mod_mod; [ | easy ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite <- Nat.pow_add_r.
rewrite Nat.sub_add; [ | flia Hip ].
rewrite fermat_little_1; [ | easy ].
apply Nat.mod_small; flia Hip.
Qed.

Theorem odd_prime : ∀ p, prime p → p ≠ 2 → p mod 2 = 1.
Proof.
intros * Hp Hp2.
remember (p mod 2) as r eqn:Hp2z; symmetry in Hp2z.
destruct r. 2: {
  destruct r; [ easy | ].
  specialize (Nat.mod_upper_bound p 2 (Nat.neq_succ_0 _)) as H1.
  flia Hp2z H1.
}
exfalso.
apply Nat.mod_divides in Hp2z; [ | easy ].
destruct Hp2z as (d, Hd).
destruct (lt_dec d 2) as [Hd2| Hd2]. {
  destruct d; [ now subst p; rewrite Nat.mul_0_r in Hp | ].
  destruct d; [ now subst p | flia Hd2 ].
}
apply Nat.nlt_ge in Hd2.
specialize (prime_prop p Hp d) as H1.
assert (H : 2 ≤ d ≤ p - 1). {
  split; [ easy | flia Hd ].
}
specialize (H1 H); clear H.
apply H1; clear H1.
rewrite Hd.
apply Nat.divide_factor_r.
Qed.

Theorem prime_not_mul : ∀ p q, prime (p * q) → p = 1 ∨ q = 1.
Proof.
intros * Hpq.
destruct (lt_dec p 2) as [H2p| H2p]. {
  destruct p; [ easy | ].
  destruct p; [ now left | flia H2p ].
}
destruct (lt_dec q 2) as [H2q| H2q]. {
  rewrite Nat.mul_comm in Hpq.
  destruct q; [ easy | ].
  destruct q; [ now right | flia H2q ].
}
apply Nat.nlt_ge in H2p.
apply Nat.nlt_ge in H2q.
exfalso.
apply prime_only_divisors with (a := p) in Hpq. {
  destruct Hpq as [Hpq| Hpq]; [ flia Hpq H2p | ].
  replace p with (p * 1) in Hpq at 1 by flia.
  apply Nat.mul_cancel_l in Hpq; [ | flia H2p ].
  flia Hpq H2q.
}
apply Nat.divide_factor_l.
Qed.

Definition divisors n := List.filter (λ a, n mod a =? 0) (List.seq 1 n).

Definition prime_divisors n :=
  filter (λ d, (is_prime d && (n mod d =? 0))%bool) (seq 1 n).
