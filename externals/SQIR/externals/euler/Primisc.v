(* We copied and modified this file from https://github.com/roglo/coq_euler_prod_form/blob/master/Primisc.v *)

(* experiments with primes... *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Misc Primes.
Require Import PTotient.

Theorem prime_pow_φ' : ∀ p, prime p →
  ∀ k, k ≠ 0 → φ' (p ^ k) = p ^ (k - 1) * φ' p.
Proof.
intros * Hp * Hk.
rewrite (prime_φ' p); [ | easy ].
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ now subst p | ].
unfold φ'.
unfold coprimes'.
rewrite (filter_ext_in _ (λ d, negb (d mod p =? 0))). 2: {
  intros a Ha.
  apply in_seq in Ha.
  rewrite Nat.add_comm, Nat.sub_add in Ha. 2: {
    apply Nat.neq_0_lt_0.
    now apply Nat.pow_nonzero.
  }
  remember (a mod p) as r eqn:Hr; symmetry in Hr.
  destruct r. {
    apply Nat.eqb_neq.
    apply Nat.mod_divides in Hr; [ | easy ].
    destruct Hr as (d, Hd).
    rewrite Hd.
    destruct k; [ easy | cbn ].
    rewrite Nat.gcd_mul_mono_l.
    intros H.
    apply Nat.eq_mul_1 in H.
    destruct H as (H, _).
    now subst p.
  } {
    apply Nat.eqb_eq.
    assert (Hg : Nat.gcd p a = 1). {
      rewrite <- Nat.gcd_mod; [ | easy ].
      rewrite Nat.gcd_comm.
      apply eq_gcd_prime_small_1; [ easy | ].
      split; [ rewrite Hr; flia | ].
      now apply Nat.mod_upper_bound.
    }
    clear - Hg.
    induction k; [ easy | ].
    now apply Nat_gcd_1_mul_l.
  }
}
clear Hp.
replace k with (k - 1 + 1) at 1 by flia Hk.
rewrite Nat.pow_add_r, Nat.pow_1_r.
remember (p ^ (k - 1)) as a eqn:Ha.
clear k Hk Ha Hpz.
induction a; [ easy | ].
cbn.
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]. {
  subst p; cbn.
  now rewrite Nat.mul_0_r.
}
destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
  subst a; cbn.
  do 2 rewrite Nat.add_0_r.
  rewrite (filter_ext_in _ (λ d, true)). 2: {
    intros a Ha.
    apply in_seq in Ha.
    rewrite Nat.mod_small; [ | flia Ha ].
    destruct a; [ flia Ha | easy ].
  }
  clear.
  destruct p; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  induction p; [ easy | ].
  rewrite <- (Nat.add_1_r p).
  rewrite seq_app, filter_app, app_length.
  now rewrite IHp.
}
rewrite <- Nat.add_sub_assoc. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.neq_mul_0.
}
rewrite Nat.add_comm.
rewrite seq_app, filter_app, app_length.
rewrite IHa, Nat.add_comm; f_equal.
rewrite Nat.add_comm, Nat.sub_add. 2: {
  apply Nat.neq_0_lt_0.
  now apply Nat.neq_mul_0.
}
replace p with (1 + (p - 1)) at 2 by flia Hpz.
rewrite seq_app, filter_app, app_length.
cbn.
rewrite Nat.mod_mul; [ | easy ]; cbn.
rewrite (filter_ext_in _ (λ d, true)). 2: {
  intros b Hb.
  remember (b mod p) as c eqn:Hc; symmetry in Hc.
  destruct c; [ | easy ].
  apply Nat.mod_divide in Hc; [ | easy ].
  destruct Hc as (c, Hc).
  subst b.
  apply in_seq in Hb.
  destruct Hb as (Hb1, Hb2).
  clear - Hb1 Hb2; exfalso.
  revert p a Hb1 Hb2.
  induction c; intros; [ flia Hb1 | ].
  cbn in Hb1, Hb2.
  destruct (Nat.eq_dec a 0) as [Haz| Haz]. {
    subst a.
    cbn in Hb1, Hb2.
    destruct p; [ flia Hb1 | ].
    rewrite Nat.sub_succ, Nat.sub_0_r in Hb2.
    flia Hb2.
  }
  destruct (Nat.eq_dec p 0) as [Hpz| Hpz]. {
    subst p; flia Hb1.
  }
  specialize (IHc p (a - 1)) as H1.
  assert (H : (a - 1) * p + 1 ≤ c * p). {
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    rewrite <- Nat.add_sub_swap. 2: {
      destruct a; [ easy | ].
      cbn; flia.
    }
    flia Hb1 Haz Hpz.
  }
  specialize (H1 H); clear H.
  apply H1.
  apply (Nat.add_lt_mono_l _ _ p).
  eapply lt_le_trans; [ apply Hb2 | ].
  ring_simplify.
  do 2 apply Nat.add_le_mono_r.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
  rewrite Nat.sub_add. 2: {
    destruct a; [ easy | rewrite Nat.mul_succ_r; flia ].
  }
  now rewrite Nat.mul_comm.
}
clear.
remember (a * p + 1) as b; clear a Heqb.
destruct p; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
revert b.
induction p; intros; [ easy | ].
rewrite <- Nat.add_1_r.
rewrite seq_app, filter_app, app_length.
now rewrite IHp.
Qed.

Theorem divide_add_div_le : ∀ m p q,
  2 ≤ p
  → 2 ≤ q
  → Nat.divide p m
  → Nat.divide q m
  → m / p + m / q ≤ m.
Proof.
intros * H2p H2q Hpm Hqm.
destruct Hpm as (kp, Hkp).
destruct Hqm as (kq, Hkq).
destruct (Nat.eq_dec p 0) as [Hpz| Hpz]; [ flia Hpz H2p | ].
destruct (Nat.eq_dec q 0) as [Hqz| Hqz]; [ flia Hqz H2q | ].
rewrite Hkq at 2.
rewrite Nat.div_mul; [ | easy ].
rewrite Hkp at 1.
rewrite Nat.div_mul; [ | easy ].
apply (Nat.mul_le_mono_pos_r _ _ (p * q)). {
  destruct p; [ easy | ].
  destruct q; [ easy | cbn; flia ].
}
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_assoc, <- Hkp.
rewrite Nat.mul_assoc, Nat.mul_shuffle0, <- Hkq.
rewrite <- Nat.mul_add_distr_l.
apply Nat.mul_le_mono_l.
rewrite Nat.add_comm.
apply Nat.add_le_mul. {
  destruct p; [ easy | ].
  destruct p; [ easy | flia ].
} {
  destruct q; [ easy | ].
  destruct q; [ easy | flia ].
}
Qed.

Theorem length_filter_mod_seq : ∀ a b,
  a mod b ≠ 0
  → length (filter (λ d, negb (d mod b =? 0)) (seq a b)) = b - 1.
Proof.
intros a b Hab1.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
specialize (Nat.div_mod a b Hbz) as H1.
remember (a / b) as q eqn:Hq.
remember (a mod b) as r eqn:Hr.
move q after r; move Hq after Hr.
replace b with (b - r + r) at 1. 2: {
  apply Nat.sub_add.
  now rewrite Hr; apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
rewrite seq_app, filter_app, app_length.
rewrite List_filter_all_true. 2: {
  intros c Hc.
  apply Bool.negb_true_iff, Nat.eqb_neq.
  apply in_seq in Hc.
  intros Hcon.
  specialize (Nat.div_mod c b Hbz) as H2.
  rewrite Hcon, Nat.add_0_r in H2.
  remember (c / b) as s eqn:Hs.
  subst a c.
  clear Hcon.
  destruct Hc as (Hc1, Hc2).
  rewrite Nat.add_sub_assoc in Hc2. 2: {
    rewrite Hr.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_swap in Hc2; [ | flia ].
  rewrite Nat.add_sub in Hc2.
  replace b with (b * 1) in Hc2 at 3 by flia.
  rewrite <- Nat.mul_add_distr_l in Hc2.
  apply Nat.mul_lt_mono_pos_l in Hc2; [ | flia Hbz ].
  rewrite Nat.add_1_r in Hc2.
  apply Nat.succ_le_mono in Hc2.
  apply Nat.nlt_ge in Hc1.
  apply Hc1; clear Hc1.
  apply (le_lt_trans _ (b * q)); [ | flia Hab1 ].
  now apply Nat.mul_le_mono_l.
}
rewrite seq_length.
replace r with (1 + (r - 1)) at 3 by flia Hab1.
rewrite seq_app, filter_app, app_length; cbn.
rewrite H1 at 1.
rewrite Nat.add_sub_assoc. 2: {
  rewrite Hr.
  now apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
rewrite Nat.add_sub_swap; [ | flia ].
rewrite Nat.add_sub.
rewrite Nat_mod_add_l_mul_l; [ | easy ].
rewrite Nat.mod_same; [ cbn | easy ].
rewrite List_filter_all_true. 2: {
  intros c Hc.
  apply Bool.negb_true_iff, Nat.eqb_neq.
  apply in_seq in Hc.
  intros Hcon.
  specialize (Nat.div_mod c b Hbz) as H2.
  rewrite Hcon, Nat.add_0_r in H2.
  remember (c / b) as s eqn:Hs.
  subst a c.
  clear Hcon.
  destruct Hc as (Hc1, Hc2).
  rewrite Nat.add_sub_assoc in Hc2. 2: {
    rewrite Hr.
    rewrite Nat_mod_add_l_mul_l; [ | easy ].
    rewrite Nat.mod_small; [ flia Hab1 | ].
    rewrite Hr.
    now apply Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_swap in Hc2; [ | flia ].
  rewrite Nat.add_sub in Hc2.
  rewrite Nat.add_sub_assoc in Hc2. 2: {
    rewrite Hr.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.sub_add in Hc2; [ | flia ].
  rewrite Nat.add_sub_assoc in Hc1. 2: {
    rewrite Hr.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Nat.add_sub_swap in Hc1; [ | flia ].
  rewrite Nat.add_sub in Hc1.
  rewrite Nat.add_shuffle0 in Hc2.
  apply Nat.nlt_ge in Hc1; apply Hc1; clear Hc1.
  rewrite Nat.add_1_r.
  apply -> Nat.succ_le_mono.
  replace b with (b * 1) at 3 by flia.
  rewrite <- Nat.mul_add_distr_l.
  apply Nat.mul_le_mono_l.
  replace b with (b * 1) in Hc2 at 3 by flia.
  rewrite <- Nat.mul_add_distr_l in Hc2.
  apply Nat.nlt_ge; intros Hc1.
  replace s with ((q + 1) + S (s - (q + 2))) in Hc2 by flia Hc1.
  rewrite Nat.mul_add_distr_l in Hc2.
  apply Nat.add_lt_mono_l in Hc2.
  apply Nat.nle_gt in Hc2; apply Hc2; clear Hc2.
  rewrite Nat.mul_comm; cbn.
  transitivity b; [ | flia Hc1 ].
  rewrite Hr.
  now apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
rewrite seq_length.
rewrite Nat.add_sub_assoc; [ | flia Hab1 ].
rewrite Nat.sub_add; [ easy | ].
rewrite Hr.
now apply Nat.lt_le_incl, Nat.mod_upper_bound.
Qed.

Theorem gcd_1_div_mul_exact : ∀ m p q kp kq,
  q ≠ 0
  → Nat.gcd p q = 1
  → m = kp * p
  → m = kq * q
  → kp = q * (kp / q).
Proof.
intros * Hqz Hg Hkp Hkq.
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  apply (Nat.gauss _ p). {
    rewrite Nat.mul_comm, <- Hkp, Hkq.
    now exists kq.
  } {
    now rewrite Nat.gcd_comm.
  }
}
now rewrite Nat.mul_comm, Nat.div_mul.
Qed.

Theorem Nat_gcd_1_mul_divide : ∀ m p q,
  Nat.gcd p q = 1
  → Nat.divide p m
  → Nat.divide q m
  → Nat.divide (p * q) m.
Proof.
intros * Hg Hpm Hqm.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]. {
  subst m; cbn.
  now exists 0.
}
assert (Hpz : p ≠ 0). {
  destruct Hpm as (k, Hk).
  now intros H; rewrite H, Nat.mul_0_r in Hk.
}
assert (Hqz : q ≠ 0). {
  destruct Hqm as (k, Hk).
  now intros H; rewrite H, Nat.mul_0_r in Hk.
}
destruct Hpm as (kp, Hkp).
destruct Hqm as (kq, Hkq).
exists (kp * kq / m).
rewrite Nat.mul_comm.
rewrite Hkp at 2.
rewrite Nat.div_mul_cancel_l; [ | easy | ]. 2: {
  intros H; subst kp.
  rewrite Hkp in Hkq; cbn in Hkq.
  symmetry in Hkq.
  apply Nat.eq_mul_0 in Hkq.
  destruct Hkq as [H| H]; [ | now subst q ].
  now subst kq.
}
rewrite (Nat.mul_comm p), <- Nat.mul_assoc.
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  exists (kq / p).
  rewrite Nat.mul_comm.
  rewrite Nat.gcd_comm in Hg.
  now apply (gcd_1_div_mul_exact m q p kq kp).
}
rewrite (Nat.mul_comm p).
rewrite Nat.div_mul; [ | easy ].
now rewrite Nat.mul_comm.
Qed.

Theorem prime_divisors_decomp : ∀ n a,
  a ∈ prime_divisors n ↔ a ∈ prime_decomp n.
Proof.
intros.
split; intros Ha. {
  apply filter_In in Ha.
  destruct Ha as (Ha, H).
  apply Bool.andb_true_iff in H.
  destruct H as (Hpa, Hna).
  apply Nat.eqb_eq in Hna.
  apply in_seq in Ha.
  apply Nat.mod_divide in Hna; [ | flia Ha ].
  apply prime_decomp_in_iff.
  split; [ | split ]; [ flia Ha | easy | easy ].
} {
  apply filter_In.
  apply prime_decomp_in_iff in Ha.
  destruct Ha as (Hnz & Ha & Han).
  split. {
    apply in_seq.
    split. {
      transitivity 2; [ flia | ].
      now apply prime_ge_2.
    } {
      destruct Han as (k, Hk); subst n.
      destruct k; [ easy | flia ].
    }
  }
  apply Bool.andb_true_iff.
  split; [ easy | ].
  apply Nat.eqb_eq.
  apply Nat.mod_divide in Han; [ easy | ].
  now intros H1; subst a.
}
Qed.

Theorem prime_divisors_nil_iff: ∀ n, prime_divisors n = [] ↔ n = 0 ∨ n = 1.
Proof.
intros.
split; intros Hn. {
  apply prime_decomp_nil_iff.
  remember (prime_decomp n) as l eqn:Hl; symmetry in Hl.
  destruct l as [| a l]; [ easy | ].
  specialize (proj2 (prime_divisors_decomp n a)) as H1.
  rewrite Hl, Hn in H1.
  now exfalso; apply H1; left.
} {
  now destruct Hn; subst n.
}
Qed.
