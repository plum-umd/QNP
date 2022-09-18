(* We copied and modified this file from https://github.com/roglo/coq_euler_prod_form/blob/master/Totient.v *)

Require Import Utf8 Arith.
Require Import Sorting.Permutation.
Import List List.ListNotations.

Require Import Misc.

(* gcd_and_bezout a b returns (g, (u, v)) with the property
        a * u = b * v + g
        g = gcd a b;
   requires a ≠ 0 *)

Fixpoint gcd_bezout_loop n (a b : nat) : (nat * (nat * nat)) :=
  match n with
  | 0 => (0, (0, 0)) (* should not happen *)
  | S n' =>
      match b with
      | 0 => (a, (1, 0))
      | S _ =>
          let '(g, (u, v)) := gcd_bezout_loop n' b (a mod b) in
          let w := (u * b + v * (a - a mod b)) / b in
          let k := max (v / b) (w / a) + 1 in
          (g, (k * b - v, k * a - w))
      end
  end.

Definition gcd_and_bezout a b := gcd_bezout_loop (a + b + 1) a b.

Lemma gcd_bezout_loop_enough_iter_lt : ∀ m n a b,
  a + b ≤ m
  → a + b ≤ n
  → b < a
  → gcd_bezout_loop m a b = gcd_bezout_loop n a b.
Proof.
intros * Habm Habn Hba.
revert n a b Habm Habn Hba.
induction m; intros; [ flia Habm Hba | ].
destruct n; [ flia Habn Hba | cbn ].
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
replace b with (S (b - 1)) at 1 2 by flia Hbz.
remember (gcd_bezout_loop m b (a mod b)) as gbm eqn:Hgbm; symmetry in Hgbm.
remember (gcd_bezout_loop n b (a mod b)) as gbn eqn:Hgbn; symmetry in Hgbn.
specialize (IHm n b (a mod b)) as H1.
assert (H : ∀ p, a + b ≤ S p → b + a mod b ≤ p). {
  intros * Habp.
  transitivity (b + (a - 1)). {
    apply Nat.add_le_mono_l.
    specialize (Nat.div_mod a b Hbz) as H2.
    apply (Nat.add_le_mono_l _ _ (b * (a / b))).
    rewrite <- H2, Nat.add_comm.
    remember (a / b) as q eqn:Hq; symmetry in Hq.
    destruct q. {
      apply Nat.div_small_iff in Hq; [ flia Hba Hq | easy ].
    }
    destruct b; [ easy | ].
    cbn; remember (b * S q); flia.
  }
  flia Habp Hba.
}
specialize (H1 (H m Habm) (H n Habn)); clear H.
assert (H : a mod b < b) by now apply Nat.mod_upper_bound.
specialize (H1 H); clear H.
now rewrite <- Hgbm, H1, Hgbn.
Qed.

Lemma gcd_bezout_loop_enough_iter_ge : ∀ m n a b,
  a + b + 1 ≤ m
  → a + b + 1 ≤ n
  → a ≤ b
  → gcd_bezout_loop m a b = gcd_bezout_loop n a b.
Proof.
intros * Habm Habn Hab.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]; [ flia Hmz Habm | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ flia Hnz Habn | ].
replace m with (S (m - 1)) by flia Hmz.
replace n with (S (n - 1)) by flia Hnz.
cbn.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
replace b with (S (b - 1)) at 1 2 by flia Hbz.
rewrite (gcd_bezout_loop_enough_iter_lt _ (n - 1)); [ easy | | | ]. {
  destruct (Nat.eq_dec a b) as [Habe| Habe]. {
    subst a.
    rewrite Nat.mod_same; [ | easy ].
    flia Habm.
  }
  rewrite Nat.mod_small; [ | flia Hab Habe ].
  flia Habm.
} {
  destruct (Nat.eq_dec a b) as [Habe| Habe]. {
    subst a.
    rewrite Nat.mod_same; [ | easy ].
    flia Habn.
  }
  rewrite Nat.mod_small; [ | flia Hab Habe ].
  flia Habn.
} {
  now apply Nat.mod_upper_bound.
}
Qed.

Lemma fst_gcd_bezout_loop_is_gcd_lt : ∀ n a b,
  a ≠ 0
  → a + b + 1 ≤ n
  → b < a
  → fst (gcd_bezout_loop n a b) = Nat.gcd a b.
Proof.
intros * Haz Hn Hba.
revert a b Haz Hn Hba.
induction n; intros; [ flia Hn | cbn ].
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst b.
  now rewrite Nat.gcd_0_r.
}
replace b with (S (b - 1)) at 1 by flia Hbz.
remember (gcd_bezout_loop n b (a mod b)) as gb eqn:Hgb; symmetry in Hgb.
destruct gb as (g, (u, v)).
rewrite Nat.gcd_comm, <- Nat.gcd_mod; [ | easy ].
rewrite Nat.gcd_comm.
cbn.
replace g with (fst (gcd_bezout_loop n b (a mod b))) by now rewrite Hgb.
apply IHn; [ easy | | ]. {
  transitivity (a + b); [ | flia Hn ].
  rewrite <- Nat.add_assoc, Nat.add_comm.
  apply Nat.add_le_mono_r.
  apply (Nat.add_le_mono_l _ _ (b * (a / b))).
  rewrite Nat.add_assoc.
  rewrite <- Nat.div_mod; [ | easy ].
  rewrite Nat.add_comm.
  apply Nat.add_le_mono_r.
  remember (a / b) as q eqn:Hq; symmetry in Hq.
  destruct q. {
    apply Nat.div_small_iff in Hq; [ flia Hba Hq | easy ].
  }
  destruct b; [ easy | ].
  cbn; remember (b * S q); flia.
} {
  now apply Nat.mod_upper_bound.
}
Qed.

Lemma fst_gcd_bezout_loop_is_gcd_ge : ∀ n a b,
  a ≠ 0
  → a + b + 1 ≤ n
  → a ≤ b
  → fst (gcd_bezout_loop n a b) = Nat.gcd a b.
Proof.
intros * Haz Hn Hba.
rewrite (gcd_bezout_loop_enough_iter_ge _ (S n)); [ | easy | flia Hn | easy ].
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ subst b; flia Haz Hba | ].
cbn.
replace b with (S (b - 1)) at 1 by flia Hbz.
remember (gcd_bezout_loop n b (a mod b)) as gb eqn:Hgb; symmetry in Hgb.
destruct gb as (g, (u, v)); cbn.
replace g with (fst (gcd_bezout_loop n b (a mod b))) by now rewrite Hgb.
rewrite Nat.gcd_comm.
rewrite <- Nat.gcd_mod; [ | easy ].
rewrite Nat.gcd_comm.
apply fst_gcd_bezout_loop_is_gcd_lt; [ easy | | ]. {
  destruct (Nat.eq_dec a b) as [Habe| Habe]. {
    subst a.
    rewrite Nat.mod_same; [ | easy ].
    flia Hn.
  }
  rewrite Nat.mod_small; [ | flia Hba Habe ].
  flia Hn.
} {
  now apply Nat.mod_upper_bound.
}
Qed.

Lemma fst_gcd_bezout_loop_is_gcd : ∀ n a b,
  a ≠ 0
  → a + b + 1 ≤ n
  → fst (gcd_bezout_loop n a b) = Nat.gcd a b.
Proof.
intros * Haz Hn.
destruct (le_dec a b) as [Hab| Hab]. {
  now apply fst_gcd_bezout_loop_is_gcd_ge.
} {
  apply Nat.nle_gt in Hab.
  now apply fst_gcd_bezout_loop_is_gcd_lt.
}
Qed.

Theorem fst_gcd_and_bezout_is_gcd : ∀ a b,
  a ≠ 0
  → fst (gcd_and_bezout a b) = Nat.gcd a b.
Proof.
intros * Haz.
now apply fst_gcd_bezout_loop_is_gcd.
Qed.

Theorem gcd_bezout_loop_enough_iter : ∀ m n a b,
  a + b + 1 ≤ m
  → a + b + 1 ≤ n
  → gcd_bezout_loop m a b = gcd_bezout_loop n a b.
Proof.
intros * Habm Habn.
destruct (le_dec a b) as [Hab| Hab]. {
  now apply gcd_bezout_loop_enough_iter_ge.
} {
  apply Nat.nle_gt in Hab.
  apply gcd_bezout_loop_enough_iter_lt; [ flia Habm | flia Habn | easy ].
}
Qed.

Theorem gcd_bezout_loop_fst_0_gcd_0 : ∀ n a b g v,
  a ≠ 0
  → a + b + 1 ≤ n
  → b < a
  → gcd_bezout_loop n a b = (g, (0, v))
  → g = 0.
Proof.
intros * Haz Hn Hba Hnab.
assert (Hg : Nat.gcd a b = g). {
  replace g with (fst (gcd_bezout_loop n a b)) by now rewrite Hnab.
  now rewrite fst_gcd_bezout_loop_is_gcd.
}
revert a b g v Haz Hn Hba Hnab Hg.
induction n; intros; [ flia Hn | ].
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
cbn in Hnab.
replace b with (S (b - 1)) in Hnab at 1 by flia Hbz.
remember (gcd_bezout_loop n b (a mod b)) as gb eqn:Hgb; symmetry in Hgb.
destruct gb as (g', (u, v')).
injection Hnab; clear Hnab; intros H1 Hv H2; subst g' v.
rename v' into v.
apply Nat.sub_0_le in Hv.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l in Hv.
rewrite <- Nat.mul_max_distr_r in Hv.
rewrite <- Nat.add_max_distr_r in Hv.
apply Nat.max_lub_iff in Hv.
destruct Hv as (Hvb, Huv).
rewrite Nat.div_div in Huv; [ | easy | easy ].
apply Nat.nlt_ge in Hvb.
exfalso; apply Hvb; clear Hvb.
rewrite Nat.mul_comm.
specialize (Nat.div_mod v b Hbz) as H1.
rewrite Nat.add_comm.
apply (Nat.add_lt_mono_r _ _ (v mod b)).
rewrite <- Nat.add_assoc, <- H1.
rewrite Nat.add_comm.
apply Nat.add_lt_mono_r.
now apply Nat.mod_upper_bound.
Qed.

Theorem gcd_bezout_loop_prop_lt : ∀ n a b g u v,
  a ≠ 0
  → a + b + 1 ≤ n
  → b < a
  → gcd_bezout_loop n a b = (g, (u, v))
  → a * u = b * v + g.
Proof.
intros * Haz Hn Hba Hnab.
assert (Hgcd : g = Nat.gcd a b). {
  apply fst_gcd_bezout_loop_is_gcd in Hn; [ | easy ].
  now rewrite Hnab in Hn; cbn in Hn.
}
rewrite (gcd_bezout_loop_enough_iter _ (S n)) in Hnab; [ | easy | flia Hn ].
revert a b g u v Haz Hn Hba Hnab Hgcd.
induction n; intros; [ flia Hn | ].
remember (S n) as sn; cbn in Hnab; subst sn.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  subst b.
  rewrite Nat.mul_0_l.
  injection Hnab; clear Hnab; intros; subst g u v.
  now rewrite Nat.mul_1_r.
}
replace b with (S (b - 1)) in Hnab at 1 by flia Hbz.
remember (gcd_bezout_loop (S n) b (a mod b)) as gb eqn:Hgb; symmetry in Hgb.
destruct gb as (g', (u', v')).
injection Hnab; clear Hnab; intros; move Hgcd at bottom; subst g u v.
rename g' into g; rename u' into u; rename v' into v.
remember ((u * b + v * (a - a mod b)) / b) as w eqn:Hw; symmetry in Hw.
remember (max (v / b) (w / a) + 1) as k eqn:Hk.
do 2 rewrite Nat.mul_sub_distr_l.
replace (a * (k * b)) with (k * a * b) by flia.
replace (b * (k * a)) with (k * a * b) by flia.
rewrite <- Nat_sub_sub_distr. 2: {
  split. 2: {
    rewrite Nat.mul_comm.
    apply Nat.mul_le_mono_r.
    apply Nat_div_lt_le_mul; [ flia Hk | ].
    destruct (Nat.lt_trichotomy (v / b) (w / a)) as [H| H]. {
      rewrite max_r in Hk; [ | now apply Nat.lt_le_incl ].
      rewrite Hk.
      apply Nat.div_lt_upper_bound; [ now rewrite Nat.add_comm | ].
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
      specialize (Nat.div_mod w a Haz) as H1.
      apply (Nat.add_lt_mono_r _ _ (w mod a)).
      rewrite Nat.add_shuffle0.
      rewrite <- H1.
      apply Nat.add_lt_mono_l.
      now apply Nat.mod_upper_bound.
    } {
      assert (Huv : w / a ≤ v / b) by flia H; clear H.
      rewrite max_l in Hk; [ | easy ].
      rewrite Hk.
      apply (le_lt_trans _ (w / (w / a + 1))). {
        apply Nat.div_le_compat_l.
        split; [ flia | ].
        now apply Nat.add_le_mono_r.
      }
      apply Nat.div_lt_upper_bound; [ now rewrite Nat.add_comm | ].
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
      specialize (Nat.div_mod w a Haz) as H1.
      rewrite H1 at 1.
      apply Nat.add_lt_mono_l.
      now apply Nat.mod_upper_bound.
    }
  } {
    clear k Hk.
    rewrite Nat.add_comm, Nat.div_add in Hw; [ | easy ].
    rewrite Nat.add_comm in Hw.
    destruct u. {
      apply gcd_bezout_loop_fst_0_gcd_0 in Hgb; [ | easy | | ]; cycle 1. {
        destruct (lt_dec a b) as [Hab| Hab]. {
          rewrite Nat.mod_small in Hgb; [ | easy ].
          rewrite Nat.mod_small; [ | easy ].
          now rewrite (Nat.add_comm b).
        } {
          apply Nat.nlt_ge in Hab.
          transitivity (a + b + 1); [ | easy ].
          rewrite (Nat.add_comm b).
          do 2 apply Nat.add_le_mono_r.
          now apply Nat.mod_le.
        }
      } {
        now apply Nat.mod_upper_bound.
      }
      subst g; apply Nat.le_0_l.
    }
    rewrite <- Hw.
    rewrite Nat.mul_comm; cbn.
    transitivity b; [ | remember (_ * b); flia ].
    rewrite Hgcd.
    now apply Nat_gcd_le_r.
  }
}
f_equal.
apply IHn in Hgb; [ | easy | | | ]; cycle 1. {
  transitivity (a + b); [ | flia Hn ].
  rewrite <- Nat.add_assoc, Nat.add_comm.
  apply Nat.add_le_mono_r.
  apply (Nat.add_le_mono_l _ _ (b * (a / b))).
  rewrite Nat.add_assoc.
  rewrite <- Nat.div_mod; [ | easy ].
  rewrite Nat.add_comm.
  apply Nat.add_le_mono_r.
  remember (a / b) as q eqn:Hq; symmetry in Hq.
  destruct q. {
    apply Nat.div_small_iff in Hq; [ flia Hba Hq | easy ].
  }
  destruct b; [ easy | ].
  cbn; remember (b * S q); flia.
} {
  now apply Nat.mod_upper_bound.
} {
  rewrite Nat.gcd_comm, Nat.gcd_mod; [ | easy ].
  now rewrite Nat.gcd_comm.
}
rewrite <- Hw.
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  exists (u + v * (a - a mod b) / b).
  rewrite Nat.mul_add_distr_r; f_equal.
  rewrite Nat.divide_div_mul_exact; [ | easy | ]. 2: {
    exists (a / b).
    rewrite (Nat.div_mod a b Hbz) at 1.
    now rewrite Nat.add_sub, Nat.mul_comm.
  }
  rewrite <- Nat.mul_assoc; f_equal.
  rewrite Nat.mul_comm.
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
    exists (a / b).
    rewrite (Nat.div_mod a b Hbz) at 1.
    now rewrite Nat.add_sub, Nat.mul_comm.
  }
  rewrite Nat.mul_comm.
  now rewrite Nat.div_mul.
}
rewrite (Nat.mul_comm b).
rewrite Nat.div_mul; [ | easy ].
rewrite Nat.mul_sub_distr_l, (Nat.mul_comm v).
rewrite Nat.add_sub_assoc. 2: {
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_r.
  now apply Nat.mod_le.
}
symmetry; apply Nat.add_sub_eq_l.
symmetry; apply Nat.add_sub_eq_l.
rewrite Nat.add_assoc; f_equal.
now rewrite (Nat.mul_comm u), (Nat.mul_comm v).
Qed.

Theorem gcd_bezout_loop_prop_ge : ∀ n a b g u v,
  a ≠ 0
  → a + b + 1 ≤ n
  → a ≤ b
  → gcd_bezout_loop n a b = (g, (u, v))
  → a * u = b * v + g.
Proof.
intros * Haz Hn Hba Hbez.
assert (Hgcd : g = Nat.gcd a b). {
  specialize (fst_gcd_bezout_loop_is_gcd n a b Haz Hn) as H1.
  now rewrite Hbez in H1.
}
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ subst b; flia Haz Hba | ].
rewrite (gcd_bezout_loop_enough_iter _ (S n)) in Hbez; try flia Hn.
cbn - [ "/" "mod" ] in Hbez.
replace b with (S (b - 1)) in Hbez at 1 by flia Haz Hba.
remember (gcd_bezout_loop n b (a mod b)) as gb eqn:Hgb.
symmetry in Hgb.
destruct gb as (g', (u', v')).
apply gcd_bezout_loop_prop_lt in Hgb; [ | easy | | ]; cycle 1. {
  destruct (Nat.eq_dec a b) as [Hab| Hab]. {
    subst b.
    rewrite Nat.mod_same; [ flia Hn | easy ].
  }
  rewrite (Nat.add_comm b).
  rewrite Nat.mod_small; [ easy | flia Hba Hab ].
} {
  now apply Nat.mod_upper_bound.
}
injection Hbez; clear Hbez; intros; move Hgcd at bottom; subst g u v.
rename g' into g; rename u' into u; rename v' into v.
remember ((u * b + v * (a - a mod b)) / b) as w eqn:Hw; symmetry in Hw.
remember (max (v / b) (w / a) + 1) as k eqn:Hk.
do 2 rewrite Nat.mul_sub_distr_l.
replace (a * (k * b)) with (k * a * b) by flia.
replace (b * (k * a)) with (k * a * b) by flia.
rewrite <- Nat_sub_sub_distr. 2: {
  split. 2: {
    rewrite Nat.mul_comm.
    apply Nat.mul_le_mono_r.
    apply Nat_div_lt_le_mul; [ flia Hk | ].
    destruct (Nat.lt_trichotomy (v / b) (w / a)) as [H| H]. {
      rewrite max_r in Hk; [ | now apply Nat.lt_le_incl ].
      rewrite Hk.
      apply Nat.div_lt_upper_bound; [ now rewrite Nat.add_comm | ].
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
      specialize (Nat.div_mod w a Haz) as H1.
      apply (Nat.add_lt_mono_r _ _ (w mod a)).
      rewrite Nat.add_shuffle0.
      rewrite <- H1.
      apply Nat.add_lt_mono_l.
      now apply Nat.mod_upper_bound.
    } {
      assert (Huv : w / a ≤ v / b) by flia H; clear H.
      rewrite max_l in Hk; [ | easy ].
      rewrite Hk.
      apply (le_lt_trans _ (w / (w / a + 1))). {
        apply Nat.div_le_compat_l.
        split; [ flia | ].
        now apply Nat.add_le_mono_r.
      }
      apply Nat.div_lt_upper_bound; [ now rewrite Nat.add_comm | ].
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
      specialize (Nat.div_mod w a Haz) as H1.
      rewrite H1 at 1.
      apply Nat.add_lt_mono_l.
      now apply Nat.mod_upper_bound.
    }
  } {
    clear k Hk.
    rewrite Nat.add_comm, Nat.div_add in Hw; [ | easy ].
    rewrite Nat.add_comm in Hw.
    destruct u. {
      rewrite Nat.mul_0_r in Hgb.
      symmetry in Hgb.
      apply Nat.eq_add_0 in Hgb.
      rewrite (proj2 Hgb).
      apply Nat.le_0_l.
    }
    rewrite <- Hw.
    rewrite Nat.mul_comm; cbn.
    transitivity b; [ | remember (_ * b); flia ].
    rewrite Hgcd.
    now apply Nat_gcd_le_r.
  }
}
f_equal.
rewrite <- Hw.
rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
  exists (u + v * ((a - a mod b) / b)).
  rewrite Nat.mul_add_distr_r; f_equal.
  rewrite <- Nat.mul_assoc; f_equal.
  rewrite Nat.mul_comm.
    rewrite <- Nat.divide_div_mul_exact; [ | easy | ]. 2: {
      exists (a / b).
      rewrite (Nat.div_mod a b) at 1; [ | easy ].
      now rewrite Nat.add_sub, Nat.mul_comm.
    }
    now rewrite Nat.mul_comm, Nat.div_mul.
  }
  rewrite (Nat.mul_comm b), Nat.div_mul; [ | easy ].
  rewrite (Nat.mul_comm u), Hgb.
  rewrite Nat.mul_sub_distr_l.
  rewrite Nat.add_shuffle0, Nat.add_sub.
  rewrite Nat.add_sub_assoc. 2: {
    apply Nat.mul_le_mono_l.
    destruct (Nat.eq_dec a b) as [Hab| Hab]. {
      subst a.
      rewrite Nat.mod_same; [ apply Nat.le_0_l | easy ].
    }
    now apply Nat.mod_le.
  }
  rewrite Nat.add_comm, (Nat.mul_comm (a mod b)).
  now rewrite Nat.add_sub, Nat.mul_comm.
Qed.

Theorem gcd_and_bezout_prop : ∀ a b g u v,
  a ≠ 0
  → gcd_and_bezout a b = (g, (u, v))
  → a * u = b * v + g ∧ g = Nat.gcd a b.
Proof.
intros * Haz Hbez.
assert (Hgcd : g = Nat.gcd a b). {
  specialize (fst_gcd_and_bezout_is_gcd a b Haz) as H1.
  now rewrite Hbez in H1.
}
split; [ | easy ].
destruct (lt_dec b a) as [Hba| Hba]. {
  now apply (gcd_bezout_loop_prop_lt (a + b + 1)).
} {
  apply Nat.nlt_ge in Hba.
  now apply (gcd_bezout_loop_prop_ge (a + b + 1)).
}
Qed.

(* Nat.gcd_bezout_pos could be implemented like this *)
Theorem Nat_gcd_bezout_pos n m : 0 < n → Nat.Bezout n m (Nat.gcd n m).
Proof.
intros * Hn.
apply Nat.neq_0_lt_0 in Hn.
remember (gcd_and_bezout n m) as gb eqn:Hgb; symmetry in Hgb.
destruct gb as (g, (u, v)).
apply gcd_and_bezout_prop in Hgb; [ | easy ].
destruct Hgb as (Hnm, Hg); rewrite <- Hg.
exists u, v.
rewrite Nat.mul_comm, Nat.add_comm.
now rewrite (Nat.mul_comm v).
Qed.

(* Euler's totient function *)

Definition coprimes' n := filter (λ d, Nat.gcd n d =? 1) (seq 1 (n - 1)).
Definition φ' n := length (coprimes' n).

(* Totient function is multiplicative *)

Theorem bijection_same_length {A B} : ∀ f g (l : list A) (l' : list B),
  NoDup l
  → NoDup l'
  → (∀ a, a ∈ l → f a ∈ l')
  → (∀ b, b ∈ l' → g b ∈ l)
  → (∀ a, a ∈ l → g (f a) = a)
  → (∀ b, b ∈ l' → f (g b) = b)
  → length l = length l'.
Proof.
intros * Hnl Hnl' Hf Hg Hgf Hfg.
revert l' Hf Hg Hfg Hnl'.
induction l as [| x l]; intros. {
  destruct l' as [| y l']; [ easy | exfalso ].
  now specialize (Hg y (or_introl eq_refl)).
}
destruct l' as [| y l']. {
  exfalso.
  now specialize (Hf x (or_introl eq_refl)).
}
specialize (in_split (f x) (y :: l') (Hf x (or_introl eq_refl))) as H.
destruct H as (l1 & l2 & Hll).
rewrite Hll.
transitivity (length (f x :: l1 ++ l2)). 2: {
  cbn; do 2 rewrite app_length; cbn; flia.
}
cbn; f_equal.
apply IHl. {
    now apply NoDup_cons_iff in Hnl.
} {
  intros a Ha.
  now apply Hgf; right.
} {
  intros a Ha.
  specialize (Hf a (or_intror Ha)) as H1.
  rewrite Hll in H1.
  apply in_app_or in H1.
  apply in_or_app.
  destruct H1 as [H1| H1]; [ now left | ].
  destruct H1 as [H1| H1]; [ | now right ].
  apply (f_equal g) in H1.
  rewrite Hgf in H1; [ | now left ].
  rewrite Hgf in H1; [ | now right ].
  subst a.
  now apply NoDup_cons_iff in Hnl.
} {
  intros b Hb.
  rewrite Hll in Hg.
  specialize (Hg b) as H1.
  assert (H : b ∈ l1 ++ f x :: l2). {
    apply in_app_or in Hb.
    apply in_or_app.
    destruct Hb as [Hb| Hb]; [ now left | ].
    now right; right.
  }
  specialize (H1 H); clear H.
  destruct H1 as [H1| H1]; [ | easy ].
  subst x.
  rewrite Hfg in Hll. 2: {
    rewrite Hll.
    apply in_app_or in Hb.
    apply in_or_app.
    destruct Hb as [Hb| Hb]; [ now left | ].
    now right; right.
  }
  rewrite Hll in Hnl'.
  now apply NoDup_remove_2 in Hnl'.
} {
  intros b Hb.
  apply Hfg.
  rewrite Hll.
  apply in_app_or in Hb.
  apply in_or_app.
  destruct Hb as [Hb| Hb]; [ now left | ].
  now right; right.
} {
  rewrite Hll in Hnl'.
  now apply NoDup_remove_1 in Hnl'.
}
Qed.

Definition prod_copr_of_copr_mul m n a := (a mod m, a mod n).

Definition copr_mul_of_prod_copr (m n : nat) '((x, y) : nat * nat) :=
  let '(u, v) := snd (gcd_and_bezout m n) in
  m * n - (n * x * v + m * (n - 1) * y * u) mod (m * n).

Theorem in_coprimes'_iff : ∀ n a,
  a ∈ seq 1 (n - 1) ∧ Nat.gcd n a = 1 ↔ a ∈ coprimes' n.
Proof.
intros.
split; intros Ha. {
  apply filter_In.
  split; [ easy | ].
  now apply Nat.eqb_eq.
} {
  apply filter_In in Ha.
  split; [ easy | ].
  now apply Nat.eqb_eq.
}
Qed.

Theorem prod_copr_of_copr_mul_in_prod : ∀ m n a,
  2 ≤ m
  → 2 ≤ n
  → a ∈ coprimes' (m * n)
  → prod_copr_of_copr_mul m n a ∈
       list_prod (coprimes' m) (coprimes' n).
Proof.
intros * H2m H2n Ha.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]; [ now subst m | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  now subst n; rewrite Nat.mul_0_r in Ha.
}
apply in_coprimes'_iff in Ha.
destruct Ha as (Ha, Hga).
apply in_seq in Ha.
rewrite Nat.add_comm, Nat.sub_add in Ha by flia Ha.
unfold prod_copr_of_copr_mul.
apply in_prod. {
  apply in_coprimes'_iff.
  split. {
    apply in_seq.
    split. {
      remember (a mod m) as r eqn:Hr; symmetry in Hr.
      destruct r; [ | flia ].
      apply Nat.mod_divides in Hr; [ | easy ].
      destruct Hr as (k, Hk).
      rewrite Hk in Hga.
      rewrite Nat.gcd_mul_mono_l in Hga.
      apply Nat.eq_mul_1 in Hga.
      flia Hga H2m.
    } {
      rewrite Nat.add_comm, Nat.sub_add; [ | flia Hmz ].
      now apply Nat.mod_upper_bound.
    }
  } {
    rewrite Nat.gcd_comm, Nat.gcd_mod; [ | easy ].
    remember (Nat.gcd m a) as g eqn:Hg; symmetry in Hg.
    destruct g; [ now apply Nat.gcd_eq_0_l in Hg | ].
    destruct g; [ easy | exfalso ].
    replace (S (S g)) with (g + 2) in Hg by flia.
    specialize (Nat.gcd_divide_l m a) as H1.
    specialize (Nat.gcd_divide_r m a) as H2.
    rewrite Hg in H1, H2.
    destruct H1 as (k1, Hk1).
    destruct H2 as (k2, Hk2).
    rewrite Hk1, Hk2 in Hga.
    rewrite Nat.mul_shuffle0 in Hga.
    rewrite Nat.gcd_mul_mono_r in Hga.
    apply Nat.eq_mul_1 in Hga.
    flia Hga.
  }
} {
  apply in_coprimes'_iff.
  rewrite Nat.mul_comm in Hga.
  split. {
    apply in_seq.
    split. {
      remember (a mod n) as r eqn:Hr; symmetry in Hr.
      destruct r; [ | flia ].
      apply Nat.mod_divides in Hr; [ | easy ].
      destruct Hr as (k, Hk).
      rewrite Hk in Hga.
      rewrite Nat.gcd_mul_mono_l in Hga.
      apply Nat.eq_mul_1 in Hga.
      flia Hga H2n.
    } {
      rewrite Nat.add_comm, Nat.sub_add; [ | flia Hnz ].
      now apply Nat.mod_upper_bound.
    }
  } {
    rewrite Nat.gcd_comm, Nat.gcd_mod; [ | easy ].
    remember (Nat.gcd n a) as g eqn:Hg; symmetry in Hg.
    destruct g; [ now apply Nat.gcd_eq_0_l in Hg | ].
    destruct g; [ easy | exfalso ].
    replace (S (S g)) with (g + 2) in Hg by flia.
    specialize (Nat.gcd_divide_l n a) as H1.
    specialize (Nat.gcd_divide_r n a) as H2.
    rewrite Hg in H1, H2.
    destruct H1 as (k1, Hk1).
    destruct H2 as (k2, Hk2).
    rewrite Hk1, Hk2 in Hga.
    rewrite Nat.mul_shuffle0 in Hga.
    rewrite Nat.gcd_mul_mono_r in Hga.
    apply Nat.eq_mul_1 in Hga.
    flia Hga.
  }
}
Qed.

Theorem copr_mul_of_prod_copr_in_coprimes' : ∀ m n,
  2 ≤ m
  → Nat.gcd m n = 1
  → ∀ a, a ∈ list_prod (coprimes' m) (coprimes' n)
  → copr_mul_of_prod_copr m n a ∈ coprimes' (m * n).
Proof.
intros m n H2m Hmn (a, b) Hab.
destruct (Nat.eq_dec m 0) as [Hmz| Hmz]; [ now subst m | ].
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]. {
  subst n; cbn in Hab.
  now rewrite List_list_prod_nil_r in Hab.
}
apply in_prod_iff in Hab.
destruct Hab as (Ha, Hb).
apply in_coprimes'_iff in Ha.
apply in_coprimes'_iff in Hb.
destruct Ha as (Ha, Hma).
destruct Hb as (Hb, Hnb).
move Hb before Ha.
apply in_seq in Ha.
apply in_seq in Hb.
replace (1 + (m - 1)) with m in Ha by flia Hmz.
replace (1 + (n - 1)) with n in Hb by flia Hnz.
unfold copr_mul_of_prod_copr.
remember (gcd_and_bezout m n) as gb eqn:Hgb.
symmetry in Hgb.
destruct gb as (g & u & v); cbn.
specialize (gcd_and_bezout_prop m n g u v Hmz Hgb) as (Hmng & Hg).
rewrite Hmn in Hg; subst g.
apply in_coprimes'_iff.
assert (Hnmz : (n * a * v + m * (n - 1) * b * u) mod (m * n) ≠ 0). {
  rewrite Nat.mod_mul_r; [ | easy | easy ].
  do 2 rewrite <- (Nat.mul_assoc m).
  rewrite Nat_mod_add_r_mul_l; [ | easy ].
  remember ((n * a * v) mod m) as p eqn:Hp; symmetry in Hp.
  destruct p. {
    apply Nat.mod_divides in Hp; [ | easy ].
    destruct Hp as (k, Hk).
    rewrite Nat.mul_shuffle0 in Hk.
    replace (n * v) with (m * u - 1) in Hk by flia Hmng.
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l in Hk.
    apply Nat.add_sub_eq_nz in Hk. 2: {
      apply Nat.neq_mul_0.
      split; [ easy | ].
      intros H; subst k; rewrite Nat.mul_0_r in Hk.
      apply Nat.sub_0_le in Hk.
      apply Nat.nlt_ge in Hk; apply Hk; clear Hk.
      replace a with (1 * a) at 1 by flia.
      apply Nat.mul_lt_mono_pos_r; [ easy | ].
      destruct u. {
        rewrite Nat.mul_0_r in Hmng; flia Hmng.
      }
      rewrite Nat.mul_succ_r.
      destruct m; [ easy | ].
      destruct m; [ flia H2m | ].
      remember (S (S m) * u); flia.
    }
    rewrite Hmng in Hk.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l in Hk.
    rewrite Nat.add_comm in Hk.
    apply Nat.add_cancel_r in Hk.
    rewrite Nat.mul_shuffle0 in Hk; rewrite <- Hk.
    rewrite Nat.mul_shuffle0 in Hk.
    replace (n * v) with (m * u - 1) in Hk by flia Hmng.
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l in Hk.
    symmetry in Hk.
    destruct (le_dec k (u * a)) as [Hku| Hku]. {
      assert (H : a = m * u * a - m * k). {
        rewrite <- Hk.
        rewrite Nat_sub_sub_distr. 2: {
          split; [ | easy ].
          destruct m; [ easy | ].
          destruct u; [ rewrite Nat.mul_0_r in Hmng; flia Hmng | cbn ].
          remember ((u + m * S u) * a); flia.
        }
        now rewrite Nat.sub_diag.
      }
      rewrite <- Nat.mul_assoc in H.
      rewrite <- Nat.mul_sub_distr_l in H.
      destruct Ha as (Ha1, Ha).
      rewrite H in Ha.
      apply Nat.nle_gt in Ha; exfalso; apply Ha.
      destruct (Nat.eq_dec (u * a) k) as [Huk| Huk]. {
        subst k.
        rewrite Nat.sub_diag, Nat.mul_0_r in H; flia H Ha1.
      }
      remember (u * a - k) as p eqn:Hp.
      destruct p. {
        rewrite Nat.mul_0_r in H; flia H Ha1.
      }
      rewrite Nat.mul_succ_r; flia.
    }
    apply Nat.nle_gt in Hku.
    apply (Nat.mul_lt_mono_pos_r m) in Hku; [ | flia Hmz ].
    rewrite (Nat.mul_comm k) in Hku.
    rewrite <- Hk in Hku.
    rewrite Nat.mul_comm, Nat.mul_assoc in Hku.
    remember (m * u * a).
    flia Hku.
  }
  flia.
}
split. {
  apply in_seq.
  split. 2: {
    rewrite (Nat.add_comm _ (m * n - 1)).
    rewrite Nat.sub_add. 2: {
      destruct m; [ flia Hmz | ].
      destruct n; [ flia Hnz | ].
      cbn; remember (m * S n); flia.
    }
    apply Nat.sub_lt; [ | now apply Nat.neq_0_lt_0 ].
    apply Nat.lt_le_incl.
    apply Nat.mod_upper_bound.
    now apply Nat.neq_mul_0.
  }
  apply Nat.le_add_le_sub_r.
  apply Nat.mod_upper_bound.
  now apply Nat.neq_mul_0.
}
remember (n * a * v + m * (n - 1) * b * u) as p eqn:Hp.
rewrite Nat_gcd_sub_diag_l. 2: {
  apply Nat.lt_le_incl.
  apply Nat.mod_upper_bound.
  now apply Nat.neq_mul_0.
}
rewrite Nat.gcd_comm.
rewrite Nat.gcd_mod; [ | now apply Nat.neq_mul_0 ].
rewrite Nat.gcd_comm.
apply Nat_gcd_1_mul_r. {
  rewrite Hp.
  rewrite Nat.gcd_comm.
  do 2 rewrite <- (Nat.mul_assoc m).
  rewrite (Nat.mul_comm m).
  rewrite Nat.gcd_add_mult_diag_r.
  rewrite <- Nat.mul_assoc.
  apply Nat_gcd_1_mul_r; [ easy | ].
  apply Nat_gcd_1_mul_r; [ easy | ].
  apply Nat.bezout_1_gcd.
  exists u, n.
  flia Hmng.
} {
  rewrite Hp.
  rewrite <- (Nat.mul_assoc n).
  rewrite (Nat.mul_comm n).
  rewrite Nat.add_comm, Nat.gcd_comm.
  rewrite Nat.gcd_add_mult_diag_r.
  do 2 rewrite <- Nat.mul_assoc.
  rewrite Nat.mul_comm.
  apply Nat_gcd_1_mul_r; [ | now rewrite Nat.gcd_comm ].
  rewrite Nat.mul_assoc.
  apply Nat_gcd_1_mul_r. 2: {
    apply Nat.bezout_1_gcd.
    apply Nat_bezout_comm; [ easy | ].
    exists m, v.
    flia Hmng.
  }
  apply Nat_gcd_1_mul_r; [ | easy ].
  rewrite Nat_gcd_sub_diag_l; [ | flia Hnz ].
  apply Nat.gcd_1_r.
}
Qed.

Theorem Nat_mul_pred_r_mod : ∀ a b,
  a ≠ 0
  → 1 ≤ b < a
  → (b * (a - 1)) mod a = a - b.
Proof.
intros n a Hmn Ha.
remember (n - a) as b.
replace a with (n - b) in * by flia Heqb Ha.
clear a Heqb; rename b into a.
assert (H : 1 ≤ a < n) by flia Ha.
clear Ha; rename H into Ha.
(* or lemma here, perhaps? *)
rewrite Nat.mul_sub_distr_r.
do 2 rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
rewrite Nat_sub_sub_assoc. 2: {
  split. {
    destruct n; [ easy | ].
    rewrite Nat.mul_succ_r; flia.
  } {
    replace n with (1 * n) at 4 by flia.
    rewrite <- Nat.mul_sub_distr_r.
    transitivity ((n - 1) * n); [ | flia ].
    apply Nat.mul_le_mono_r; flia Ha.
  }
}
rewrite <- (Nat.mod_add _ a); [ | easy ].
rewrite Nat.sub_add. 2: {
  replace n with (1 * n) at 4 by flia.
  rewrite <- Nat.mul_sub_distr_r.
  transitivity ((n - 1) * n); [ | flia ].
  apply Nat.mul_le_mono_r; flia Ha.
}
rewrite <- Nat.add_sub_swap. 2: {
  replace n with (1 * n) at 1 by flia.
  apply Nat.mul_le_mono_r; flia Hmn.
}
rewrite <- (Nat.mod_add _ 1); [ | easy ].
rewrite Nat.mul_1_l.
rewrite Nat.sub_add. 2: {
  transitivity (n * n); [ | flia ].
  replace n with (1 * n) at 1 by flia.
  apply Nat.mul_le_mono_r; flia Hmn.
}
rewrite Nat.add_comm, Nat.mod_add; [ | easy ].
now rewrite Nat.mod_small.
Qed.

Theorem coprimes'_mul_prod_coprimes' : ∀ m n,
  m ≠ 0
  → n ≠ 0
  → Nat.gcd m n = 1
  → ∀ a, a ∈ seq 1 (m * n - 1)
  → copr_mul_of_prod_copr m n (prod_copr_of_copr_mul m n a) = a.
Proof.
intros * Hmz Hnz Hgmn * Ha.
unfold copr_mul_of_prod_copr.
unfold prod_copr_of_copr_mul.
remember (gcd_and_bezout m n) as gb eqn:Hgb.
symmetry in Hgb.
destruct gb as (g & u & v); cbn.
specialize (gcd_and_bezout_prop m n g u v Hmz Hgb) as (Hmng & Hg).
rewrite Hgmn in Hg; subst g.
specialize (Nat.div_mod a m Hmz) as Ham.
specialize (Nat.div_mod a n Hnz) as Han.
remember (a / m) as qm eqn:Hqm.
remember (a / n) as qn eqn:Hqn.
replace (a mod m) with (a - m * qm) by flia Ham.
replace (a mod n) with (a - n * qn) by flia Han.
rewrite Nat.mul_sub_distr_l, Nat.mul_assoc.
rewrite (Nat.mul_shuffle0 m).
rewrite (Nat.mul_sub_distr_l _ _ m), Nat.mul_assoc.
do 3 rewrite Nat.mul_sub_distr_r.
rewrite Nat.add_sub_assoc. 2: {
  do 2 apply Nat.mul_le_mono_r.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  subst qn.
  now apply Nat.mul_div_le.
}
assert (Hmn : m * n ≠ 0) by now apply Nat.neq_mul_0.
rewrite <- (Nat.mod_add _ (qn * (n - 1) * u)); [ | easy ].
replace (qn * (n - 1) * u * (m * n)) with (m * n * qn * (n - 1) * u) by flia.
rewrite Nat.sub_add. 2: {
  ring_simplify.
  transitivity (m * (n - 1) * u * a); [ | flia ].
  rewrite Nat.mul_shuffle0.
  rewrite (Nat.mul_shuffle0 m (n - 1)).
  rewrite (Nat.mul_shuffle0 (m * u)).
  apply Nat.mul_le_mono_r.
  rewrite (Nat.mul_shuffle0 _ u).
  apply Nat.mul_le_mono_r.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  subst qn.
  now apply Nat.mul_div_le.
}
rewrite <- Nat.add_sub_swap. 2: {
  apply Nat.mul_le_mono_r.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  subst qm.
  now apply Nat.mul_div_le.
}
rewrite <- (Nat.mod_add _ (qm * v)); [ | easy ].
replace (qm * v * (m * n)) with (n * m * qm * v) by flia.
rewrite Nat.sub_add. 2: {
  transitivity (n * a * v). 2: {
    remember (m * a * (n - 1) * u); flia.
  }
  apply Nat.mul_le_mono_r.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  subst qm.
  now apply Nat.mul_div_le.
}
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
rewrite Nat.mul_sub_distr_r.
rewrite Nat.add_sub_assoc. 2: {
  apply Nat.mul_le_mono_r.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  destruct n; [ easy | ].
  rewrite Nat.mul_succ_r; flia.
}
rewrite (Nat.mul_shuffle0 m a u).
rewrite Hmng.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
rewrite Nat.add_comm.
rewrite Nat.sub_add_distr.
rewrite (Nat.mul_shuffle0 n a v).
rewrite Nat.add_sub.
rewrite <- (Nat.mod_add _ a); [ | easy ].
rewrite <- Nat.add_sub_swap. 2: {
  destruct m; [ easy | ].
  destruct n; [ easy | ].
  destruct u; [ rewrite Nat.mul_comm in Hmng; cbn in Hmng; flia Hmng | ].
  rewrite (Nat.mul_shuffle0 (S m)).
  rewrite Nat.mul_shuffle0.
  cbn.
  remember ((u + (n + m * S n) * S u) * a).
  flia.
}
rewrite <- Nat.add_sub_assoc. 2: {
  destruct m; [ easy | ].
  destruct n; [ easy | ].
  rewrite Nat.mul_comm; cbn.
  remember (n + m * S n); flia.
}
replace a with (a * 1) at 3 by flia.
rewrite <- Nat.mul_sub_distr_l.
rewrite Nat.add_comm.
replace (m * a * n * u) with (a * u * (m * n)) by flia.
rewrite Nat.mod_add; [ | easy ].
apply in_seq in Ha.
replace (1 + (m * n - 1)) with (m * n) in Ha by flia Hmn.
rewrite Nat_mul_pred_r_mod; [ | easy | easy ].
rewrite Nat_sub_sub_distr. 2: {
  split; [ | easy ].
  now apply Nat.lt_le_incl.
}
now rewrite Nat.sub_diag.
Qed.

Theorem prod_coprimes'_coprimes'_mul_prod : ∀ m n,
  n ≠ 0
  → Nat.gcd m n = 1
  → ∀ x y, x < m → y < n
  → prod_copr_of_copr_mul m n
       (copr_mul_of_prod_copr m n (x, y)) = (x, y).
Proof.
intros * Hnz Hgmn * Hxm Hyn.
assert (Hmz : m ≠ 0) by flia Hxm.
move Hmz before n.
unfold copr_mul_of_prod_copr.
unfold prod_copr_of_copr_mul.
remember (gcd_and_bezout m n) as gb eqn:Hgb.
symmetry in Hgb.
destruct gb as (g & u & v); cbn.
specialize (gcd_and_bezout_prop m n g u v Hmz Hgb) as (Hmng & Hg).
rewrite Hgmn in Hg; subst g.
remember (n * x * v + m * (n - 1) * y * u) as p eqn:Hp.
f_equal. {
  rewrite Nat.mod_mul_r; [ | easy | easy ].
  rewrite Nat.sub_add_distr.
  rewrite <- (Nat.mod_add _ ((p / m) mod n)); [ | easy ].
  rewrite (Nat.mul_comm _ m).
  rewrite Nat.sub_add. 2: {
    apply Nat.le_add_le_sub_r.
    replace (m * n) with (m * (n - 1) + m). 2: {
      rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
      apply Nat.sub_add.
      destruct n; [ easy | ].
      rewrite Nat.mul_succ_r; flia.
    }
    apply Nat.add_le_mono. {
      apply Nat.mul_le_mono_l.
      rewrite Nat.sub_1_r.
      apply Nat.lt_le_pred.
      now apply Nat.mod_upper_bound.
    } {
      now apply Nat.lt_le_incl, Nat.mod_upper_bound.
    }
  }
  rewrite Hp.
  do 2 rewrite <- (Nat.mul_assoc m).
  rewrite Nat_mod_add_r_mul_l; [ | easy ].
  rewrite Nat.mul_shuffle0.
  replace (n * v) with (m * u - 1) by flia Hmng.
  rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
  rewrite <- (Nat.mod_add (m * u * x - x) x); [ | easy ].
  rewrite <- Nat.add_sub_swap. 2: {
    destruct m; [ easy | ].
    destruct u; [ now rewrite Nat.mul_0_r, Nat.add_1_r in Hmng | ].
    cbn.
    apply Nat.le_sub_le_add_l.
    rewrite Nat.sub_diag.
    apply Nat.le_0_l.
  }
  rewrite <- Nat.add_sub_assoc. 2: {
    destruct m; [ easy | ].
    rewrite Nat.mul_succ_r; flia.
  }
  replace x with (x * 1) at 3 by flia.
  rewrite <- Nat.mul_sub_distr_l.
  rewrite Nat.add_comm, <- Nat.mul_assoc.
  rewrite Nat_mod_add_r_mul_l; [ | easy ].
  rewrite <- (Nat.mod_add _ ((x * (m - 1)) mod m)); [ | easy ].
  rewrite <- Nat.add_sub_swap. 2: {
    transitivity (pred m). 2: {
      destruct n; [ easy | ].
      rewrite Nat.mul_succ_r; flia.
    }
    apply Nat.lt_le_pred.
    now apply Nat.mod_upper_bound.
  }
  remember ((x * (m - 1)) mod m) as a.
  rewrite <- Nat.add_sub_assoc. 2: {
    destruct m; [ easy | ].
    rewrite Nat.mul_succ_r; flia.
  }
  replace a with (a * 1) at 2 by flia.
  rewrite <- Nat.mul_sub_distr_l.
  rewrite Nat.add_comm.
  rewrite Nat_mod_add_r_mul_l; [ | easy ].
  subst a.
  rewrite Nat.mul_mod_idemp_l; [ | easy ].
  rewrite <- Nat.mul_assoc.
  rewrite <- Nat.pow_2_r.
  rewrite Nat_sqr_sub; [ | flia Hmz ].
  rewrite Nat.pow_1_l, Nat.mul_1_r, Nat.pow_2_r.
  rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
  rewrite <- (Nat.mod_add (m * m + 1 - 2 * m) 2); [ | easy ].
  rewrite Nat.sub_add. 2: {
    destruct m; [ easy | ].
    destruct m; [ easy | ].
    cbn; remember (m * (S (S m))); flia.
  }
  rewrite Nat.add_comm, Nat.mod_add; [ | easy ].
  rewrite Nat.mul_mod_idemp_r; [ | easy ].
  rewrite Nat.mul_1_r.
  now apply Nat.mod_small.
} {
  rewrite Nat.mul_comm at 2.
  rewrite Nat.mod_mul_r; [ | easy | easy ].
  rewrite Nat.sub_add_distr.
  rewrite <- (Nat.mod_add _ ((p / n) mod m)); [ | easy ].
  rewrite (Nat.mul_comm n).
  rewrite Nat.sub_add. 2: {
    apply Nat.le_add_le_sub_r.
    replace (m * n) with (n * (m - 1) + n). 2: {
      rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
      rewrite Nat.mul_comm.
      apply Nat.sub_add.
      destruct m; [ easy | ].
      rewrite Nat.mul_succ_l; flia.
    }
    apply Nat.add_le_mono. {
      rewrite Nat.mul_comm.
      apply Nat.mul_le_mono_l.
      rewrite Nat.sub_1_r.
      apply Nat.lt_le_pred.
      now apply Nat.mod_upper_bound.
    } {
      now apply Nat.lt_le_incl, Nat.mod_upper_bound.
    }
  }
  rewrite Hp.
  rewrite Nat.add_comm.
  rewrite <- (Nat.mul_assoc n).
  rewrite Nat_mod_add_r_mul_l; [ | easy ].
  rewrite Nat.mul_shuffle0.
  rewrite (Nat.mul_shuffle0 m).
  rewrite Hmng.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  rewrite Nat.mul_add_distr_r.
  do 2 rewrite <- Nat.mul_assoc.
  rewrite Nat.add_comm.
  rewrite Nat_mod_add_r_mul_l; [ | easy ].
  rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
  rewrite <- (Nat.mod_add (n * y - y) y); [ | easy ].
  rewrite <- Nat.add_sub_swap. 2: {
    destruct n; [ easy | cbn; flia ].
  }
  rewrite <- Nat.add_sub_assoc. 2: {
    rewrite Nat.mul_comm.
    destruct n; [ easy | cbn; flia ].
  }
  rewrite Nat.add_comm.
  rewrite Nat_mod_add_r_mul_l; [ | easy ].
  replace y with (y * 1) at 2 by flia.
  rewrite <- Nat.mul_sub_distr_l.
  rewrite <- (Nat.mod_add _ ((y * (n - 1)) mod n)); [ | easy ].
  rewrite <- Nat.add_sub_swap. 2: {
    transitivity (pred n). 2: {
      destruct m; [ easy | ].
      rewrite Nat.mul_succ_l; flia.
    }
    apply Nat.lt_le_pred.
    now apply Nat.mod_upper_bound.
  }
  remember ((y * (n - 1)) mod n) as a.
  rewrite <- Nat.add_sub_assoc. 2: {
    destruct n; [ easy | ].
    rewrite Nat.mul_succ_r; flia.
  }
  replace a with (a * 1) at 2 by flia.
  rewrite <- Nat.mul_sub_distr_l.
  rewrite Nat.add_comm.
  rewrite Nat.mod_add; [ | easy ].
  subst a.
  rewrite Nat.mul_mod_idemp_l; [ | easy ].
  rewrite <- Nat.mul_assoc.
  rewrite <- Nat.pow_2_r.
  rewrite Nat_sqr_sub; [ | flia Hnz ].
  rewrite Nat.pow_1_l, Nat.mul_1_r, Nat.pow_2_r.
  rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
  rewrite <- (Nat.mod_add (n * n + 1 - 2 * n) 2); [ | easy ].
  rewrite Nat.sub_add. 2: {
    destruct n; [ easy | ].
    destruct n; [ easy | ].
    cbn; remember (n * (S (S n))); flia.
  }
  rewrite Nat.add_comm, Nat.mod_add; [ | easy ].
  rewrite Nat.mul_mod_idemp_r; [ | easy ].
  rewrite Nat.mul_1_r.
  now apply Nat.mod_small.
}
Qed.

Theorem φ'_multiplicative : ∀ m n,
  2 ≤ m
  → 2 ≤ n
  → Nat.gcd m n = 1
  → φ' (m * n) = φ' m * φ' n.
Proof.
intros * H2m H2n Hg.
unfold φ'.
rewrite <- prod_length.
apply
  (bijection_same_length (prod_copr_of_copr_mul m n)
     (copr_mul_of_prod_copr m n)). {
  unfold coprimes'.
  apply NoDup_filter, seq_NoDup.
} {
  apply NoDup_prod; apply NoDup_filter, seq_NoDup.
} {
  intros a Ha.
  now apply prod_copr_of_copr_mul_in_prod.
} {
  intros b Hb.
  now apply copr_mul_of_prod_copr_in_coprimes'.
} {
  intros a Ha.
  apply coprimes'_mul_prod_coprimes'; [ flia H2m | flia H2n | easy | ].
  now apply filter_In in Ha.
} {
  intros (x, y) Hxy.
  apply in_prod_iff in Hxy.
  destruct Hxy as (Hx, Hy).
  apply prod_coprimes'_coprimes'_mul_prod; [ flia H2n | easy | | ]. {
    apply filter_In in Hx.
    destruct Hx as (Hx, _).
    apply in_seq in Hx.
    flia Hx.
  } {
    apply filter_In in Hy.
    destruct Hy as (Hy, _).
    apply in_seq in Hy.
    flia Hy.
  }
}
Qed.

(* Euler's theorem *)

Require Import Primes.

Theorem different_coprimes'_all_different_multiples : ∀ n a,
  a ∈ coprimes' n
  → ∀ i j,
  i ∈ coprimes' n
  → j ∈ coprimes' n
  → i ≠ j
  → (i * a) mod n ≠ (j * a) mod n.
Proof.
(* like smaller_than_prime_all_different_multiples but more general *)
intros * Ha * Hi Hj Hij.
intros Haa; symmetry in Haa.
apply in_coprimes'_iff in Ha.
apply in_coprimes'_iff in Hi.
apply in_coprimes'_iff in Hj.
destruct Ha as (Ha, Hna).
destruct Hi as (Hi, Hni).
destruct Hj as (Hj, Hnj).
assert
  (H : ∀ i j, i ∈ seq 1 (n - 1) → j ∈ seq 1 (n - 1) → i < j →
   (j * a) mod n ≠ (i * a) mod n). {
  clear i j Hi Hj Hni Hnj Hij Haa.
  intros * Hi Hj Hilj Haa.
  apply in_seq in Hi.
  apply in_seq in Hj.
  apply Nat_mul_mod_cancel_r in Haa; [ | now rewrite Nat.gcd_comm ].
  rewrite Nat.mod_small in Haa; [ | flia Hj ].
  rewrite Nat.mod_small in Haa; [ | flia Hi ].
  flia Hilj Haa.
}
destruct (lt_dec i j) as [Hilj| Hjli]. {
  now revert Haa; apply H.
} {
  symmetry in Haa.
  assert (Hilj : j < i) by flia Hij Hjli.
  now revert Haa; apply H.
}
Qed.

Theorem coprimes'_mul_in_coprimes' : ∀ n i j,
  i ∈ coprimes' n → j ∈ coprimes' n → (i * j) mod n ∈ coprimes' n.
Proof.
intros * Hi Hj.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
apply in_coprimes'_iff in Hi.
apply in_coprimes'_iff in Hj.
destruct Hi as (Hi, Hgi).
destruct Hj as (Hj, Hgj).
apply in_seq in Hi.
apply in_seq in Hj.
apply in_coprimes'_iff.
split. {
  apply in_seq.
  split. {
    remember ((i * j) mod n) as a eqn:Ha; symmetry in Ha.
    destruct a; [ | flia ].
    apply Nat.mod_divide in Ha; [ | easy ].
    apply Nat.gauss in Ha; [ | easy ].
    destruct Ha as (k, Hk).
    replace n with (1 * n) in Hgj by flia.
    subst j.
    rewrite Nat.gcd_mul_mono_r in Hgj.
    apply Nat.eq_mul_1 in Hgj.
    destruct Hgj as (H1k, Hn); subst n.
    flia Hi.
  } {
    rewrite Nat.add_comm, Nat.sub_add; [ | flia Hnz ].
    now apply Nat.mod_upper_bound.
  }
} {
  rewrite Nat.gcd_comm, Nat.gcd_mod; [ | easy ].
  now apply Nat_gcd_1_mul_r.
}
Qed.

Theorem NoDup_coprimes' : ∀ n, NoDup (coprimes' n).
Proof.
intros.
unfold coprimes'.
apply NoDup_filter, seq_NoDup.
Qed.

Theorem gcd_prod_coprimes' : ∀ n,
  Nat.gcd n (fold_left Nat.mul (coprimes' n) 1) = 1.
Proof.
intros.
assert (H : ∀ a, a ∈ coprimes' n → Nat.gcd n a = 1). {
  intros * H.
  now apply in_coprimes'_iff in H.
}
remember (coprimes' n) as l eqn:Hl; symmetry in Hl; clear Hl.
induction l as [| a l]; intros; [ apply Nat.gcd_1_r | ].
cbn; rewrite Nat.add_0_r.
rewrite fold_left_mul_from_1.
apply Nat_gcd_1_mul_r; [ now apply H; left | ].
apply IHl.
intros b Hb.
now apply H; right.
Qed.

Theorem euler_fermat_little : ∀ n a,
  n ≠ 0 → a ≠ 0 → Nat.gcd a n = 1 → a ^ φ' n ≡ 1 mod n.
Proof.
intros * Hnz Haz Hg.
(* https://wstein.org/edu/2007/spring/ent/ent-html/node19.html#sec:flittle *)
destruct (Nat.eq_dec n 1) as [Hn1| Hn1]; [ now subst n | ].
assert (Ha : a mod n ∈ coprimes' n). {
  apply in_coprimes'_iff.
  rewrite Nat.gcd_comm, Nat.gcd_mod; [ | easy ].
  rewrite Nat.gcd_comm.
  split; [ | easy ].
  apply in_seq.
  rewrite Nat.add_comm, Nat.sub_add; [ | flia Hnz ].
  split. {
    remember (a mod n) as b eqn:Hb; symmetry in Hb.
    destruct b; [ | flia ].
    apply Nat.mod_divides in Hb; [ | easy ].
    replace n with (n * 1) in Hg by flia.
    destruct Hb as (k, Hk); subst a.
    rewrite Nat.gcd_mul_mono_l in Hg.
    now apply Nat.eq_mul_1 in Hg.
  } {
    now apply Nat.mod_upper_bound.
  }
}
rewrite <- Nat_mod_pow_mod.
assert
  (H1 : ∀ i j, i ∈ coprimes' n → j ∈ coprimes' n
   → i ≠ j → (i * a) mod n ≠ (j * a) mod n). {
  intros * Hi Hj Hij.
  rewrite <- (Nat.mul_mod_idemp_r i); [ | easy ].
  rewrite <- (Nat.mul_mod_idemp_r j); [ | easy ].
  now apply different_coprimes'_all_different_multiples.
}
assert (Hcc : ∀ i, i ∈ coprimes' n → (i * a) mod n ∈ coprimes' n). {
  intros i Hi.
  rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
  now apply coprimes'_mul_in_coprimes'.
}
assert
  (Hperm :
     Permutation (map (λ i, (i * a) mod n) (coprimes' n)) (coprimes' n)). {
  apply NoDup_Permutation_bis; try apply NoDup_coprimes'; cycle 1. {
    now rewrite map_length.
  } {
    intros i Hi.
    apply in_map_iff in Hi.
    destruct Hi as (j & Hji & Hj).
    rewrite <- Hji.
    rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
    now apply coprimes'_mul_in_coprimes'.
  } {
    apply NoDup_map_iff with (d := 0).
    intros * Hi Hj Hnth.
    destruct (Nat.eq_dec i j) as [Heij| Heij]; [ easy | exfalso ].
    revert Hnth.
    apply H1; [ now apply nth_In | now apply nth_In | ].
    specialize (NoDup_coprimes' n) as H2.
    remember (coprimes' n) as l.
    clear - Hi Hj Heij H2.
    revert i j Hi Hj Heij.
    induction l as [| a l]; intros; [ easy | ].
    apply NoDup_cons_iff in H2.
    destruct H2 as (Ha, Hnd).
    intros H; cbn in H.
    destruct i. {
      destruct j; [ easy | ].
      subst a; apply Ha.
      cbn in Hj.
      apply Nat.succ_lt_mono in Hj.
      now apply nth_In.
    }
    destruct j. {
      subst a; apply Ha.
      cbn in Hi.
      apply Nat.succ_lt_mono in Hi.
      now apply nth_In.
    }
    cbn in Hi, Hj.
    apply Nat.succ_lt_mono in Hi.
    apply Nat.succ_lt_mono in Hj.
    apply -> Nat.succ_inj_wd_neg in Heij.
    revert H.
    now apply IHl.
  }
}
remember (λ i : nat, (i * a) mod n) as f eqn:Hf.
remember (fold_left Nat.mul (map f (coprimes' n)) 1) as x eqn:Hx.
remember (fold_left Nat.mul (coprimes' n) 1) as y eqn:Hy.
assert (Hx1 : x mod n = y mod n). {
  subst x y.
  erewrite Permutation_fold_mul; [ easy | apply Hperm ].
}
assert (Hx2 : x mod n = (y * a ^ φ' n) mod n). {
  subst x y; rewrite Hf.
  rewrite <- (map_map (λ i, i * a) (λ j, j mod n)).
  rewrite fold_left_mul_map_mod.
  now rewrite fold_left_mul_map_mul.
}
rewrite Hx2 in Hx1.
replace y with (y * 1) in Hx1 at 2 by flia.
apply Nat_mul_mod_cancel_l in Hx1. 2: {
  rewrite Hy, Nat.gcd_comm.
  apply gcd_prod_coprimes'.
}
now rewrite Nat_mod_pow_mod.
Qed.

Theorem prime_φ' : ∀ p, prime p → φ' p = p - 1.
Proof.
intros * Hp.
unfold φ'.
unfold coprimes'.
rewrite (filter_ext_in _ (λ d, true)). 2: {
  intros a Ha.
  apply Nat.eqb_eq.
  apply in_seq in Ha.
  rewrite Nat.add_comm, Nat.sub_add in Ha. 2: {
    destruct p; [ easy | flia ].
  }
  now apply eq_gcd_prime_small_1.
}
clear Hp.
destruct p; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
induction p; [ easy | ].
rewrite <- (Nat.add_1_r p).
rewrite seq_app.
rewrite filter_app.
now rewrite app_length, IHp.
Qed.

Corollary fermat_little_again : ∀ p,
  prime p → ∀ a, 1 ≤ a < p → a ^ (p - 1) mod p = 1.
Proof.
intros * Hp * Hap.
rewrite <- prime_φ'; [ | easy ].
replace 1 with (1 mod p). 2: {
  apply Nat.mod_1_l.
  now apply prime_ge_2.
}
apply euler_fermat_little; [ now intros H; subst p | flia Hap | ].
rewrite Nat.gcd_comm.
now apply eq_gcd_prime_small_1.
Qed.

(* proof of corollary above simpler than fermat_little, isn't it? *)
