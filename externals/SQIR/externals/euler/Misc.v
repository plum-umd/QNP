(* We copied and modified this file from https://github.com/roglo/coq_euler_prod_form/blob/master/Misc.v *)

(* Theorems of general usage, which could be (or not) in Coq library *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz Sorted Permutation Decidable.
Import List List.ListNotations.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; intros; nia.

Notation "x '∈' l" := (List.In x l) (at level 70).
Notation "x '∉' l" := (¬ List.In x l) (at level 70).

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level) :
                          nat_scope.
Notation "x < y < z" := (x < y ∧ y < z)%nat (at level 70, y at next level).

Notation "∃! x .. y , p" :=
  (ex (unique (λ x, .. (ex (unique (λ y, p))) ..)))
    (at level 200, x binder, right associativity)
  : type_scope.

Definition List_combine_all {A} (l1 l2 : list A) (d : A) :=
  let '(l'1, l'2) :=
    match List.length l1 ?= List.length l2 with
    | Eq => (l1, l2)
    | Lt => (l1 ++ List.repeat d (List.length l2 - List.length l1), l2)
    | Gt => (l1, l2 ++ List.repeat d (List.length l1 - List.length l2))
    end
  in
  List.combine l'1 l'2.

Theorem filter_ext_in {A : Type} : forall (f g : A -> bool) (l : list A),
    (forall a, a ∈ l -> f a = g a) -> filter f l = filter g l.
Proof.
  intros f g l. induction l; intros. easy.
  assert (forall a : A, a ∈ l -> f a = g a).
  { intros x Hx. apply H. simpl. right. easy.
  }
  assert (f a = g a).
  { apply H. simpl. left. easy.
  }
  simpl. rewrite IHl by easy. destruct (f a); rewrite <- H1; easy.
Qed.

Lemma filter_app {A : Type} (f : A -> bool) (l l' : list A) :
  filter f (l ++ l') = filter f l ++ filter f l'.
Proof.
  induction l. simpl. easy.
  simpl. rewrite IHl. destruct (f a); easy.
Qed.  

Theorem List_cons_app A (a : A) l : a :: l = [a] ++ l.
Proof. easy. Qed.

Theorem List_skipn_1 : ∀ A (l : list A), skipn 1 l = tl l.
Proof. easy. Qed.

Theorem List_fold_left_map :
  ∀ A B C (f : A → B → A) (g : C → B) (l : list C) a,
  fold_left f (map g l) a = fold_left (λ c b, f c (g b)) l a.
Proof.
intros.
revert a.
induction l as [| c]; intros; [ easy | apply IHl ].
Qed.

(* summations *)

Notation "'Σ' ( i = b , e ) , g" :=
  (fold_left (λ c i, c + g) (seq b (S e - b)) 0)
  (at level 45, i at level 0, b at level 60, e at level 60) : nat_scope.

Theorem fold_left_add_fun_from_0 {A} : ∀ a l (f : A → nat),
  fold_left (λ c i, c + f i) l a =
  a + fold_left (λ c i, c + f i) l 0.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply Nat.add_0_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
apply Nat.add_assoc.
Qed.

Theorem fold_left_mul_fun_from_1 {A} : ∀ a l (f : A → nat),
  fold_left (λ c i, c * f i) l a =
  a * fold_left (λ c i, c * f i) l 1.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply Nat.mul_1_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite Nat.add_0_r.
apply Nat.mul_assoc.
Qed.

Theorem fold_left_mul_from_1 : ∀ a l,
  fold_left Nat.mul l a = a * fold_left Nat.mul l 1.
Proof.
intros.
revert a.
induction l as [| x l]; intros; [ symmetry; apply Nat.mul_1_r | cbn ].
rewrite IHl; symmetry; rewrite IHl.
rewrite Nat.add_0_r.
apply Nat.mul_assoc.
Qed.

Theorem fold_right_max_ge : ∀ m l, m ≤ fold_right max m l.
Proof.
intros.
induction l as [| a]; [ easy | cbn ].
etransitivity; [ apply IHl | ].
apply Nat.le_max_r.
Qed.

Theorem summation_split_first : ∀ b e f,
  b ≤ e
  → Σ (i = b, e), f i = f b + Σ (i = S b, e), f i.
Proof.
intros * Hbe.
rewrite Nat.sub_succ.
replace (S e - b) with (S (e - b)) by flia Hbe.
cbn.
apply fold_left_add_fun_from_0.
Qed.

Theorem summation_split_last : ∀ b e f,
  b ≤ e
  → 1 ≤ e
  → Σ (i = b, e), f i = Σ (i = b, e - 1), f i + f e.
Proof.
intros * Hbe He.
destruct e; [ flia He | clear He ].
rewrite Nat.sub_succ, Nat.sub_0_r.
replace (S (S e) - b) with (S (S e - b)) by flia Hbe.
remember (S e - b) as n eqn:Hn.
revert b Hbe Hn.
induction n; intros. {
  now replace (S e) with b by flia Hbe Hn.
}
remember (S n) as sn; cbn; subst sn.
rewrite fold_left_add_fun_from_0.
rewrite IHn; [ | flia Hn | flia Hn ].
rewrite Nat.add_assoc; f_equal; cbn.
now rewrite (fold_left_add_fun_from_0 (f b)).
Qed.

Theorem all_0_summation_0 : ∀ b e f,
  (∀ i, b ≤ i ≤ e → f i = 0)
  → Σ (i = b, e), f i = 0.
Proof.
intros * Hz.
remember (S e - b) as n eqn:Hn.
revert b Hz Hn.
induction n; intros; [ easy | cbn ].
rewrite fold_left_add_fun_from_0.
rewrite IHn; [ | | flia Hn ]. {
  rewrite Hz; [ easy | flia Hn ].
}
intros i Hi.
apply Hz; flia Hi.
Qed.

Ltac rewrite_in_summation th :=
  let b := fresh "b" in
  let e := fresh "e" in
  let a := fresh "a" in
  intros b e;
  remember (S e - b) as n eqn:Hn;
  remember 0 as a eqn:Ha; clear Ha;
  revert e a b Hn;
  induction n as [| n IHn]; intros; [ easy | cbn ];
  rewrite th;
  apply (IHn e); flia Hn.

Theorem summation_eq_compat : ∀ b e g h,
  (∀ i, b ≤ i ≤ e → g i = h i)
  → Σ (i = b, e), g i = Σ (i = b, e), h i.
Proof.
intros * Hgh.
remember (S e - b) as n eqn:Hn.
remember 0 as a eqn:Ha; clear Ha.
revert e a b Hn Hgh.
induction n as [| n IHn]; intros; [ easy | cbn ].
rewrite Hgh; [ | flia Hn ].
rewrite (IHn e); [ easy | flia Hn | ].
intros i Hbie.
apply Hgh; flia Hbie.
Qed.

Theorem summation_le_compat: ∀ b e g h,
  (∀ i, b ≤ i ≤ e → g i ≤ h i) → Σ (i = b, e), g i ≤ Σ (i = b, e), h i.
Proof.
intros * Hgh.
remember (S e - b) as n eqn:Hn.
remember 0 as a eqn:Ha; clear Ha.
revert a b Hn Hgh.
induction n as [| n IHn]; intros; [ easy | cbn ].
setoid_rewrite fold_left_add_fun_from_0.
do 2 rewrite <- Nat.add_assoc.
apply Nat.add_le_mono_l.
apply Nat.add_le_mono; [ apply Hgh; flia Hn | ].
apply IHn; [ flia Hn | ].
intros i Hbie.
apply Hgh; flia Hbie.
Qed.

Theorem mul_add_distr_r_in_summation : ∀ b e f g h,
  Σ (i = b, e), (f i + g i) * h i =
  Σ (i = b, e), (f i * h i + g i * h i).
Proof.
intros; revert b e.
rewrite_in_summation Nat.mul_add_distr_r.
Qed.

Theorem double_mul_assoc_in_summation : ∀ b e f g h k,
  Σ (i = b, e), f i * g i * h i * k i = Σ (i = b, e), f i * (g i * h i * k i).
Proof.
intros.
assert (H : ∀ a b c d, a * b * c * d = a * (b * c * d)) by flia.
revert b e.
rewrite_in_summation H.
Qed.

Theorem mul_assoc_in_summation : ∀ b e f g h,
  Σ (i = b, e), f i * g i * h i = Σ (i = b, e), f i * (g i * h i).
Proof.
intros.
assert (H : ∀ a b c, a * b * c = a * (b * c)) by flia.
revert b e.
rewrite_in_summation H.
Qed.

Theorem mul_comm_in_summation : ∀ b e f g,
  Σ (i = b, e), f i * g i = Σ (i = b, e), g i * f i.
Proof.
intros.
assert (H : ∀ a b, a * b = b * a) by flia.
revert b e.
rewrite_in_summation H.
Qed.

Theorem mul_summation_distr_l : ∀ a b e f,
  a * (Σ (i = b, e), f i) = Σ (i = b, e), a * f i.
Proof.
intros.
remember (S e - b) as n eqn:Hn.
revert e a b Hn.
induction n; intros; [ apply Nat.mul_0_r | cbn ].
rewrite fold_left_add_fun_from_0.
rewrite Nat.mul_add_distr_l.
rewrite (IHn e); [ | flia Hn ].
symmetry.
apply fold_left_add_fun_from_0.
Qed.

Theorem mul_summation_distr_r : ∀ a b e f,
  (Σ (i = b, e), f i) * a = Σ (i = b, e), f i * a.
Proof.
intros.
rewrite Nat.mul_comm.
rewrite mul_summation_distr_l.
now rewrite mul_comm_in_summation.
Qed.

Theorem power_shuffle1_in_summation : ∀ b e a f g,
  Σ (i = b, e), a * f i * a ^ (e - i) * g i =
  Σ (i = b, e), f i * a ^ (S e - i) * g i.
Proof.
intros.
(* failed to be able to use "rewrite_in_summation" here *)
assert
  (H : ∀ i e,
   a * f i * a ^ (e - i) * g i = f i * a ^ (S (e - i)) * g i). {
  clear e; intros; f_equal.
  rewrite <- Nat.mul_assoc, Nat.mul_comm, <- Nat.mul_assoc.
  f_equal.
  rewrite Nat.mul_comm.
  replace a with (a ^ 1) at 1 by apply Nat.pow_1_r.
  now rewrite <- Nat.pow_add_r.
}
remember (S e - b) as n eqn:Hn.
remember 0 as z eqn:Hz; clear Hz.
revert e z b Hn.
induction n as [| n IHn]; intros; [ easy | ].
cbn - [ "-" ].
rewrite IHn; [ | flia Hn ].
f_equal; f_equal; rewrite H.
f_equal; f_equal; f_equal; flia Hn.
Qed.

Theorem power_shuffle2_in_summation : ∀ b e a c f,
  Σ (i = b, e), c * f i * a ^ (e - i) * c ^ i =
  Σ (i = b, e), f i * a ^ (e - i) * c ^ S i.
Proof.
intros.
remember (S e - b) as n eqn:Hn.
remember 0 as z eqn:Hz; clear Hz.
revert e z b Hn.
induction n as [| n IHn]; intros; [ easy | ].
cbn.
rewrite IHn; [ | flia Hn ].
f_equal; f_equal.
do 2 rewrite <- Nat.mul_assoc.
rewrite Nat.mul_comm.
do 3 rewrite <- Nat.mul_assoc.
f_equal; f_equal.
apply Nat.mul_comm.
Qed.

Theorem summation_add : ∀ b e f g,
  Σ (i = b, e), (f i + g i) = Σ (i = b, e), f i + Σ (i = b, e), g i.
Proof.
intros.
remember (S e - b) as n eqn:Hn.
revert b Hn.
induction n; intros; [ easy | cbn ].
rewrite fold_left_add_fun_from_0.
rewrite IHn; [ | flia Hn ].
rewrite (fold_left_add_fun_from_0 (f b)).
rewrite (fold_left_add_fun_from_0 (g b)).
flia.
Qed.

Theorem summation_sub : ∀ b e f g,
  (∀ i, b ≤ i ≤ e → g i ≤ f i)
  → Σ (i = b, e), (f i - g i) = Σ (i = b, e), f i - Σ (i = b, e), g i.
Proof.
intros * Hgf.
remember (S e - b) as n eqn:Hn.
revert b Hn Hgf.
induction n; intros; [ easy | cbn ].
rewrite fold_left_add_fun_from_0.
rewrite IHn; [ | flia Hn | ]. 2: {
  intros i Hi.
  apply Hgf; flia Hi.
}
rewrite (fold_left_add_fun_from_0 (f b)).
rewrite (fold_left_add_fun_from_0 (g b)).
rewrite Nat.sub_add_distr.
rewrite Nat.add_sub_swap. 2: {
  apply Hgf.
  split; [ easy | ].
  flia Hn.
}
rewrite Nat.add_sub_assoc; [ easy | ].
assert (Hbe : b + n ≤ e) by flia Hn.
clear - Hbe Hgf.
revert b Hgf Hbe.
induction n; intros; [ easy | ].
replace (S n) with (n + 1) by flia.
rewrite seq_app.
do 2 rewrite fold_left_app.
setoid_rewrite fold_left_add_fun_from_0.
apply Nat.add_le_mono. 2: {
  cbn.
  apply Hgf.
  flia Hbe.
}
apply IHn; [ easy | flia Hbe ].
Qed.

Theorem summation_succ_succ : ∀ b e f,
  Σ (i = S b, S e), f i = Σ (i = b, e), f (S i).
Proof.
intros.
rewrite Nat.sub_succ.
remember (S e - b) as n eqn:Hn.
revert b Hn.
induction n; intros; [ easy | cbn ].
setoid_rewrite fold_left_add_fun_from_0.
rewrite IHn; [ easy | flia Hn ].
Qed.

Theorem summation_mod_idemp : ∀ b e f n,
  (Σ (i = b, e), f i) mod n = (Σ (i = b, e), f i mod n) mod n.
Proof.
intros.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz]; [ now subst n | ].
remember (S e - b) as m eqn:Hm.
revert b Hm.
induction m; intros; [ easy | cbn ].
rewrite (fold_left_add_fun_from_0 (f b)).
rewrite (fold_left_add_fun_from_0 (f b mod n)).
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
apply IHm; flia Hm.
Qed.

Lemma fold_left_seq_succ_last : ∀ g b len s,
  fold_left (λ c i, c + g i) (seq b (S len)) s =
  fold_left (λ c i, c + g i) (seq b len) s + g (b + len).
Proof.
intros.
revert b s.
induction len; intros; [ now cbn; rewrite Nat.add_0_r | ].
remember (S len) as x; cbn; subst x.
now rewrite IHlen, Nat.add_succ_comm.
Qed.

Theorem summation_rtl : ∀ g b k,
  Σ (i = b, k), g i = Σ (i = b, k), g (k + b - i).
Proof.
intros g b k.
destruct (le_dec (S k) b) as [Hkb| Hkb]. {
  cbn - [ "-" ].
  now replace (S k - b) with 0 by flia Hkb.
}
apply Nat.nle_gt in Hkb.
apply -> Nat.lt_succ_r in Hkb.
remember 0 as s.
remember (S k - b) as len eqn:Hlen.
replace k with (b + len - 1) by flia Hkb Hlen; clear.
revert s b.
induction len; intros; [ easy | ].
rewrite fold_left_seq_succ_last.
rewrite IHlen; cbn.
rewrite Nat.add_sub.
replace (b + S len - 1) with (b + len) by flia.
rewrite <- seq_shift.
rewrite List_fold_left_map.
setoid_rewrite fold_left_add_fun_from_0.
rewrite Nat.add_shuffle0; f_equal.
destruct len; [ easy | ].
replace (S len) with (S (len + b) - b) by flia.
apply summation_eq_compat.
intros i Hi; f_equal.
flia.
Qed.

(* *)

Theorem match_id {A} : ∀ a (b : A), match a with O => b | S _ => b end = b.
Proof. now intros; destruct a. Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem Nat_add_div_same : ∀ a b c,
  Nat.divide c a
  → a / c + b / c = (a + b) / c.
Proof.
intros * Hca.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]; [ now subst c | ].
destruct Hca as (d, Hd).
rewrite Hd, Nat.div_mul; [ | easy ].
now rewrite Nat.div_add_l.
Qed.

Theorem Nat_sub_div_same: ∀ a b c,
  Nat.divide c a
  → Nat.divide c b
  → a / c - b / c = (a - b) / c.
Proof.
intros * Hca Hcb.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]; [ now subst c | ].
destruct Hca as (ka, Hka).
destruct Hcb as (kb, Hkb).
subst a b.
rewrite Nat.div_mul; [ | easy ].
rewrite Nat.div_mul; [ | easy ].
rewrite <- Nat.mul_sub_distr_r.
now rewrite Nat.div_mul.
Qed.

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

Theorem Nat_eq_mod_sub_0 : ∀ a b c,
  a mod c = b mod c → (a - b) mod c = 0.
Proof.
intros * Hab.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]. 
subst c. simpl in *. lia.
specialize (Nat.div_mod a c Hcz) as H1.
specialize (Nat.div_mod b c Hcz) as H2.
rewrite H1, H2, Hab.
rewrite (Nat.add_comm (c * (b / c))).
rewrite Nat.sub_add_distr, Nat.add_sub.
rewrite <- Nat.mul_sub_distr_l, Nat.mul_comm.
now apply Nat.mod_mul.
Qed.

Theorem Nat_mod_add_r_mul_l : ∀ a b c,
  b ≠ 0 → (a + b * c) mod b = a mod b.
Proof.
intros * Hbz.
rewrite Nat.mul_comm.
now apply Nat.mod_add.
Qed.

Theorem Nat_mod_add_l_mul_l : ∀ a b c,
  b ≠ 0 → (b * c + a) mod b = a mod b.
Proof.
intros * Hbz.
rewrite Nat.add_comm, Nat.mul_comm.
now apply Nat.mod_add.
Qed.

Theorem Nat_mod_add_l_mul_r : ∀ a b c,
  b ≠ 0 → (c * b + a) mod b = a mod b.
Proof.
intros * Hbz.
rewrite Nat.add_comm.
now apply Nat.mod_add.
Qed.

Theorem Nat_mod_0_mod_div : ∀ a b,
  0 < b ≤ a → a mod b = 0 → a mod (a / b) = 0.
Proof.
intros * Hba Ha.
assert (Hbz : b ≠ 0) by flia Hba.
assert (Habz : a / b ≠ 0). {
  intros H.
  apply Nat.div_small_iff in H; [ | flia Hba ].
  now apply Nat.nle_gt in H.
}
specialize (Nat.div_mod a (a / b) Habz) as H1.
specialize (Nat.div_mod a b Hbz) as H2.
rewrite Ha, Nat.add_0_r in H2.
rewrite H2 in H1 at 3.
rewrite Nat.div_mul in H1; [ | easy ].
rewrite Nat.mul_comm in H1.
flia H1 H2.
Qed.

Theorem Nat_mod_0_div_div : ∀ a b,
  0 < b ≤ a → a mod b = 0 → a / (a / b) = b.
Proof.
intros * Hba Ha.
assert (Hbz : b ≠ 0) by flia Hba.
assert (Habz : a / b ≠ 0). {
  intros H.
  apply Nat.div_small_iff in H; [ | easy ].
  now apply Nat.nle_gt in H.
}
specialize (Nat.div_mod a (a / b) Habz) as H1.
rewrite Nat_mod_0_mod_div in H1; [ | easy | easy ].
rewrite Nat.add_0_r in H1.
apply (Nat.mul_cancel_l _ _ (a / b)); [ easy | ].
rewrite <- H1; symmetry.
rewrite Nat.mul_comm.
apply Nat.mod_divide in Ha; [ | easy ].
rewrite <- Nat.divide_div_mul_exact; [ | easy | easy ].
now rewrite Nat.mul_comm, Nat.div_mul.
Qed.

Theorem Nat_fact_succ : ∀ n, fact (S n) = S n * fact n.
Proof. easy. Qed.

Theorem Nat_div_lt_le_mul : ∀ a b c, b ≠ 0 → a / b < c → a ≤ b * c.
Proof.
intros * Hbz Habc.
apply (Nat.mul_le_mono_l _ _ b) in Habc.
transitivity (b * S (a / b)); [ | easy ].
specialize (Nat.div_mod a b Hbz) as H1.
rewrite <- Nat.add_1_r.
rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
rewrite H1 at 1.
apply Nat.add_le_mono_l.
now apply Nat.lt_le_incl, Nat.mod_upper_bound.
Qed.

Theorem Nat_divide_fact_fact : ∀ n d, Nat.divide (fact (n - d)) (fact n).
Proof.
intros *.
revert n.
induction d; intros; [ rewrite Nat.sub_0_r; apply Nat.divide_refl | ].
destruct n; [ apply Nat.divide_refl | ].
rewrite Nat.sub_succ.
apply (Nat.divide_trans _ (fact n)); [ apply IHd | ].
rewrite Nat_fact_succ.
now exists (S n).
Qed.

Theorem Nat_divide_small_fact : ∀ n k, 0 < k ≤ n → Nat.divide k (fact n).
Proof.
intros * Hkn.
revert k Hkn.
induction n; intros; [ flia Hkn | ].
rewrite Nat_fact_succ.
destruct (Nat.eq_dec k (S n)) as [Hksn| Hksn]. {
  rewrite Hksn.
  apply Nat.divide_factor_l.
}
apply (Nat.divide_trans _ (fact n)). {
  apply IHn; flia Hkn Hksn.
}
apply Nat.divide_factor_r.
Qed.

Theorem Nat_divide_mul_fact : ∀ n a b,
  0 < a ≤ n
  → 0 < b ≤ n
  → a < b
  → Nat.divide (a * b) (fact n).
Proof.
intros * Han Hbn Hab.
exists (fact (a - 1) * (fact (b - 1) / fact a) * (fact n / fact b)).
rewrite Nat.mul_comm.
rewrite (Nat.mul_shuffle0 _ b).
do 2 rewrite Nat.mul_assoc.
replace (a * fact (a - 1)) with (fact a). 2: {
  destruct a; [ flia Han | ].
  rewrite Nat_fact_succ.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
replace (fact a * (fact (b - 1) / fact a)) with (fact (b - 1)). 2: {
  specialize (Nat_divide_fact_fact (b - 1) (b - 1 - a)) as H1.
  replace (b - 1 - (b - 1 - a)) with a in H1 by flia Hab.
  destruct H1 as (c, Hc).
  rewrite Hc, Nat.div_mul; [ | apply fact_neq_0 ].
  apply Nat.mul_comm.
}
rewrite Nat.mul_comm, Nat.mul_assoc.
replace (b * fact (b - 1)) with (fact b). 2: {
  destruct b; [ flia Hbn | ].
  rewrite Nat_fact_succ.
  now rewrite Nat.sub_succ, Nat.sub_0_r.
}
replace (fact b * (fact n / fact b)) with (fact n). 2: {
  specialize (Nat_divide_fact_fact n (n - b)) as H1.
  replace (n - (n - b)) with b in H1 by flia Hbn.
  destruct H1 as (c, Hc).
  rewrite Hc, Nat.div_mul; [ | apply fact_neq_0 ].
  apply Nat.mul_comm.
}
easy.
Qed.

(** Bezout commutes *)

Theorem Nat_bezout_comm : ∀ a b g,
  b ≠ 0 → Nat.Bezout a b g → Nat.Bezout b a g.
Proof.
intros * Hbz (u & v & Huv).
destruct (Nat.eq_0_gt_0_cases a) as [Haz| Haz]. {
  rewrite Haz in Huv |-*.
  rewrite Nat.mul_0_r in Huv; symmetry in Huv.
  apply Nat.eq_add_0 in Huv.
  rewrite (proj1 Huv).
  now exists 0, 0; Nat.nzsimpl.
}
apply Nat.neq_0_lt_0 in Haz.
destruct (Nat.lt_trichotomy (u / b) (v / a)) as [Hm|Hm]. {
  apply Nat.lt_le_incl in Hm.
  remember (v / a + 1) as k eqn:Hk.
  exists (k * a - v), (k * b - u).
  do 2 rewrite Nat.mul_sub_distr_r.
  rewrite Huv.
  rewrite (Nat.add_comm _ (v * b)).
  rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub_assoc. 2: {
    apply (Nat.add_le_mono_r _ _ (v * b)).
    rewrite <- Huv.
    rewrite Nat.sub_add. 2: {
      rewrite Nat.mul_shuffle0.
      apply Nat.mul_le_mono_r.
      rewrite Hk.
      specialize (Nat.div_mod v a Haz) as H1.
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
      rewrite H1 at 1.
      apply Nat.add_le_mono_l.
      apply Nat.lt_le_incl.
      apply Nat.mod_bound_pos; [ apply Nat.le_0_l | ].
      now apply Nat.neq_0_lt_0.
    }
    apply Nat.mul_le_mono_r.
    rewrite Hk.
    specialize (Nat.div_mod u b Hbz) as H1.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
    rewrite H1 at 1.
    apply Nat.add_le_mono; [ now apply Nat.mul_le_mono_l | ].
    apply Nat.lt_le_incl.
    apply Nat.mod_bound_pos; [ apply Nat.le_0_l | ].
    now apply Nat.neq_0_lt_0.
  }
  rewrite Nat.add_comm, Nat.add_sub.
  now rewrite Nat.mul_shuffle0.
} {
  remember (u / b + 1) as k eqn:Hk.
  exists (k * a - v), (k * b - u).
  do 2 rewrite Nat.mul_sub_distr_r.
  rewrite Huv.
  rewrite (Nat.add_comm _ (v * b)).
  rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub_assoc. 2: {
    apply (Nat.add_le_mono_r _ _ (v * b)).
    rewrite Nat.sub_add. 2: {
      rewrite Nat.mul_shuffle0.
      apply Nat.mul_le_mono_r.
      rewrite Hk.
      specialize (Nat.div_mod v a Haz) as H1.
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
      rewrite H1 at 1.
      apply Nat.add_le_mono. {
        apply Nat.mul_le_mono_l.
        destruct Hm as [Hm| Hm]; [ now rewrite Hm | ].
        now apply Nat.lt_le_incl.
      }
      apply Nat.lt_le_incl.
      apply Nat.mod_bound_pos; [ apply Nat.le_0_l | ].
      now apply Nat.neq_0_lt_0.
    }
    rewrite <- Huv.
    apply Nat.mul_le_mono_r.
    rewrite Hk.
    specialize (Nat.div_mod u b Hbz) as H1.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.mul_comm.
    rewrite H1 at 1.
    apply Nat.add_le_mono_l.
    apply Nat.lt_le_incl.
    apply Nat.mod_bound_pos; [ apply Nat.le_0_l | ].
    now apply Nat.neq_0_lt_0.
  }
  rewrite Nat.add_comm, Nat.add_sub.
  now rewrite Nat.mul_shuffle0.
}
Qed.

Theorem Nat_bezout_mul : ∀ a b c,
  Nat.Bezout a c 1
  → Nat.Bezout b c 1
  → Nat.Bezout (a * b) c 1.
Proof.
intros * (ua & uc & Hu) (vb & vc & Hv).
exists (ua * vb).
replace (ua * vb * (a * b)) with ((ua * a) * (vb * b)) by flia.
rewrite Hu, Hv.
exists (uc * vc * c + uc + vc).
ring.
Qed.

Theorem Nat_gcd_le_r : ∀ a b, b ≠ 0 → Nat.gcd a b ≤ b.
Proof.
intros * Hbz.
specialize (Nat.gcd_divide_r a b) as H1.
destruct H1 as (c, Hc); rewrite Hc at 2.
destruct c; [ easy | flia ].
Qed.

Theorem Nat_gcd_1_mul_l : ∀ a b c,
  Nat.gcd a c = 1
  → Nat.gcd b c = 1
  → Nat.gcd (a * b) c = 1.
Proof.
intros * Hac Hbc.
destruct (Nat.eq_dec c 0) as [Hcz| Hcz]. {
  now subst c; rewrite Nat.gcd_comm in Hac, Hbc; cbn in Hac, Hbc; subst a b.
}
destruct (Nat.eq_dec a 0) as [Haz| Haz]; [ now subst a | ].
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]. {
  now subst b; rewrite Nat.mul_0_r.
}
apply Nat.bezout_1_gcd.
apply Nat_bezout_mul. {
  rewrite <- Hac.
  apply Nat.gcd_bezout_pos.
  flia Haz.
} {
  rewrite <- Hbc.
  apply Nat.gcd_bezout_pos.
  flia Hbz.
}
Qed.

Theorem Nat_gcd_1_mul_r : ∀ a b c,
  Nat.gcd a b = 1
  → Nat.gcd a c = 1
  → Nat.gcd a (b * c) = 1.
Proof.
intros * Hab Hac.
rewrite Nat.gcd_comm.
now apply Nat_gcd_1_mul_l; rewrite Nat.gcd_comm.
Qed.

Theorem Nat_gcd_sub_diag_l : ∀ m n, n ≤ m → Nat.gcd m (m - n) = Nat.gcd m n.
Proof.
intros * Hnm.
replace m with (n + (m - n)) at 1 by flia Hnm.
rewrite Nat.gcd_comm.
rewrite Nat.gcd_add_diag_r.
rewrite Nat.gcd_comm.
rewrite Nat.gcd_sub_diag_r; [ | easy ].
apply Nat.gcd_comm.
Qed.

(* (a ^ b) mod c defined like that so that we can use "Compute"
   for testing; proved equal to (a ^ b) mod c just below *)

Fixpoint Nat_pow_mod_loop a b c :=
  match b with
  | 0 => 1 mod c
  | S b' => (a * Nat_pow_mod_loop a b' c) mod c
  end.

Definition Nat_pow_mod a b c := Nat_pow_mod_loop a b c.

Theorem Nat_pow_mod_is_pow_mod : ∀ a b c,
  c ≠ 0 → Nat_pow_mod a b c = (a ^ b) mod c.
Proof.
intros * Hcz.
revert a.
induction b; intros; [ easy | ].
cbn; rewrite IHb.
now rewrite Nat.mul_mod_idemp_r.
Qed.

Theorem Nat_pow_sub_pow : ∀ a b n,
  n ≠ 0
  → b ≤ a
  → a ^ n - b ^ n =
     (a - b) * Σ (i = 0, n - 1), a ^ (n - i - 1) * b ^ i.
Proof.
intros * Hnz Hba.
destruct n; [ easy | clear Hnz ].
induction n; [ now cbn; do 3 rewrite Nat.mul_1_r | ].
remember (S n) as sn; cbn - [ "-" ]; subst sn.
rewrite <- (Nat.sub_add (a * b ^ S n) (a * a ^ S n)). 2: {
  apply Nat.mul_le_mono_l.
  now apply Nat.pow_le_mono_l.
}
rewrite <- Nat.mul_sub_distr_l.
rewrite <- Nat.add_sub_assoc; [ | now apply Nat.mul_le_mono_r ].
rewrite <- Nat.mul_sub_distr_r.
rewrite (Nat.mul_comm a).
rewrite IHn, <- Nat.mul_assoc.
rewrite <- Nat.mul_add_distr_l; f_equal.
do 2 rewrite Nat.sub_succ.
replace (n - 0) with n by now rewrite Nat.sub_0_r.
replace (S n - 0) with (S n) at 2 by now rewrite Nat.sub_0_r.
rewrite (summation_split_last _ (S n)); [ | flia | flia ].
rewrite Nat.sub_succ.
replace (n - 0) with n by now rewrite Nat.sub_0_r.
replace (S (S n) - S n - 1) with 0 by flia.
rewrite Nat.pow_0_r, Nat.mul_1_l.
f_equal.
rewrite mul_summation_distr_r.
apply summation_eq_compat.
intros i Hi.
rewrite Nat.mul_shuffle0; f_equal.
rewrite <- (Nat.pow_1_r a) at 2.
rewrite <- Nat.pow_add_r.
f_equal; flia Hi.
Qed.

Theorem Nat_sqr_sub_sqr : ∀ a b, a ^ 2 - b ^ 2 = (a + b) * (a - b).
Proof.
intros.
destruct (lt_dec a b) as [Hab| Hba]. {
  rewrite (proj2 (Nat.sub_0_le _ _)). 2: {
    now apply Nat.pow_le_mono_l, Nat.lt_le_incl.
  }
  rewrite (proj2 (Nat.sub_0_le _ _)). 2: {
    now apply Nat.lt_le_incl.
  }
  now rewrite Nat.mul_0_r.
}
apply Nat.nlt_ge in Hba.
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_sub_distr_l.
rewrite Nat.mul_sub_distr_l.
rewrite Nat.add_sub_assoc; [ | now apply Nat.mul_le_mono_l ].
rewrite (Nat.mul_comm b).
rewrite Nat.sub_add; [ | now apply Nat.mul_le_mono_l ].
now do 2 rewrite Nat.pow_2_r.
Qed.

Theorem Nat_sqr_sub_1 : ∀ a, a ^ 2 - 1 = (a + 1) * (a - 1).
Proof.
intros.
destruct (Nat.eq_dec a 0) as [Haz| Haz]; [ now subst a | ].
rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
rewrite Nat.add_sub_assoc; [ | flia Haz ].
rewrite Nat.pow_2_r.
rewrite Nat.sub_add; [ easy | ].
destruct a; [ easy | flia ].
Qed.

Theorem Nat_sub_sub_assoc : ∀ a b c,
  c ≤ b ≤ a + c
  → a - (b - c) = a + c - b.
Proof.
intros * (Hcb, Hba).
revert a c Hcb Hba.
induction b; intros.
-apply Nat.le_0_r in Hcb; subst c.
 now rewrite Nat.add_0_r.
-destruct c; [ now rewrite Nat.add_0_r | ].
 apply Nat.succ_le_mono in Hcb.
 rewrite Nat.add_succ_r in Hba.
 apply Nat.succ_le_mono in Hba.
 specialize (IHb a c Hcb Hba) as H1.
 rewrite Nat.sub_succ, H1.
 rewrite Nat.add_succ_r.
 now rewrite Nat.sub_succ.
Qed.

Theorem Nat_sub_sub_distr : ∀ a b c, c ≤ b ≤ a → a - (b - c) = a - b + c.
Proof.
intros.
rewrite <- Nat.add_sub_swap; [ | easy ].
apply Nat_sub_sub_assoc.
split; [ easy | ].
apply (Nat.le_trans _ a); [ easy | ].
apply Nat.le_add_r.
Qed.

Theorem Nat_sqr_sub : ∀ a b, b ≤ a → (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b.
Proof.
intros * Hba.
do 3 rewrite Nat.pow_2_r.
rewrite Nat.mul_sub_distr_l.
do 2 rewrite Nat.mul_sub_distr_r.
rewrite (Nat.mul_comm b).
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
rewrite Nat.sub_add_distr.
rewrite Nat_sub_sub_distr. 2: {
  split; [ now apply Nat.mul_le_mono_r | now apply Nat.mul_le_mono_l ].
}
replace 2 with (1 + 1) by easy.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
rewrite Nat.mul_add_distr_r.
rewrite Nat.sub_add_distr; f_equal.
rewrite Nat.add_sub_swap; [ easy | ].
now apply Nat.mul_le_mono_l.
Qed.

Theorem Nat_sqr_add : ∀ a b, (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b.
Proof.
intros.
do 3 rewrite Nat.pow_2_r; flia.
Qed.

Theorem Nat_mod_pow_mod : ∀ a b c, (a mod b) ^ c mod b = a ^ c mod b.
Proof.
intros.
destruct (Nat.eq_dec b 0) as [Hbz| Hbz]; [ now subst b | ].
revert a b Hbz.
induction c; intros; [ easy | cbn ].
rewrite Nat.mul_mod_idemp_l; [ | easy ].
rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
rewrite IHc; [ | easy ].
now rewrite Nat.mul_mod_idemp_r.
Qed.

Notation "a ≡ b 'mod' c" := (a mod c = b mod c) (at level 70, b at level 36).
Notation "a ≢ b 'mod' c" := (a mod c ≠ b mod c) (at level 70, b at level 36).

Theorem Nat_mul_mod_cancel_r : ∀ a b c n,
  Nat.gcd c n = 1
  → a * c ≡ (b * c) mod n
  → a ≡ b mod n.
Proof.
intros * Hg Hab.
destruct (Nat.eq_dec n 0) as [Hnz| Hnz].
subst n. rewrite Nat.gcd_0_r in Hg.
simpl in *. lia.
destruct (le_dec b a) as [Hba| Hba]. {
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite <- Nat.mul_sub_distr_r in Hab.
  apply Nat.mod_divide in Hab; [ | easy ].
  rewrite Nat.gcd_comm in Hg.
  rewrite Nat.mul_comm in Hab.
  specialize (Nat.gauss n c (a - b) Hab Hg) as H1.
  destruct H1 as (k, Hk).
  replace a with (b + k * n) by flia Hba Hk.
  now rewrite Nat.mod_add.
} {
  apply Nat.nle_gt in Hba.
  symmetry in Hab.
  apply Nat_eq_mod_sub_0 in Hab.
  rewrite <- Nat.mul_sub_distr_r in Hab.
  apply Nat.mod_divide in Hab; [ | easy ].
  rewrite Nat.gcd_comm in Hg.
  rewrite Nat.mul_comm in Hab.
  specialize (Nat.gauss n c (b - a) Hab Hg) as H1.
  destruct H1 as (k, Hk).
  replace b with (a + k * n) by flia Hba Hk.
  now rewrite Nat.mod_add.
}
Qed.

Theorem Nat_mul_mod_cancel_l : ∀ a b c n,
  Nat.gcd c n = 1
  → c * a ≡ (c * b) mod n
  → a ≡ b mod n.
Proof.
intros * Hg Hab.
setoid_rewrite Nat.mul_comm in Hab.
now apply Nat_mul_mod_cancel_r in Hab.
Qed.

Definition Nat_le_neq_lt : ∀ x y : nat, x ≤ y → x ≠ y → (x < y)%nat :=
  λ x y Hxy Hnxy,
  match le_lt_eq_dec x y Hxy with
  | left Hle => Hle
  | right Heq => match Hnxy Heq with end
  end.

Theorem List_hd_nth_0 {A} : ∀ l (d : A), hd d l = nth 0 l d.
Proof. intros; now destruct l. Qed.

Theorem List_map_map_map {A B C D} : ∀ (f : A → B → C) (g : A → D → B) h l,
  map (λ d, map (f d) (map (g d) (h d))) l =
  map (λ d, map (λ x, (f d (g d x))) (h d)) l.
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
now rewrite List.map_map, IHl.
Qed.

Theorem List_flat_map_length {A B} : ∀ (l : list A) (f : _ → list B),
  length (flat_map f l) =
    List.fold_right Nat.add 0 (map (@length B) (map f l)).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
now rewrite app_length, IHl.
Qed.

Theorem List_last_seq : ∀ i n, n ≠ 0 → last (seq i n) 0 = i + n - 1.
Proof.
intros * Hn.
destruct n; [ easy | clear Hn ].
revert i; induction n; intros. {
  cbn; symmetry.
  apply Nat.add_sub.
}
remember (S n) as sn; cbn; subst sn.
remember (seq (S i) (S n)) as l eqn:Hl.
destruct l; [ easy | ].
rewrite Hl.
replace (i + S (S n)) with (S i + S n) by flia.
apply IHn.
Qed.

Theorem List_last_In {A} : ∀ (d : A) l, l ≠ [] → In (last l d) l.
Proof.
intros * Hl.
destruct l as [| a l]; [ easy | clear Hl ].
revert a.
induction l as [| b l]; intros; [ now left | ].
remember (b :: l) as l'; cbn; subst l'.
right; apply IHl.
Qed.

Theorem List_last_app {A} : ∀ l (d a : A), List.last (l ++ [a]) d = a.
Proof.
intros.
induction l; [ easy | ].
cbn.
remember (l ++ [a]) as l' eqn:Hl'.
destruct l'; [ now destruct l | apply IHl ].
Qed.

Theorem List_map_fun {A} : ∀ l l' (f : nat → A),
  length l = length l'
  → (∀ i, f (nth i l 0) = f (nth i l' 0))
  → map f l = map f l'.
Proof.
intros * Hlen Hf.
revert l' Hlen Hf.
induction l as [| a l]; intros; [ now destruct l' | ].
destruct l' as [| a' l']; [ easy | cbn ].
specialize (Hf 0) as H1; cbn in H1.
rewrite H1; f_equal.
cbn in Hlen; apply Nat.succ_inj in Hlen.
apply IHl; [ easy | ].
intros i.
now specialize (Hf (S i)).
Qed.

Theorem List_map_nth_in {A B} : ∀ (f : A → B) a b l n,
  n < length l → nth n (map f l) b = f (nth n l a).
Proof.
intros * Hnl.
revert n Hnl.
induction l as [| c l]; intros; [ easy | ].
cbn in Hnl; cbn.
destruct n; [ easy | ].
apply Nat.succ_lt_mono in Hnl.
now apply IHl.
Qed.

Theorem List_firstn_seq : ∀ n start len,
  firstn n (seq start len) = seq start (min n len).
Proof.
intros.
revert start len.
induction n; intros; [ easy | cbn ].
remember (seq start len) as l eqn:Hl; symmetry in Hl.
destruct l as [| a l]; [ now destruct len | ].
destruct len; [ easy | cbn in Hl; cbn ].
injection Hl; clear Hl; intros Hl Ha.
subst start; f_equal.
rewrite <- Hl; apply IHn.
Qed.

Theorem List_filter_all_true {A} : ∀ f (l : list A),
  (∀ a, a ∈ l → f a = true) → filter f l = l.
Proof.
intros * Hf.
induction l as [| a l]; [ easy | ].
cbn; rewrite Hf; [ | now left ].
rewrite IHl; [ easy | ].
intros b Hb.
apply Hf.
now right.
Qed.

Theorem List_filter_all_false {A} : ∀ f (l : list A),
  (∀ a, a ∈ l → f a = false) → filter f l = [].
Proof.
intros * Hf.
induction l as [| a l]; [ easy | ].
cbn; rewrite Hf; [ | now left ].
apply IHl; intros b Hb.
now apply Hf; right.
Qed.

Theorem List_filter_nil {A} : ∀ f (l : list A),
  filter f l = [] → (∀ a, a ∈ l → f a = false).
Proof.
intros * Hf a Ha.
induction l as [| b l]; [ easy | ].
cbn in Hf.
remember (f b) as c eqn:Hc; symmetry in Hc.
destruct c; [ easy | ].
destruct Ha as [Ha| Ha]; [ now subst b | ].
now apply IHl.
Qed.

Theorem List_filter_filter {A} : ∀ (f g : A → _) l,
  filter f (filter g l) = filter (λ a, andb (f a) (g a)) l.
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
remember (andb (f a) (g a)) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply Bool.andb_true_iff in Hb.
  rewrite (proj2 Hb); cbn.
  rewrite (proj1 Hb); cbn.
  now rewrite IHl.
} {
  apply Bool.andb_false_iff in Hb.
  destruct Hb as [Hb| Hb]. {
    remember (g a) as c eqn:Hc; symmetry in Hc.
    destruct c; [ | apply IHl ].
    cbn; rewrite Hb.
    apply IHl.
  } {
    rewrite Hb; cbn.
    apply IHl.
  }
}
Qed.

Theorem List_filter_filter_comm {A} : ∀ (f : A → _) g l,
  filter f (filter g l) = filter g (filter f l).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
remember (g a) as bg eqn:Hbg; symmetry in Hbg.
remember (f a) as bf eqn:Hbf; symmetry in Hbf.
move bf before bg.
destruct bg, bf; cbn. {
  rewrite Hbg, Hbf.
  now rewrite IHl.
} {
  now rewrite Hbf, IHl.
} {
  now rewrite Hbg, IHl.
} {
  apply IHl.
}
Qed.

Theorem List_fold_filter_comm {A B} : ∀ f g (al : list A) (l : list B),
  fold_left (λ l a, filter (f a) l) al (filter g l) =
  filter g (fold_left (λ l a, filter (f a) l) al l).
Proof.
intros.
revert l.
induction al as [| a al]; intros; [ easy | ].
cbn.
rewrite <- IHal.
now rewrite List_filter_filter_comm.
Qed.

Theorem List_length_filter_negb {A} : ∀ f (l : list A),
  NoDup l
  → length (filter f l) = length l - length (filter (λ x, negb (f x)) l).
Proof.
intros * Hl.
induction l as [| a l]; [ easy | ].
cbn - [ "-" ].
remember (f a) as b eqn:Hb; symmetry in Hb.
destruct b; cbn - [ "-" ]. {
  rewrite IHl; [ | now apply NoDup_cons_iff in Hl ].
  rewrite Nat.sub_succ_l; [ easy | ].
  clear.
  induction l as [| a l]; [ easy | cbn ].
  destruct (negb (f a)); cbn. {
    now apply Nat.succ_le_mono in IHl.
  } {
    transitivity (length l); [ easy | flia ].
  }
} {
  rewrite Nat.sub_succ.
  apply IHl.
  now apply NoDup_cons_iff in Hl.
}
Qed.

Theorem List_length_filter_or {A B} : ∀ (p q : A) (l : list B) f g,
  length (filter (λ a, (f p a || g q a)%bool) l) =
  length (filter (f p) l) + length (filter (g q) l) -
  length (filter (λ a, (f p a && g q a)%bool) l).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
remember (f p a) as b eqn:Hb; symmetry in Hb.
remember (g q a) as c eqn:Hc; symmetry in Hc.
assert (Hpq :
  length (filter (λ a, (f p a && g q a)%bool) l) ≤
  length (filter (f p) l) + length (filter (g q) l)). {
  clear.
  induction l as [| a l]; [ easy | cbn ].
  remember (f p a) as b eqn:Hb; symmetry in Hb.
  remember (g q a) as c eqn:Hc; symmetry in Hc.
  destruct b, c; cbn; [ flia IHl | flia IHl | flia IHl | easy ].
}
destruct b, c; cbn - [ "-" ]. {
  rewrite IHl.
  rewrite <- Nat.sub_succ_l; [ flia | easy ].
} {
  rewrite IHl.
  now rewrite <- Nat.sub_succ_l.
} {
  rewrite IHl.
  rewrite <- Nat.sub_succ_l; [ flia | easy ].
} {
  apply IHl.
}
Qed.

Theorem not_equiv_imp_False : ∀ P : Prop, (P → False) ↔ ¬ P.
Proof. easy. Qed.

Theorem Sorted_Sorted_seq : ∀ start len, Sorted.Sorted lt (seq start len).
Proof.
intros.
revert start.
induction len; intros; [ apply Sorted.Sorted_nil | ].
cbn; apply Sorted.Sorted_cons; [ apply IHlen | ].
clear IHlen.
induction len; [ apply Sorted.HdRel_nil | ].
cbn. apply Sorted.HdRel_cons.
apply Nat.lt_succ_diag_r.
Qed.

Theorem Forall_inv_tail {A} : ∀ P (a : A) l, Forall P (a :: l) → Forall P l.
Proof.
intros * HF.
now inversion HF.
Qed.

Theorem NoDup_app_comm {A} : ∀ l l' : list A,
  NoDup (l ++ l') → NoDup (l' ++ l).
Proof.
intros * Hll.
revert l Hll.
induction l' as [| a l']; intros; [ now rewrite app_nil_r in Hll | ].
cbn; constructor. {
  intros Ha.
  apply NoDup_remove_2 in Hll; apply Hll.
  apply in_app_or in Ha.
  apply in_or_app.
  now destruct Ha; [ right | left ].
}
apply IHl'.
now apply NoDup_remove_1 in Hll.
Qed.

Theorem List_in_app_app_swap {A} : ∀ (a : A) l1 l2 l3,
  In a (l1 ++ l3 ++ l2)
  → In a (l1 ++ l2 ++ l3).
Proof.
intros * Hin.
revert l2 l3 Hin.
induction l1 as [| a2 l1]; intros. {
  cbn in Hin; cbn.
  apply in_app_or in Hin.
  apply in_or_app.
  now destruct Hin; [ right | left ].
}
cbn in Hin; cbn.
destruct Hin as [Hin| Hin]; [ now left | right ].
now apply IHl1.
Qed.

Theorem List_in_removelast : ∀ A l (x : A), x ∈ removelast l → x ∈ l.
Proof.
intros * Hx.
revert x Hx.
induction l as [| a]; intros; [ easy | ].
cbn in Hx.
destruct l as [| b]; [ easy | ].
destruct Hx as [Hx| Hx]; [ now left | right ].
now apply IHl.
Qed.

Theorem List_fold_left_ext_in : ∀ A B (f g : A → B → A) l a,
  (∀ b c, b ∈ l → f c b = g c b)
  → fold_left f l a = fold_left g l a.
Proof.
intros * Hfg.
revert a.
induction l as [| d]; intros; [ easy | cbn ].
rewrite (Hfg d a); [ | now left ].
apply IHl.
intros b c Hb.
apply Hfg.
now right.
Qed.

Theorem List_fold_left_mul_assoc : ∀ a b l,
  fold_left Nat.mul l a * b = fold_left Nat.mul l (a * b).
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | ].
cbn; rewrite IHl.
now rewrite Nat.mul_shuffle0.
Qed.

Theorem List_firstn_map {A B} : ∀ n l (f : A → B),
  firstn n (map f l) = map f (firstn n l).
Proof.
intros.
revert n.
induction l as [| a l]; intros; [ now cbn; do 2 rewrite firstn_nil | ].
destruct n; [ easy | cbn ].
now rewrite IHl.
Qed.

Theorem List_list_prod_nil_r {A B} : ∀ l : list A,
  list_prod l ([] : list B) = [].
Proof.
intros.
now induction l.
Qed.

Theorem List_eq_rev_nil {A} : ∀ (l : list A), rev l = [] → l = [].
Proof.
intros * Hl.
destruct l as [| a]; [ easy | cbn in Hl ].
now apply app_eq_nil in Hl.
Qed.

Theorem List_app_cons : ∀ A (l1 l2 : list A) a,
  l1 ++ a :: l2 = l1 ++ [a] ++ l2.
Proof. easy. Qed.

Theorem List_skipn_map : ∀ A B (f : A → B) l n,
  skipn n (map f l) = map f (skipn n l).
Proof.
intros.
revert n.
induction l as [| a]; intros; [ now do 2 rewrite skipn_nil | cbn ].
destruct n; [ easy | cbn; apply IHl ].
Qed.

Theorem List_skipn_seq : ∀ n start len,
  n ≤ len → skipn n (seq start len) = seq (start + n) (len - n).
Proof.
intros * Hnlen.
revert n start Hnlen.
induction len; intros; [ now rewrite skipn_nil | cbn ].
destruct n; [ now cbn; rewrite Nat.add_0_r | cbn ].
rewrite <- Nat.add_succ_comm.
apply Nat.succ_le_mono in Hnlen.
now apply IHlen.
Qed.

Theorem List_last_nth : ∀ A l (d : A), last l d = nth (length l - 1) l d.
Proof.
intros.
destruct l as [| a]; [ easy | ].
cbn - [ last nth ].
rewrite Nat.sub_0_r.
revert a.
induction l as [| b]; intros; [ easy | ].
cbn - [ last nth ].
remember (b :: l) as l'; cbn; subst l'.
apply IHl.
Qed.

Theorem NoDup_app_app_swap {A} : ∀ l1 l2 l3 : list A,
  NoDup (l1 ++ l2 ++ l3) → NoDup (l1 ++ l3 ++ l2).
Proof.
intros * Hlll.
revert l2 l3 Hlll.
induction l1 as [| a1 l1]; intros; [ now cbn; apply NoDup_app_comm | ].
cbn; constructor. {
  intros Hin.
  cbn in Hlll.
  apply NoDup_cons_iff in Hlll.
  destruct Hlll as (Hin2, Hlll).
  apply Hin2; clear Hin2.
  now apply List_in_app_app_swap.
}
apply IHl1.
cbn in Hlll.
now apply NoDup_cons_iff in Hlll.
Qed.

Theorem NoDup_concat_rev {A} : ∀ (ll : list (list A)),
  NoDup (concat (rev ll)) → NoDup (concat ll).
Proof.
intros * Hll.
destruct ll as [| l ll]; [ easy | ].
cbn; cbn in Hll.
rewrite concat_app in Hll; cbn in Hll.
rewrite app_nil_r in Hll.
apply NoDup_app_comm.
revert l Hll.
induction ll as [| l' ll]; intros; [ easy | ].
cbn in Hll; cbn.
rewrite concat_app in Hll; cbn in Hll.
rewrite app_nil_r, <- app_assoc in Hll.
rewrite <- app_assoc.
apply NoDup_app_app_swap.
rewrite app_assoc.
apply NoDup_app_comm.
now apply IHll.
Qed.

Theorem NoDup_filter {A} : ∀ (f : A → _) l, NoDup l → NoDup (filter f l).
Proof.
intros * Hnd.
induction l as [| a l]; [ easy | cbn ].
remember (f a) as b eqn:Hb; symmetry in Hb.
apply NoDup_cons_iff in Hnd.
destruct Hnd as (Hal, Hl).
destruct b. {
  constructor; [ | now apply IHl ].
  intros H; apply Hal.
  now apply filter_In in H.
}
now apply IHl.
Qed.

Theorem NoDup_map_iff {A B} : ∀ d l (f : A → B),
  NoDup (map f l)
  ↔ (∀ i j,
      i < length l → j < length l → f (nth i l d) = f (nth j l d) → i = j).
Proof.
intros.
split. {
  intros Hnd i j Hi Hj Hij.
  revert i j Hi Hj Hij.
  induction l as [| a l]; intros; [ easy | ].
  cbn in Hnd.
  apply NoDup_cons_iff in Hnd.
  destruct Hnd as (Hnin, Hnd).
  specialize (IHl Hnd).
  destruct i. {
    destruct j; [ easy | exfalso ].
    cbn in Hij, Hj; clear Hi.
    apply Nat.succ_lt_mono in Hj.
    rewrite Hij in Hnin; apply Hnin; clear Hnin.
    now apply in_map, nth_In.
  }
  cbn in Hi, Hj.
  destruct j; [ exfalso | ]. {
    cbn in Hij, Hj; clear Hj.
    apply Nat.succ_lt_mono in Hi.
    rewrite <- Hij in Hnin; apply Hnin; clear Hnin.
    now apply in_map, nth_In.
  }
  apply Nat.succ_lt_mono in Hi.
  apply Nat.succ_lt_mono in Hj.
  cbn in Hij.
  f_equal.
  now apply IHl.
} {
  intros Hinj.
  induction l as [| a l]; [ constructor | cbn ].
  apply NoDup_cons. {
    intros Hcon.
    apply in_map_iff in Hcon.
    destruct Hcon as (b & Hba & Hb).
    symmetry in Hba.
    apply (In_nth _ _ d) in Hb.
    destruct Hb as (n & Hlen & Hnth).
    specialize (Hinj 0 (S n)) as H1.
    cbn in H1; rewrite Hnth in H1.
    apply Nat.succ_lt_mono in Hlen.
    now specialize (H1 (Nat.lt_0_succ _) Hlen Hba).
  }
  apply IHl.
  intros i j Hi Hj Hij.
  apply Nat.succ_lt_mono in Hi.
  apply Nat.succ_lt_mono in Hj.
  specialize (Hinj (S i) (S j) Hi Hj Hij) as H1.
  now apply Nat.succ_inj in H1.
}
Qed.

Theorem NoDup_app_remove_l : ∀ A (l l' : list A), NoDup (l ++ l') → NoDup l'.
Proof.
intros * Hnd.
apply NoDup_app_comm in Hnd.
revert l Hnd.
induction l' as [| b]; intros; [ constructor | ].
cbn in Hnd.
apply NoDup_cons_iff in Hnd.
destruct Hnd as (H1, H2).
constructor; [ | now apply IHl' in H2 ].
intros H; apply H1.
now apply in_or_app; left.
Qed.

Theorem NoDup_app_remove_r : ∀ A (l l' : list A), NoDup (l ++ l') → NoDup l.
Proof.
intros * Hnd.
apply NoDup_app_comm in Hnd.
now apply NoDup_app_remove_l in Hnd.
Qed.

Theorem NoDup_app_iff : ∀ A (l l' : list A),
  NoDup (l ++ l') ↔
    NoDup l ∧ NoDup l' ∧ (∀ a, a ∈ l → a ∉ l').
Proof.
intros.
split. {
  intros Hnd.
  split; [ now apply NoDup_app_remove_r in Hnd | ].
  split; [ now apply NoDup_app_remove_l in Hnd | ].
  intros a Ha Ha'.
  revert l' Hnd Ha'.
  induction l as [| b]; intros; [ easy | ].
  destruct Ha as [Ha| Ha]. {
    subst b.
    apply NoDup_app_comm in Hnd.
    apply NoDup_remove_2 in Hnd.
    apply Hnd.
    now apply in_app_iff; left.
  }
  apply (IHl Ha l'); [ | easy ].
  cbn in Hnd.
  now apply NoDup_cons_iff in Hnd.
} {
  intros * (Hnl & Hnl' & Hll).
  revert l' Hnl' Hll.
  induction l as [| b l]; intros; [ easy | cbn ].
  constructor. {
    intros Hb.
    apply in_app_or in Hb.
    destruct Hb as [Hb| Hb]. {
      now apply NoDup_cons_iff in Hnl.
    } {
      now specialize (Hll b (or_introl eq_refl)) as H1.
    }
  } {
    apply NoDup_cons_iff in Hnl.
    apply IHl; [ easy | easy | ].
    intros a Ha.
    now apply Hll; right.
  }
}
Qed.

Theorem NoDup_prod {A} {B} : ∀ (l : list A) (l' : list B),
  NoDup l → NoDup l' → NoDup (list_prod l l').
Proof.
intros * Hnl Hnl'.
revert l' Hnl'.
induction l as [| a l]; intros; [ constructor | ].
cbn.
apply NoDup_app_iff.
split. {
  induction l' as [| b l']; [ constructor | ].
  apply NoDup_cons. {
    intros Hab.
    apply NoDup_cons_iff in Hnl'; apply Hnl'.
    clear - Hab.
    induction l' as [| c l']; [ easy | ].
    cbn in Hab.
    destruct Hab as [Hab| Hab]. {
      injection Hab; clear Hab; intros; subst c.
      now left.
    } {
      now right; apply IHl'.
    }
  }
  apply IHl'.
  now apply NoDup_cons_iff in Hnl'.
}
split. {
  apply IHl; [ | easy ].
  now apply NoDup_cons_iff in Hnl.
} {
  intros (a', b) Hab.
  assert (H : a = a'). {
    clear - Hab.
    induction l' as [| b' l']; [ easy | ].
    cbn in Hab.
    destruct Hab as [Hab| Hab]; [ congruence | ].
    now apply IHl'.
  }
  subst a'.
  intros H.
  apply in_prod_iff in H.
  now apply NoDup_cons_iff in Hnl.
}
Qed.

Theorem Permutation_fold_mul : ∀ l1 l2 a,
  Permutation l1 l2 → fold_left Nat.mul l1 a = fold_left Nat.mul l2 a.
Proof.
intros * Hperm.
induction Hperm using Permutation_ind; [ easy | | | ]. {
  cbn; do 2 rewrite <- List_fold_left_mul_assoc.
  now rewrite IHHperm.
} {
  now cbn; rewrite Nat.mul_shuffle0.
}
etransitivity; [ apply IHHperm1 | apply IHHperm2 ].
Qed.

Theorem not_forall_in_interv_imp_exist : ∀ a b (P : nat → Prop),
  (∀ n, decidable (P n))
  → a ≤ b
  → (¬ (∀ n, a ≤ n ≤ b → ¬ P n))
  → ∃ n, P n.
Proof.
intros * Hdec Hab Hnab.
revert a Hab Hnab.
induction b; intros. {
  apply Nat.le_0_r in Hab; subst a.
  exists 0.
  destruct (Hdec 0) as [H1| H1]; [ easy | ].
  exfalso; apply Hnab.
  intros * Hn.
  now replace n with 0 by flia Hn.
}
destruct (Nat.eq_dec a (S b)) as [Hasb| Hasb]. {
  exists (S b).
  destruct (Hdec (S b)) as [H1| H1]; [ easy | ].
  exfalso; apply Hnab.
  intros * Hn.
  now replace n with (S b) by flia Hasb Hn.
}
assert (H : a ≤ b) by flia Hab Hasb.
move H before Hab; clear Hab Hasb; rename H into Hab.
destruct (Hdec (S b)) as [H1| H1]; [ now exists (S b) | ].
apply (IHb a); [ easy | ].
intros H; apply Hnab.
intros n Hn.
destruct (Nat.eq_dec n (S b)) as [H2| H2]; [ now rewrite H2 | ].
apply H; flia Hn H2.
Qed.

Fixpoint merge {A} (le : A → A → bool) l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if le a1 a2 then a1 :: merge le l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.

Fixpoint merge_list_to_stack {A} (le : A → A → bool) stack l :=
  match stack with
  | [] => [Some l]
  | None :: stack' => Some l :: stack'
  | Some l' :: stack' => None :: merge_list_to_stack le stack' (merge le l' l)
  end.

Fixpoint merge_stack {A} (le : A → A → bool) stack :=
  match stack with
  | [] => []
  | None :: stack' => merge_stack le stack'
  | Some l :: stack' => merge le l (merge_stack le stack')
  end.

Fixpoint iter_merge {A} (le : A → A → bool) stack l :=
  match l with
  | [] => merge_stack le stack
  | a::l' => iter_merge le (merge_list_to_stack le stack [a]) l'
  end.

Definition bsort {A} (le : A → A → bool) := iter_merge le [].
