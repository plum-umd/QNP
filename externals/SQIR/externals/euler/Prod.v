(* Product formula of φ *)

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Psatz Misc Primes Totient Primisc.

Definition prod (l : list nat) := fold_left Nat.mul l 1.
Arguments prod l /.

Definition pow_in_n n p := count_occ Nat.eq_dec (prime_decomp n) p.

Lemma in_prime_divisors_power_ge_1 :
    ∀ n p, p ∈ prime_divisors n → 1 ≤ pow_in_n n p.
Proof.
    intros. unfold pow_in_n.
    apply count_occ_In. 
    apply prime_divisors_decomp. assumption.
Qed.

Lemma prime_divisors_distinct : ∀ n, NoDup (prime_divisors n).
Proof.
    intros.
    unfold prime_divisors.
    apply NoDup_filter.
    apply seq_NoDup.
Qed.

(* Print count_occ.
Print NoDup. *)

Lemma fold_left_Natmul_accum :
  forall l n,
    fold_left Nat.mul l n = n * fold_left Nat.mul l 1.
Proof.
  induction l; intros. simpl. lia.
  simpl. rewrite IHl. symmetry. rewrite IHl. lia. 
Qed.

Lemma prod_empty :
  prod [] = 1.
Proof. easy. Qed.

Lemma prod_extend :
  forall l a, prod (a :: l) = a * prod l.
Proof.
  intros. simpl. rewrite fold_left_Natmul_accum. lia.
Qed.

Lemma prod_map1 :
  forall l, prod (map (λ _ : nat, 1) l) = 1.
Proof.
  induction l. easy.
  Local Opaque prod. simpl. rewrite prod_extend. rewrite IHl. lia.
Qed.

Lemma prod_augmented_not_in :
  forall l a f,
    a ∉ l ->
    NoDup l ->
    prod (map (fun x => if a =? x then a * f x else f x) l) = prod (map f l).
Proof.
  induction l; intros. easy.
  apply not_in_cons in H. destruct H as [Ha0 Hl].
  simpl. do 2 rewrite prod_extend. apply Nat.eqb_neq in Ha0. rewrite Ha0.
  inversion H0; subst. rewrite IHl by easy. lia.
Qed.

Lemma prod_augmented_in :
  forall l a f,
    a ∈ l ->
    NoDup l ->
    prod (map (fun x => if a =? x then a * f x else f x) l) = a * prod (map f l).
Proof.
  induction l; intros. inversion H.
  simpl. do 2 rewrite prod_extend.
  inversion H.
  - rewrite <- H1. inversion H0; subst. rewrite Nat.eqb_refl. 
    rewrite prod_augmented_not_in by easy. lia.
  - destruct (a0 =? a) eqn:E. apply Nat.eqb_eq in E. inversion H0; subst. easy.
    apply Nat.eqb_neq in E. inversion H0; subst. rewrite IHl by easy. lia.
Qed.

Theorem prod_by_occ :
    forall (l1 l2 : list nat)
        (Hocc : forall x, x ∈ l1 -> x ∈ l2)
        (Hdis : NoDup l2),
    prod l1 = 
    prod (map (fun x => x ^ (count_occ Nat.eq_dec l1 x)) l2).
Proof.
  induction l1; intros. simpl. rewrite prod_map1. easy.
  simpl. rewrite prod_extend.
  assert (a ∈ l2) by (apply Hocc; constructor; easy).
  specialize (prod_augmented_in l2 a (fun x : nat => x ^ (count_occ Nat.eq_dec l1 x)) H Hdis) as G. simpl in G.
  replace (map (λ x : nat, x ^ (if Nat.eq_dec a x then S (count_occ Nat.eq_dec l1 x) else count_occ Nat.eq_dec l1 x)) l2) with (map (λ x : nat, if a =? x then a * x ^ count_occ Nat.eq_dec l1 x else x ^ count_occ Nat.eq_dec l1 x) l2).
  2:{ apply map_ext. intro x.
      destruct (Nat.eq_dec a x). subst. rewrite Nat.eqb_refl. rewrite Nat.pow_succ_r'. easy.
      apply Nat.eqb_neq in n. rewrite n. easy.
  }
  rewrite G. rewrite IHl1 with (l2 := l2); try easy.
  intros. apply Hocc. right. easy.
Qed.

Lemma prod_le :
  forall {A} (l : list A) f1 f2,
    (forall a, a ∈ l -> 0 < f1 a <= f2 a) ->
    prod (map f1 l) <= prod (map f2 l).
Proof.
  intro A. induction l; intros. simpl. lia.
  simpl. do 2 rewrite prod_extend.
  assert (∀ a0 : A, a0 ∈ l → 0 < f1 a0 ≤ f2 a0) by (intros; apply H; constructor; easy).
  specialize (IHl _ _ H0).
  assert (0 < f1 a <= f2 a) by (apply H; constructor; easy).
  nia.
Qed.  

Lemma prod_const_f :
  forall {A} (l : list A) f c,
    (forall a, a ∈ l -> f a = c) ->
    prod (map f l) = c^(length l).
Proof.
  intro A. induction l; intros. simpl. apply prod_empty.
  simpl. rewrite prod_extend. rewrite IHl with (c := c).
  rewrite H. easy.
  constructor; easy.
  intros. apply H. constructor; easy.
Qed.

Local Transparent prod.

Theorem prime_divisor_pow_prod :
    ∀ n, n ≠ 0 → prod (map (fun x => x ^ (pow_in_n n x)) (prime_divisors n)) = n.
Proof.
    intros. rewrite <- prime_decomp_prod; auto.
    unfold pow_in_n. symmetry. apply prod_by_occ.
    apply prime_divisors_decomp. apply prime_divisors_distinct.
Qed.

Inductive pairwise_coprime : list nat -> Prop :=
    | PCnil : pairwise_coprime nil
    | PCcons (x : nat) (l : list nat)
        (Hxlc : ∀ y, y ∈ l → Nat.gcd x y = 1)
        (Hlpc : pairwise_coprime l) : pairwise_coprime (x :: l).

Theorem φ_prod_pairwise_coprime : 
    ∀ (l : list nat) (Hpc : pairwise_coprime l),
        φ (prod l) = prod (map φ l).
Proof.
    intros. induction Hpc.
    - simpl. reflexivity. (* φ 1 = 1 *)
    - simpl in *. repeat rewrite Nat.add_0_r. 
      rewrite fold_left_mul_from_1.
      rewrite fold_left_mul_from_1 with (φ x) _.
      rewrite φ_multiplicative. rewrite IHHpc. reflexivity.
      clear - Hpc Hxlc.
      induction l.
      + simpl. apply Nat.gcd_1_r.
      + simpl. rewrite plus_0_r. replace a with (1 * a) by flia.
        rewrite <- List_fold_left_mul_assoc.
        rewrite Nat_gcd_1_mul_r. flia.
        inversion Hpc. apply IHl.
        --  intros. apply Hxlc. now right.
        --  assumption.
        --  apply Hxlc. now left.
Qed. 

Lemma prime_divisors_aux :
    ∀ n a, a ∈ prime_divisors n ->
        prime a ∧ pow_in_n n a > 0.
Proof.
    intros. split.
    apply in_prime_decomp_is_prime with n.
    apply prime_divisors_decomp. assumption.
    apply in_prime_divisors_power_ge_1 in H.
    flia H.
Qed.

Lemma Nat_gcd_1_pow_l :
  forall pa a b,
    Nat.gcd a b = 1 ->
    Nat.gcd (a^pa) b = 1.
Proof.
  induction pa; intros. easy.
  simpl. apply Nat_gcd_1_mul_l. easy. apply IHpa. easy.
Qed.

Lemma Nat_gcd_1_pow :
  forall a b pa pb,
    Nat.gcd a b = 1 ->
    Nat.gcd (a^pa) (b^pb) = 1.
Proof.
  intros. specialize (Nat_gcd_1_pow_l pa a b H) as G. rewrite Nat.gcd_comm in G.
  rewrite Nat.gcd_comm. apply Nat_gcd_1_pow_l. easy.
Qed.

Lemma diff_prime_power_coprime :
  ∀ x y px py,
    x <> y -> prime x → prime y →
    Nat.gcd (x ^ px) (y ^ py) = 1.
Proof.
  intros. apply Nat_gcd_1_pow. apply eq_primes_gcd_1; easy.
Qed.

Lemma prime_power_pairwise_coprime :
    ∀ l (f : nat → nat) (HND : NoDup l) (Hprime : ∀ x, x ∈ l → prime x),
        pairwise_coprime (map (λ x, x ^ f x) l).
Proof.
    intros. induction l.
    - simpl. constructor.
    - simpl. constructor.
      + intros. rewrite in_map_iff in H.
        destruct H as (x & H1 & H2). subst.
        apply diff_prime_power_coprime.
        inversion HND; subst.
        destruct (x =? a) eqn:E. apply Nat.eqb_eq in E. subst. easy.
        apply Nat.eqb_neq in E. lia.
        apply Hprime. now left.
        apply Hprime. now right.
      + apply IHl. inversion HND. assumption.
        intros. apply Hprime. now right.
Qed.

Theorem φ_prime_divisors_power :
    ∀ n, n ≠ 0 ->
        φ n = prod (map (fun x => x ^ (pow_in_n n x - 1) * (x - 1)) (prime_divisors n)).
Proof.
    intros.
    rewrite <- (prime_divisor_pow_prod n) at 1 by flia H.
    rewrite φ_prod_pairwise_coprime.
    rewrite map_map.
    rewrite map_ext_in with _ _ _ (λ x : nat, x ^ (pow_in_n n x - 1) * (x - 1)) _. reflexivity.
    - intros.
      apply prime_divisors_aux in H0 as (H0 & H1).
      assert (pow_in_n n a ≠ 0) by flia H1.
      rewrite prime_pow_φ by assumption.
      rewrite prime_φ by assumption. reflexivity.
    - apply prime_power_pairwise_coprime.
      apply prime_divisors_distinct.
      intros. apply prime_divisors_decomp in H0.
      apply in_prime_decomp_is_prime with n. assumption.
Qed.
