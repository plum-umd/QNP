Require Import Primes Arith Psatz List Nat Misc Primisc Prod Bool.

Local Open Scope nat_scope.

(* TODO: Develop this, use Prime as main definition of primality.
   Prime shouldn't be defined in terms of a prima      lity checker. -RNR *)

Definition Prime (p : nat) := p > 1 /\ forall a, Nat.divide a p -> a = 1 \/ a = p.

Definition Composite (n : nat) := exists a b, a > 1 /\ b > 1 /\ a * b = n.

Lemma NatOdd2x :
  forall x, ~ Nat.Odd (x * 2).
Proof.
  induction x. simpl. intro. inversion H. lia.
  intro. simpl in *. rewrite Nat.Odd_succ_succ in H. easy.
Qed.

Definition coprime (a b : nat) : Prop := Nat.gcd a b = 1%nat.

Lemma pow_coprime :
  forall a p k,
    Nat.gcd a p = 1 -> Nat.gcd a (p^k) = 1.
Proof.
  intros. induction k. simpl. apply Nat.gcd_1_r.
  simpl. apply Nat_gcd_1_mul_r; easy.
Qed.

Lemma coprime_list_prod :
  forall p l f,
    (forall q, In q l -> Nat.gcd p q = 1) ->
    Nat.gcd p (fold_left Nat.mul (map (fun x : nat => x ^ f x) l) 1) = 1.
Proof.
  intros. induction l.
  simpl. apply Nat.gcd_1_r.
  simpl. replace (a ^ f a + 0) with (1 * (a ^ f a)) by lia.
  rewrite <- Misc.List_fold_left_mul_assoc.
  apply Misc.Nat_gcd_1_mul_r.
  apply IHl. intros. apply H. apply in_cons. easy.
  apply pow_coprime. apply H. constructor. easy.
Qed.

(* A bit of useful reflection from Software Foundations Vol 3 *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Lemma simplify_primality : forall N,
    ~ (prime N) -> Nat.Odd N -> (forall p k, prime p -> N <> p ^ k) ->
    (exists p k q, (k <> 0) /\ prime p /\ (p > 2) /\ (q > 2) /\ coprime (p ^ k) q /\ N = p ^ k * q)%nat.
Proof.
  intros.
  assert (GN : N > 1).
  { destruct H0. specialize (H1 2 0 eq_refl). simpl in *. lia. }  
  destruct (prime_divisors N) as [| p [| q l]] eqn:E.
  - apply Primisc.prime_divisors_nil_iff in E. lia.
  - assert (Hp: In p (prime_divisors N)) by (rewrite E; constructor; easy).
    apply Prod.prime_divisors_aux in Hp. destruct Hp as [Hp Hpn].
    assert (HN0: N <> 0) by lia.
    specialize (Prod.prime_divisor_pow_prod N HN0) as G.
    rewrite E in G. simpl in G.    
    specialize (H1 p (Prod.pow_in_n N p) Hp).
    remember (p ^ Prod.pow_in_n N p) as pk.
    rewrite <- G in H1. lia.
  - assert (Hp: In p (prime_divisors N)) by (rewrite E; constructor; easy).
    assert (Hq: In q (prime_divisors N)) by (rewrite E; constructor; constructor; easy).
    assert (Hp': In p (prime_decomp N)) by (apply Primisc.prime_divisors_decomp; easy).
    assert (Hq': In q (prime_decomp N)) by (apply Primisc.prime_divisors_decomp; easy).
    apply in_prime_decomp_divide in Hp'. apply in_prime_decomp_divide in Hq'.
    apply Prod.prime_divisors_aux in Hp. destruct Hp as [Hp Hpn].
    apply Prod.prime_divisors_aux in Hq. destruct Hq as [Hq Hqn].
    remember (q :: l) as lq.
    assert (HN0: N <> 0) by lia.
    specialize (Prod.prime_divisor_pow_prod N HN0) as G.
    rewrite E in G. simpl in G.
    replace (p ^ Prod.pow_in_n N p + 0) with (1 * (p ^ Prod.pow_in_n N p)) in G by lia.
    rewrite <- Misc.List_fold_left_mul_assoc in G.
    remember (Prod.prod (map (fun x : nat => x ^ Prod.pow_in_n N x) lq)) as Plq.
    exists p, (Prod.pow_in_n N p), Plq.
    split. lia. split. easy.
    split. assert (2 <= p) by (apply prime_ge_2; easy).
    bdestruct (2 =? p). rewrite <- H3 in Hp'. destruct Hp'. rewrite H4 in H0. apply NatOdd2x in H0. easy. lia.
    assert (HeqPlq' := HeqPlq).
    simpl in HeqPlq'. rewrite <- HeqPlq' in G.
    rewrite Heqlq in HeqPlq.
    rewrite map_cons, Prod.prod_extend in HeqPlq.
    split.
    bdestruct (Plq =? 0). rewrite H2 in G. lia.
    bdestruct (Plq =? 1).
    assert (2 <= q) by (apply prime_ge_2; easy).
    assert (Prod.pow_in_n N q < q ^ Prod.pow_in_n N q) by (apply Nat.pow_gt_lin_r; lia).
    assert (2 <= q ^ Prod.pow_in_n N q) by lia.
    destruct (Prod.prod (map (fun x : nat => x ^ Prod.pow_in_n N x) l)); lia.
    bdestruct (Plq =? 2). rewrite H4 in G. rewrite <- G in H0. rewrite Nat.mul_comm in H0. apply NatOdd2x in H0. easy.
    lia.
    split. unfold coprime. apply Prod.Nat_gcd_1_pow_l.
    rewrite HeqPlq'. apply coprime_list_prod.
    intros. assert (In q0 (prime_divisors N)) by (rewrite E; apply in_cons; easy).
    assert (p <> q0).
    { specialize (Prod.prime_divisors_distinct N) as T. rewrite E in T.
      inversion T. intro. subst. easy.
    } 
    apply Prod.prime_divisors_aux in H3. destruct H3 as [Hq0 Hq0n].
    apply eq_primes_gcd_1; easy.
    lia.
Qed.

Theorem Prime_prime :
  forall n, Prime n <-> prime n.
Proof.
  intros. split; intro.
  - destruct H.
    unfold prime, is_prime.
    do 2 (destruct n; try lia).
    apply prev_not_div_prime_test_true; try lia.
    intros. intro. apply Nat.mod_divide in H2; try lia.
    specialize (H0 e H2).
    lia.
  - unfold Prime.
    assert (2 <= n) by (apply prime_ge_2; easy).
    split. lia.
    intros.
    apply prime_only_divisors; easy.
Qed.
