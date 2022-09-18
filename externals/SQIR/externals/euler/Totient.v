(* Correct Definition of φ *)

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Misc Primes.
Require Import PTotient Primisc.


Definition coprimes n := filter (λ d, Nat.gcd n d =? 1) (seq 1 n).
Definition φ n := length (coprimes n).

Lemma coprimes_coprimes' :
    ∀ n, 2 ≤ n → coprimes n = coprimes' n.
Proof.
    intros. unfold coprimes, coprimes'.
    replace n with ((n - 1) + 1) at 1 by flia H.
    rewrite seq_app.
    replace (1 + (n - 1)) with n at 1 by flia H.
    rewrite filter_app. simpl.
    destruct (Nat.eqb_spec (Nat.gcd n n) 1).
    - rewrite Nat.gcd_diag in *. flia H e.
    - rewrite app_nil_r. reflexivity.
Qed.

Lemma φ_φ' :
    ∀ n, 2 ≤ n → φ n = φ' n.
Proof.
    intros. unfold φ, φ'.
    rewrite coprimes_coprimes' by flia H.
    reflexivity.
Qed.

Theorem prime_φ :
    ∀ p, prime p → φ p = p - 1.
Proof.
    intros.
    rewrite <- prime_φ' by assumption.
    apply φ_φ'. apply prime_ge_2. assumption.
Qed.

Theorem φ_multiplicative :
    ∀ m n, 
        Nat.gcd m n = 1 →
        φ (m * n) = φ m * φ n.
Proof.
    intros.
    destruct (Nat.leb_spec 2 m).
    destruct (Nat.leb_spec 2 n).
    -   assert (2 ≤ m * n) by flia H0 H1.
        repeat rewrite φ_φ' by assumption.
        rewrite φ'_multiplicative by assumption.
        reflexivity.
    -   destruct n. rewrite Nat.gcd_0_r in H.
        flia H H0. replace n with 0 by flia H1.
        cbn. rewrite mult_1_r. rewrite mult_1_r.
        reflexivity.
    -   destruct m. rewrite Nat.gcd_0_l in H.
        rewrite mult_0_l. cbn. reflexivity.
        replace m with 0 by flia H0.
        rewrite mult_1_l. cbn. rewrite plus_0_r.
        reflexivity.
Qed.
        
Theorem prime_pow_φ :
    ∀ p, prime p →
        ∀ k, k ≠ 0 → φ (p ^ k) = p ^ (k - 1) * φ p.
Proof.
    intros.
    assert (2 ≤ p ^ k).
    {
        apply le_trans with p.
        apply prime_ge_2.
        assumption.
        rewrite <- Nat.pow_1_r at 1.
        apply Nat.pow_le_mono_r.
        apply prime_ge_2 in H. flia H.
        flia H0.
    }
    rewrite φ_φ' by assumption.
    rewrite prime_pow_φ' by assumption.
    rewrite φ_φ'. reflexivity.
    apply prime_ge_2. assumption.
Qed.


