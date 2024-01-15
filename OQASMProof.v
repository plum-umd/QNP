Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
Require Import OQASM.
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

Lemma mapsto_always_same : forall k v1 v2 s,
           @Env.MapsTo (type) k v1 s ->
            @Env.MapsTo (type) k v2 s -> 
                       v1 = v2.
Proof.
     intros.
     apply Env.find_1 in H.
     apply Env.find_1 in H0.
     rewrite H in H0.
     injection H0.
     easy.
Qed.

Lemma find_add : forall k v m,
        @Env.find (type) k (Env.add k v m) = Some v.
Proof.
      intros.
      apply Env.find_1.
      apply Env.add_1.
      easy.
Qed.

Lemma mapsto_add1 : forall k v1 v2 s,
        @Env.MapsTo (type) k v1 (Env.add k v2 s) -> v1 = v2.
Proof.
      intros.
      apply Env.find_1 in H.
      rewrite find_add in H.
      inversion H.
      reflexivity.
Qed.

Lemma mapsto_equal : forall k v s1 s2,
   @Env.MapsTo type k v s1 ->
   Env.Equal s1 s2 ->
   Env.MapsTo k v s2.
Proof.
      intros.
      unfold Env.Equal in H0.
      apply Env.find_2. rewrite <- H0.
      apply Env.find_1.
      assumption.
Qed.


Lemma map_find_add : forall x v env, @Env.find (type) x (Env.add x v env) = Some v.
Proof.
  intros.
  apply Env.find_1.
  apply Env.add_1. easy.
Qed.

Lemma map_find_neq : forall x y v env, x <> y -> @Env.find (type) x (Env.add y v env) = Env.find x env.
Proof.
  intros.
  destruct (Env.find (elt:=type) x env) eqn:eq1.
  apply Env.find_1. apply Env.add_2. lia. 
  apply Env.find_2 in eq1. easy.
  destruct (Env.find (elt:=type) x (Env.add y v env)) eqn:eq2.
  apply Env.find_2 in eq2. apply Env.add_3 in eq2.
  apply Env.find_1 in eq2. rewrite eq1 in eq2. inv eq2. lia.
  easy.
Qed.


(* Helper theorems for fbrev and rotation. *)
Lemma fbrev_1_same {A}: forall f, @fbrev A 1 f = f.
Proof.
  intros.
  unfold fbrev.
  apply functional_extensionality. intros.
  bdestruct (x<?1).
  assert (1 - 1 - x = x) by lia.
  rewrite H0. easy. easy. 
Qed.


Lemma rotate_twice_same_1 : forall r, (rotate (rotate r 1) 1) = r.
Proof.
  intros. unfold rotate.
  unfold addto.
  apply functional_extensionality. intros.
  bdestruct (x <? 1).
  assert ( x = 0) by lia. subst.
  repeat rewrite fbrev_1_same.
  destruct (r 0) eqn:eq1.
  specialize (cut_n_1_1 r eq1) as eq2.
  rewrite eq2.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_mod.
  assert (((1 + 1) mod 2 ^ 1) = 0).
  assert ((1 + 1) = 2) by lia. rewrite H0.
  rewrite Nat.pow_1_r. rewrite Nat.mod_same. easy. lia.
  rewrite H0.
  rewrite cut_n_if_cut.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r. rewrite Nat.mod_small by lia.
  rewrite sumfb_correct_carry0.
  rewrite plus_0_l. 
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_small by lia.
  unfold nat2fb. simpl. easy.
  rewrite (cut_n_1_0 r eq1).
  rewrite sumfb_correct_carry0.
  rewrite plus_0_l.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r. rewrite Nat.mod_small by lia.
  rewrite cut_n_if_cut.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r. rewrite Nat.mod_small by lia.
  rewrite sumfb_correct_carry0.
  assert ((1 + 1) = 2) by lia. rewrite H0.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_same by lia.
  unfold nat2fb. easy.
  easy.
Qed.

Lemma rotate_1_0: forall r, r 0 = false -> rotate r 1 0 = true.
Proof.
  unfold rotate, addto.
  intros.
  bdestruct (0 <? 1).
  repeat rewrite fbrev_1_same.
  rewrite (cut_n_1_0 r H). 
  rewrite sumfb_correct_carry0.
  rewrite plus_0_l. 
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_small by lia. easy. lia.
Qed.

Lemma rotate_1_1: forall r, r 0 = true -> rotate r 1 0 = false.
Proof.
  unfold rotate, addto.
  intros.
  bdestruct (0 <? 1).
  repeat rewrite fbrev_1_same.
  rewrite (cut_n_1_1 r H). 
  rewrite sumfb_correct_carry0.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_same by lia. easy. lia.
Qed.

(*
Lemma hexchange_twice_same :
  forall v1 v2, hexchange (hexchange v1 v2) v2 = v1.
Proof.
  intros.
  unfold hexchange.
  destruct v1 eqn:eq1. easy.
  destruct v2 eqn:eq2. easy.
  destruct (eqb b0 b3) eqn:eq3. easy.
  assert ((¬ (¬ b2)) = b2) by btauto. rewrite H0. easy.
  easy. easy.
Qed.


Lemma h_case_twice_same : 
   forall t v, right_mode_val t v -> h_case (h_case v) = v.
Proof.
  intros. unfold h_case.
  destruct v.
  destruct (r 0) eqn:eq1.
  destruct b.
  rewrite rotate_twice_same_1. easy.
  rewrite rotate_twice_same_1. easy.
  destruct b. simpl. easy. simpl. easy.
  inv H0.
  destruct b1.
  destruct b2. rewrite H3. simpl. easy.
  rewrite H3. simpl. easy.
  destruct b2.
  rewrite (rotate_1_0 r H3).
  rewrite rotate_twice_same_1. easy.
  rewrite (rotate_1_0 r H3).
  rewrite rotate_twice_same_1. easy.
  easy.
Qed.
*)
Lemma get_cua_eq : forall f x v, nor_mode f x -> get_cua ((f[x |-> put_cu (f x) v]) x) = v.
Proof.
  intros.
  unfold get_cua.
  rewrite eupdate_index_eq.
  unfold put_cu.
  unfold nor_mode in H.
  destruct (f x). easy. inv H.
Qed.

Lemma type_nor_mode :  forall f aenv env p, 
    Env.MapsTo (fst p) Nor env -> snd p < aenv (fst p) -> right_mode_env aenv env f -> nor_mode f p.
Proof.
 intros. unfold right_mode_env in *.
 apply (H1 Nor) in H0 ; try easy.
 inv H0. unfold nor_mode.
 rewrite <- H2. easy.
Qed.


Lemma type_nor_modes :  forall f aenv env x, 
    Env.MapsTo x Nor env -> right_mode_env aenv env f -> nor_modes f x (aenv x).
Proof.
 intros. unfold right_mode_env in *.
 unfold nor_modes. intros.
 specialize (H0 Nor (x,i)).
 simpl in H0. apply H0 in H1; try easy.
 inv H1. unfold nor_mode.
 assert ((@pair var nat x i) = (@pair Env.key nat x i)) by easy.
 rewrite H1 in *.
 rewrite <- H2. easy.
Qed.

Lemma nor_mode_nval : forall f x, nor_mode f x -> (exists r, f x = nval true r \/ f x = nval false r).
Proof.
  intros. unfold nor_mode in *. destruct (f x); inv H.
  exists r.
  destruct b. left. easy. right. easy.
Qed.

Lemma neq_sym {A} : forall (x y: A), x <> y -> y <> x.
Proof.
 intros. intros R.
 subst. contradiction.
Qed.

Lemma nor_mode_up : forall f x y v, x <> y -> nor_mode f x -> nor_mode (f[y |-> v]) x.
Proof.
  intros. unfold nor_mode in *.
  assert ((f [y |-> v]) x = (f x)).
  rewrite eupdate_index_neq. reflexivity. apply neq_sym. assumption.
  rewrite H1.
  destruct (f x); inv H0. easy.
Qed.



Lemma get_cus_cua : forall n f x m, m < n -> get_cus n f x m = get_cua (f (x,m)).
Proof.
  intros.
  unfold get_cus,get_cua.
  bdestruct (m <? n).
  destruct (f (x,n)). easy. easy.
  lia.
Qed.

Definition put_cus (f:posi -> val) (x:var) (g:nat -> bool) (n:nat) : (posi -> val) :=
     fun a => if fst a =? x then if snd a <? n then put_cu (f a) (g (snd a)) else f a else f a.

Lemma get_r_put_same : forall (f:posi -> val) x y g n i,
      get_r (put_cus f x g n (y,i)) = get_r (f (y,i)).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? x).
 bdestruct (i <? n).
 unfold put_cu.
 destruct (f (y, i)).
 unfold get_r. easy. easy. easy. easy.
Qed.

Lemma get_r_put_cu_same : forall (f:posi -> val) p v,
      nor_mode f p ->
      get_r (put_cu (f p) v) = get_r (f p).
Proof.
 intros.
 unfold put_cu,nor_mode in *.
 destruct (f p). easy. easy.
Qed.



Lemma cus_get_neq : forall (f:posi -> val) (x y :var) g n i, 
              x <> y -> get_cua ((put_cus f y g n) (x,i)) = get_cua (f (x,i)).
Proof.
 intros.
 unfold get_cua.
 unfold put_cus.
 simpl.
 bdestruct (x =? y).
 lia. easy.
Qed.

Lemma put_cus_out : forall (f:posi -> val) (x y :var) g n i, 
              n <= i -> ((put_cus f y g n) (x,i)) = (f (x,i)).
Proof. 
  intros.
  unfold put_cus.
  simpl.
  bdestruct (x =? y).
  bdestruct (i <? n). lia.
  easy. easy.
Qed.

Lemma nor_mode_cus_eq: forall f x g n y i, 
       nor_mode f (y,i) -> nor_mode (put_cus f x g n) (y,i).
Proof.
  intros. unfold nor_mode in *.
  unfold put_cus.
  simpl.
  bdestruct (y =? x).
  bdestruct (i <? n).
  destruct (f (y, i)).
  unfold put_cu. easy.
  inv H.
  apply H. apply H.
Qed.

Lemma cus_get_eq : forall (f:posi -> val) (x :var) g n i, 
              i < n -> nor_modes f x n -> get_cua ((put_cus f x g n) (x,i)) = g i.
Proof.
 intros.
 unfold get_cua.
 unfold put_cus.
 simpl.
 bdestruct (x =? x).
 bdestruct (i <? n).
 unfold put_cu.
 specialize (H0 i H2). unfold nor_mode in *.
 destruct (f (x, i)) eqn:eq1. easy.
 inv H0.
 lia. lia.
Qed.

Lemma put_cus_eq : forall (f:posi -> val) (x:var) g n i, 
          i < n -> (put_cus f x g n) (x,i) = put_cu (f (x,i)) (g i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (x =? x).
 bdestruct (i <? n). easy. lia. lia.
Qed.

Lemma put_cus_neq : forall (f:posi -> val) (x y:var) g n i, 
              x <> y -> (put_cus f x g n) (y,i) = f (y,i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? x). lia. easy.
Qed.

Lemma put_cus_neq_1 : forall (f:posi -> val) (x:var) g n c, 
              x <> fst c -> (put_cus f x g n) c = f c.
Proof.
 intros.
 destruct c. apply put_cus_neq.
 simpl in H. assumption.
Qed.

Lemma put_cus_neq_2 : forall (f:posi -> val) (x y:var) g n i, 
           n <= i -> (put_cus f x g n) (y,i) = f (y,i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? x).
 bdestruct (i <? n). lia. easy.
 easy.
Qed.

Lemma put_cu_cus : forall (f:posi -> val) x y g i n v, put_cu (put_cus f y g n (x,i)) v = put_cu (f (x,i)) v.
Proof.
  intros.
  unfold put_cus,put_cu.
  simpl.
  bdestruct (x =? y).
  bdestruct (i <? n).
  destruct (f (x,i)). easy. easy. easy. easy.
Qed.

Lemma nor_mode_up_1 : forall f x v, nor_mode f x -> nor_mode (f[x |-> put_cu (f x) v]) x.
Proof.
  intros.
  unfold nor_mode in *.
  rewrite eupdate_index_eq.
  unfold put_cu.
  destruct (f x).
  easy. inv H.
Qed.


Lemma nor_mode_ups : forall f f' x v, f x = f' x -> nor_mode f x ->
                                    nor_mode (f[x |-> put_cu (f' x) v]) x.
Proof.
  intros. unfold nor_mode in *.
  rewrite eupdate_index_eq.
  unfold put_cu. rewrite <- H.
  destruct (f x); inv H0. easy.
Qed.

Lemma nor_mode_get : forall f x, nor_mode f x -> (exists b, get_cua (f x) = b).
Proof.
  intros. unfold nor_mode in *. destruct (f x); inv H.
  exists b. unfold get_cua. reflexivity.
Qed.

Lemma put_get_cus_eq :
   forall f x n, nor_modes f x n -> (put_cus f x (get_cus n f x) n) = f.
Proof.
  intros.
  unfold put_cus,get_cus,put_cu.
  apply functional_extensionality. intros.
  destruct x0. simpl.
  bdestruct (v =? x). bdestruct (n0 <? n).
  subst.
  unfold nor_modes in H.
  specialize (H n0 H1) as eq1. unfold nor_mode in eq1.
  destruct (f (x,n0)). easy. inv eq1. 
  easy. easy.
Qed.

Lemma get_cus_put_eq :
   forall f x v n, v < 2^n -> nor_modes f x n -> get_cus n (put_cus f x (nat2fb v) n) x = (nat2fb v).
Proof.
  intros.
  unfold get_cus.
  apply functional_extensionality. intros.
  bdestruct (x0 <? n).
  simpl.
  unfold nor_modes in H.
  assert (nor_mode (put_cus f x (nat2fb v) n) (x, x0)).
  apply nor_mode_cus_eq. apply H0. easy.
  unfold nor_mode in H2.
  destruct (put_cus f x ((nat2fb v)) n (x, x0)) eqn:eq2.
  unfold put_cus in eq2. simpl in eq2.
  bdestruct (x =? x).
  bdestruct (x0 <? n).
  unfold put_cu in eq2.
  assert (nor_mode f (x,x0)).
  apply H0. easy.
  unfold nor_mode in H5.
  destruct (f (x, x0)). inv eq2. easy. inv H5. lia. lia.
  inv H2.
  unfold allfalse.
  rewrite nat2fb_bound with (n := n); try easy.
Qed.

Lemma put_cus_same : forall f x g n, nor_modes f x n 
               -> get_cus n f x = g -> put_cus f x g n = f.
Proof.
  intros.
  rewrite <- H0. 
  rewrite put_get_cus_eq. easy. easy.
Qed.

Lemma get_cus_put_neq :
   forall f x y g n, x <> y -> get_cus n (put_cus f x g n) y = get_cus n f y.
Proof.
  intros. unfold get_cus,put_cus.
  apply functional_extensionality. intros.
  simpl.
  bdestruct ( y =? x). lia.
  destruct (f (y, x0)). easy. easy. 
Qed.

Lemma get_put_cus_cut_n : forall n f x g, nor_modes f x n
             -> (get_cus n (put_cus f x g n) x) = cut_n g n.
Proof.
  intros. unfold get_cus,put_cus,cut_n.
  apply functional_extensionality. intros.
  bdestruct (x0 <? n). simpl.
  bdestruct (x =? x).
  bdestruct (x0 <? n).
  unfold put_cu.
  unfold nor_modes in H0.
  specialize (H x0 H2). unfold nor_mode in H.
  destruct (f (x,x0)). easy. lia. lia.
  lia. easy.
Qed.

Definition get_cu (v : val) :=
    match v with nval b r => Some b 
                 | _ => None
    end.

Lemma put_get_cu : forall f x, nor_mode f x -> put_cu (f x) (get_cua (f x)) = f x.
Proof.
 intros. unfold put_cu, get_cua.
 unfold nor_mode in H. destruct (f x); inv H.
 reflexivity.
Qed.

Lemma get_put_cu : forall f x v, nor_mode f x -> get_cua (put_cu (f x) v) = v.
Proof.
 intros. unfold put_cu, get_cua.
 unfold nor_mode in H. destruct (f x); inv H.
 reflexivity.
Qed.

Lemma get_cua_t : forall b r, get_cua (nval b r) = b.
Proof.
 intros. unfold get_cua. reflexivity.
Qed.

(* Proofs of types and syntax. *)
Ltac nor_sym := try (apply neq_sym; assumption) ; try assumption.


Lemma iner_neq : forall (x y:var) (a b:nat), x <> y -> (x,a) <> (y,b).
Proof.
  intros. intros R.
  inv R. contradiction.
Qed.

Lemma iner_neq_1 : forall (x:var) (c:posi) a, x <> fst c -> (x,a) <> c.
Proof.
  intros. intros R.
  destruct c.
  inv R. contradiction.
Qed.

Lemma iner_neq_2 : forall (x:var) (c:posi) a, x <> fst c -> c <> (x,a).
Proof.
  intros. intros R.
  destruct c.
  inv R. contradiction.
Qed.

Ltac tuple_eq := intros R; inv R; lia.

Ltac iner_p := try nor_sym; try tuple_eq ; try (apply iner_neq ; assumption)
           ; try (apply iner_neq_1 ; assumption) ; try (apply iner_neq_2 ; assumption).

Lemma assign_r_right_mode : forall n i size f x r, i < n <= size -> 
       (forall i, i < size -> right_mode_val Nor (f (x,i))) ->
       right_mode_val (Phi size) (assign_r f x r n (x,i)).
Proof.
  induction n; intros; simpl. inv H. inv H1.
  bdestruct (i =? n).
  subst. rewrite eupdate_index_eq.
  unfold up_qft.
  specialize (H0 n).
  assert (n < size) by lia. apply H0 in H1. inv H1.
  constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy.
Qed.

Lemma assign_h_right_mode : forall i b j size f x,  b <= j < size -> j < b + i ->
       (forall i, b <= i < size -> right_mode_val Nor (f (x,i))) ->
       right_mode_val (Phi b) (assign_h f x b i (x,j)).
Proof.
  induction i; intros; simpl. lia.
  bdestruct (j =? b + i).
  subst.
  rewrite eupdate_index_eq. unfold up_h.
  destruct (f (x, b + i)) eqn:eq1. destruct b0.
  constructor. constructor.
  specialize (H1 (b+i) H). inv H1. rewrite eq1 in H2. inv H2.
  rewrite eupdate_index_neq by iner_p.
  apply IHi with (size := size). lia. lia. easy.
Qed.

Lemma assign_r_right_mode_out : forall n t f x r v i, v <> x -> 
        right_mode_val t (f (v,i)) ->
       right_mode_val t (assign_r f x r n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy. 
Qed.

Lemma assign_h_right_mode_out : forall n t f x r v i, v <> x -> 
        right_mode_val t (f (v,i)) ->
       right_mode_val t (assign_h f x r n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy. 
Qed.

Lemma assign_h_r_right_mode : forall i b j size f x,  b <= j < size -> j < b + i ->
       (forall i, b <= i < size -> right_mode_val (Phi b) (f (x,i))) ->
       right_mode_val Nor (assign_h_r f x b i (x,j)).
Proof.
  induction i; intros; simpl. lia.
  bdestruct (j =? b + i).
  subst.
  rewrite eupdate_index_eq. unfold up_h.
  destruct (f (x, b + i)) eqn:eq1. destruct b0.
  specialize (H1 (b+i) H). inv H1. rewrite eq1 in H4. inv H4.
  specialize (H1 (b+i) H). inv H1. rewrite eq1 in H4. inv H4.
  constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHi with (size := size). lia. lia. easy.
Qed.

Lemma assign_h_r_right_mode_out : forall n t f x r v i, v <> x -> 
        right_mode_val t (f (v,i)) ->
       right_mode_val t (assign_h_r f x r n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy. 
Qed.

Lemma assign_seq_right_mode : forall n i f x r, i < n -> 
       right_mode_val Nor (assign_seq f x r n (x,i)).
Proof.
  induction n; intros; simpl.
  inv H.
  bdestruct (i =? n).
  subst. rewrite eupdate_index_eq.
  constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia.
Qed.

Lemma assign_seq_right_mode_out : forall n t f x r v i, v <> x -> 
        right_mode_val t (f (v,i)) ->
       right_mode_val t (assign_seq f x r n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy.
Qed.

(*
Lemma h_sem_right_mode_nor : forall n i f x, i < n -> 
       right_mode_val Nor (f (x,i)) ->
       right_mode_val Had (h_sem f x n (x,i)).
Proof.
  induction n; intros; simpl. lia.
  inv H1.
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq.
  rewrite <- H2. unfold h_case. destruct (r 0) eqn:eq1; constructor.
  rewrite rotate_1_1; try easy. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. rewrite <- H2. constructor.
Qed.


Lemma h_sem_right_mode_had : forall n i f x, i < n -> 
       right_mode_val Had (f (x,i)) ->
       right_mode_val Nor (h_sem f x n (x,i)).
Proof.
  induction n; intros; simpl. lia.
  inv H1.
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq.
  rewrite <- H2. unfold h_case.
  destruct b1. destruct b2; constructor.
  destruct b2; constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. rewrite <- H2. constructor. easy.
Qed.

Lemma h_sem_right_mode_out : forall n t f x v i, v <> x -> 
       right_mode_val t (f (v,i)) ->
       right_mode_val t(h_sem f x n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy.
Qed.
*)


(* Defining matching shifting stack. *)

Lemma exp_neu_t_prop : forall p x l l', exp_neu_l x l p l' -> exp_neu_prop l -> exp_neu_prop l'.
Proof.
 induction p; intros; try easy.
 1-7:inv H; easy.
 unfold exp_neu_prop in *.
 intros. inv H.
 destruct l'. simpl in *. lia.
 destruct i. simpl in *.
 destruct l'. easy.
 specialize (H0 1 a).
 assert (1 + 1 < S (S (length (s0 :: l')))) by lia.
 apply H0 in H. simpl in *. easy.
 simpl in *. easy.
 specialize (H0 (S (S i)) a).
 assert (S (S i) + 1 < length (Rs :: s :: l')).
 simpl in *. lia.
 apply H0 in H.
 simpl in *. easy.
 simpl in *. easy.
 unfold fst_not_opp in H5. destruct l. simpl in *. lia.
 destruct i. simpl in *. inv H2.
 unfold opp_ls in *. intros R. inv R. easy.
 specialize (H0 i a).
 assert (i + 1 < length (s :: l)). simpl in *. lia.
 apply H0 in H. simpl in *. easy. simpl in *. easy.
 apply H0; try easy.
 unfold exp_neu_prop in *.
 intros. inv H.
 destruct l'. simpl in *. lia.
 destruct i. simpl in *.
 destruct l'. easy.
 specialize (H0 1 a).
 assert (1 + 1 < S (S (length (s0 :: l')))) by lia.
 apply H0 in H. simpl in *. easy.
 simpl in *. easy.
 specialize (H0 (S (S i)) a).
 assert (S (S i) + 1 < length (Ls :: s :: l')).
 simpl in *. lia.
 apply H0 in H.
 simpl in *. easy.
 simpl in *. easy.
 unfold fst_not_opp in *. destruct l. simpl in *. lia.
 destruct i. simpl in *. inv H2.
 unfold opp_ls. intros R. inv R. easy.
 specialize (H0 i a).
 assert (i + 1 < length (s :: l)). simpl in *. lia.
 apply H0 in H. simpl in *. easy. simpl in *. easy.
 apply H0; try easy.
 unfold exp_neu_prop in *.
 intros. inv H.
 destruct i. simpl in *.
 destruct l'. easy.
 specialize (H0 1 a).
 assert (1 + 1 < S (length (s :: l'))) by lia.
 apply H0 in H. simpl in *. easy.
 simpl in *. easy.
 specialize (H0 (S (S i)) a).
 assert (S (S i) + 1 < length (Re :: l')).
 simpl in *. lia.
 apply H0 in H.
 simpl in *. easy.
 simpl in *. easy.
 unfold fst_not_opp in *. destruct l. simpl in *. lia.
 destruct i. simpl in *. inv H2.
 unfold opp_ls. intros R. inv R. easy.
 specialize (H0 i a).
 assert (i + 1 < length (s :: l)). simpl in *. lia.
 apply H0 in H. simpl in *. easy. simpl in *. easy.
 apply H0; try easy.
 1-2:inv H; easy.
 inv H.
 apply IHp2 with (x := x) (l := l'0); try easy. 
 apply IHp1 with (x:=x) (l := l); try easy.
Qed.

Lemma eupdates_twice_neq : forall f x g n c v, x <> fst c 
           -> (put_cus f x g n)[c |-> v] = put_cus (f[c |-> v]) x g n.
Proof.
  intros. unfold put_cus.
  apply functional_extensionality.
  intros.
  bdestruct (x0 ==? c).
  subst.
  rewrite eupdate_index_eq.
  bdestruct (fst c =? x).
  subst. contradiction.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  bdestruct (fst x0 =? x).
  rewrite eupdate_index_neq.
  easy. nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  easy. nor_sym.
Qed.

Lemma get_cus_up : forall n f x c v, fst c <> x -> get_cus n (f[c |-> v]) x = get_cus n f x.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold get_cus.
  bdestruct (x0 <? n). destruct c. simpl in *. rewrite eupdate_index_neq by iner_p.
  easy. easy.
Qed.

Lemma get_cus_up_ge : forall n f x c v, n <= snd c -> get_cus n (f[c |-> v]) x = get_cus n f x.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold get_cus.
  bdestruct (x0 <? n). destruct c. simpl in *. rewrite eupdate_index_neq by iner_p.
  easy. easy.
Qed.



Lemma put_cu_mid_eq : forall (f g:posi -> val) a v, 
              nor_mode f a -> nor_mode g a -> get_r (f a) = get_r (g a) -> (put_cu (f a) v) = (put_cu (g a) v).
Proof.
 intros.
 unfold put_cu. unfold nor_mode in *.
 destruct (f a). destruct (g a).
 unfold get_r in H1. subst.
 easy. inv H0.
 inv H.
Qed.

Lemma put_cus_twice_neq : forall (f:posi -> val) (x y:var) g1 g2 n, 
              x <> y -> (put_cus (put_cus f x g1 n) y g2 n)
                          = (put_cus (put_cus f y g2 n) x g1 n).
Proof.
 intros.
 apply functional_extensionality.
 unfold put_cus. intros.
 destruct x0. simpl.
 bdestruct (v =? y).
 bdestruct (v =? x). lia. easy.
 easy.
Qed.


Lemma put_cu_twice_eq : forall (f:posi -> val) (x:var) v1 v2 i, 
        put_cu (put_cu (f (x,i)) v1) v2 = put_cu (f (x,i)) v2.
Proof.
  intros. unfold put_cu.
  destruct (f (x, i)). easy. easy.
Qed.

Lemma put_cu_twice_eq_1 : forall (f:posi -> val) c v1 v2, 
        put_cu (put_cu (f c) v1) v2 = put_cu (f c) v2.
Proof.
  intros. unfold put_cu.
  destruct (f c). easy. easy.
Qed.


Lemma put_cus_twice_eq : forall (f:posi -> val) (x:var) g1 g2 n, 
              (put_cus (put_cus f x g1 n) x g2 n)
                          = (put_cus f x g2 n).
Proof.
 intros.
 apply functional_extensionality.
 unfold put_cus. intros.
 destruct x0. simpl.
 bdestruct (v =? x).
 bdestruct (n0 <? n). rewrite put_cu_twice_eq. easy.
 easy.
 easy.
Qed.

Lemma put_cus_sem_eq : forall (f:posi -> val) (x:var) g1 g2 n, 
           (forall m, m < n -> g1 m = g2 m) -> 
                 (put_cus f x g1 n) = (put_cus f x g2 n).
Proof.
 intros.
 apply functional_extensionality.
 unfold put_cus. intros.
 destruct x0. simpl.
 bdestruct (v =? x).
 bdestruct (n0 <? n). rewrite H. easy.
 lia. easy. easy. 
Qed.




(* Here, we define the addto / addto_n functions for angle rotation. 
Definition cut_n (f:nat -> bool) (n:nat) := fun i => if i <? n then f i else allfalse i.
 
Definition fbrev' i n (f : nat -> bool) := fun (x : nat) => 
            if (x <=? i) then f (n - 1 - x) else if (x <? n - 1 - i) 
                         then f x else if (x <? n) then f (n - 1 - x) else f x.
Definition fbrev {A} n (f : nat -> A) := fun (x : nat) => if (x <? n) then f (n - 1 - x) else f x.
*)
Lemma x_nor_sem : forall aenv f x v, nor_mode f x -> put_cu (f x) (¬ (get_cua (f x))) = v ->
                            exp_sem aenv (X x) f = (f[x |-> v]).
Proof.
 intros.
 apply nor_mode_nval in H.
 destruct H. destruct H.
 unfold get_cua in H0. rewrite H in H0. 
 unfold put_cu in H0. subst. 
 assert ((exchange (f x)) = nval (¬ true) x0).
 unfold exchange. rewrite H. reflexivity.
 rewrite <- H0. simpl. easy.
 unfold get_cua in H0. rewrite H in H0.
 unfold put_cu in H0. subst.
 assert ((exchange (f x)) = nval (¬ false) x0).
 unfold exchange. rewrite H.
 reflexivity. 
 rewrite <- H0. simpl. easy. 
Qed.

Lemma lshift'_irrelevant :
   forall n size f x p, fst p <> x -> lshift' n size f x p = f p.
Proof.
  intros.
  induction n.
  simpl.
  rewrite eupdate_index_neq. easy.
  apply iner_neq_1. lia.
  simpl.
  rewrite eupdate_index_neq.
  rewrite IHn.
  easy.
  apply iner_neq_1. lia.
Qed.


Lemma rshift'_irrelevant :
   forall n size f x p, fst p <> x -> rshift' n size f x p = f p.
Proof.
  intros.
  induction n.
  intros. simpl.
  rewrite eupdate_index_neq. easy.
  apply iner_neq_1. lia.
  intros. simpl.
  rewrite eupdate_index_neq.
  rewrite IHn. easy.
  apply iner_neq_1. lia.
Qed.

Lemma sr_rotate'_ge : 
   forall n size f x p, n <= snd p -> sr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia.
 destruct p.
 bdestruct (x =? v).  subst.
 intros R. inv R. simpl in H. lia.
 intros R. inv R. lia.
Qed.

Lemma sr_rotate'_lt : 
   forall n size f p, snd p < n -> n <= size -> 
        sr_rotate' f (fst p) n size p = times_rotate (f p) (size - (snd p)).
Proof.
 intros. induction n.
 easy.
 simpl.
 destruct p. simpl in *.
 bdestruct (n =? n0). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia. lia.
Qed.

Lemma sr_rotate'_irrelevant : 
   forall n size f x p, fst p <> x -> sr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy.
 destruct p. iner_p.
Qed.

Lemma srr_rotate'_lt : 
   forall n size f p, snd p < n -> n <= size -> 
        srr_rotate' f (fst p) n size p = times_r_rotate (f p) (size - (snd p)).
Proof.
 intros. induction n.
 easy.
 simpl.
 destruct p. simpl in *.
 bdestruct (n =? n0). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia. lia.
Qed.

Lemma srr_rotate'_ge : 
   forall n size f x p, n <= snd p -> srr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia.
 destruct p.
 bdestruct (x =? v).  subst.
 intros R. inv R. simpl in H. lia.
 intros R. inv R. lia.
Qed.

Lemma srr_rotate'_irrelevant : 
   forall n size f x p, fst p <> x -> srr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy.
 destruct p. iner_p.
Qed.

Lemma lshift'_0 : forall m n f x, m <= n -> lshift' m n f x (x,0) = f (x,n).
Proof.
 intros.
 induction m.
 simpl. 
 rewrite eupdate_index_eq.
 easy.
 simpl.
 rewrite eupdate_index_neq by tuple_eq.
 rewrite IHm. easy. lia.
Qed.

Lemma lshift'_gt : forall i m n f x, m < i -> lshift' m n f x (x,i) = f (x,i).
Proof.
  intros.
  induction m.
  simpl.
  rewrite eupdate_index_neq. easy.
  tuple_eq.
  simpl.
  rewrite eupdate_index_neq.
  rewrite IHm.
  easy. lia.
  tuple_eq.
Qed.

Lemma lshift'_le : forall i m n f x, S i <= m <= n  -> lshift' m n f x (x,S i) = f (x,i).
Proof.
  induction m.
  simpl.
  intros. inv H. inv H0.
  intros.
  simpl.
  bdestruct (i =? m). subst.
  rewrite eupdate_index_eq. easy. 
  rewrite eupdate_index_neq.
  rewrite IHm. easy.
  lia.
  tuple_eq.
Qed.

Lemma rshift'_0 : forall m n f x, m <= n -> rshift' m n f x (x,n) = f (x,0).
Proof.
 intros.
 induction m.
 simpl. 
 rewrite eupdate_index_eq.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHm. easy. lia.
 tuple_eq.
Qed.

Lemma rshift'_gt : forall i m n f x, m <= n < i -> rshift' m n f x (x,i) = f (x,i).
Proof.
  induction m.
  simpl.
  intros.
  rewrite eupdate_index_neq. easy.
  tuple_eq.
  intros.
  simpl.
  rewrite eupdate_index_neq.
  rewrite IHm. easy.
  lia.
  tuple_eq.
Qed.

Lemma rshift'_le : forall i m n f x, i < m <= n  -> rshift' m n f x (x,i) = f (x,S i).
Proof.
  induction m.
  simpl.
  intros. inv H. inv H0.
  intros.
  simpl.
  bdestruct (i =? m). subst.
  rewrite eupdate_index_eq. easy. 
  rewrite eupdate_index_neq.
  rewrite IHm. easy.
  lia.
  tuple_eq.
Qed.

Lemma assign_r_angle_same : forall n i f x r, i < n -> nor_modes f x n ->
              get_r ((assign_r f x r n) (x,i)) = get_r (f (x,i)).
Proof.
  induction n; intros; simpl.
  easy.
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq.
  unfold up_qft.
  unfold nor_modes in *. unfold nor_mode in H0.
  specialize (H0 n H). 
  destruct (f (x,n)). unfold get_r. easy. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn. easy. lia.
  unfold nor_modes in *. intros. apply H0. lia.
Qed.

Lemma assign_seq_covers : forall m n i f x g h, i < m <= n ->
            nor_modes f x n -> h i = get_cua (f (x,i)) ->
            assign_seq (assign_r f x g n) x h m (x,i) = f (x,i).
Proof.
 induction m; intros; simpl. lia.
 bdestruct (i =? m).
 subst.
 rewrite eupdate_index_eq.
 rewrite assign_r_angle_same; try easy.
 rewrite H1. 
 unfold nor_modes in H0.
 assert (m < n) by lia.
 specialize (H0 m H2). unfold nor_mode in H0.
 destruct (f (x,m)). unfold get_cua,get_r. easy. lia.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHm; try easy. lia.
Qed.

Lemma assign_seq_ge : forall n i f x h, n <= i -> assign_seq f x h n (x,i) = f (x,i).
Proof.
 induction n; intros; simpl.
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma assign_seq_out : forall n p f x h, fst p <> x -> assign_seq f x h n p = f p.
Proof.
 induction n; intros; simpl.
 easy. destruct p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. easy.
Qed.

Lemma qft_start_nor_modes : forall aenv tenv tenv' x n f, well_typed_oexp aenv tenv (QFT x n) tenv'
        -> right_mode_env aenv tenv f -> nor_modes f x (aenv x).
Proof.
  intros. inv H. unfold right_mode_env in H0.
  unfold nor_modes. intros.
  specialize (H0 Nor (x,i)). simpl in H0.
  inv H1.
  apply type_nor_modes with (env := tenv); try easy.
Qed.

Lemma assign_r_same_0 : forall n size f x h, 0 < n <= size
          -> nor_modes f x size -> (assign_r f x h n (x,0)) = qval (get_r (f (x,0))) h.
Proof.
  induction n; intros; simpl.
  lia.
  bdestruct (n =? 0). subst.
  rewrite eupdate_index_eq.
  unfold nor_modes in H0.
  assert (0 < size) by lia.
  specialize (H0 0 H1). unfold nor_mode in H0.
  unfold lshift_fun.
  unfold up_qft.
  destruct (f (x,0)). unfold get_r.
  assert ((fun i : nat => h (i + 0)) = h).
  apply functional_extensionality.
  intros. rewrite plus_0_r. easy. rewrite H2. easy. lia.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn with (size := size); try easy. lia.
Qed.

Lemma assign_r_ge : forall n i f x h, n <= i -> assign_r f x h n (x,i) = f (x,i).
Proof.
 induction n; intros; simpl.
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma assign_r_out : forall n p f x h, fst p <> x -> assign_r f x h n p = f p.
Proof.
 induction n; intros; simpl.
 easy. destruct p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. easy.
Qed.

Lemma assign_h_ge : forall i n j f x, n + i <= j -> assign_h f x n i (x,j) = f (x,j).
Proof.
 induction i; intros; simpl.
 easy.
 rewrite eupdate_index_neq.
 rewrite IHi. easy. lia. iner_p. 
Qed.

Lemma assign_h_lt_same : forall i n j f x, j < n -> assign_h f x n i (x,j) = f (x,j).
Proof.
 induction i; intros; simpl.
 easy.
 rewrite eupdate_index_neq.
 rewrite IHi. easy. lia. iner_p. 
Qed.

Lemma assign_h_r_out : forall i n p f x, fst p <> x -> assign_h_r f x n i p = f p.
Proof.
 induction i; intros; simpl.
 easy. destruct p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHi. easy. easy.
Qed.

Lemma assign_h_r_ge : forall i n j f x, n + i <= j -> assign_h_r f x n i (x,j) = f (x,j).
Proof.
 induction i; intros; simpl.
 easy.
 rewrite eupdate_index_neq.
 rewrite IHi. easy. lia. iner_p. 
Qed.


Lemma assign_h_r_lt_same : forall i n j f x, j < n -> assign_h_r f x n i (x,j) = f (x,j).
Proof.
 induction i; intros; simpl.
 easy.
 rewrite eupdate_index_neq.
 rewrite IHi. easy. lia. iner_p. 
Qed.

Lemma assign_h_out : forall i n p f x, fst p <> x -> assign_h f x n i p = f p.
Proof.
 induction i; intros; simpl.
 easy. destruct p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHi. easy. easy.
Qed.

Lemma assign_seq_out_1 : forall n f h x y i, x <> y -> assign_seq f x h n (y,i) = f (y,i).
Proof.
 induction n; intros; simpl.
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. easy.
Qed.

(*
Lemma h_sem_out : forall n f x y i, x <> y -> h_sem f x n (y,i) = f (y,i).
Proof.
 induction n; intros; simpl. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn; try easy.
Qed.

Lemma h_sem_ge : forall n f x i, n <= i -> h_sem f x n (x,i) = f (x,i).
Proof.
 induction n; intros; simpl. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn; try easy. lia.
Qed.
*)
Lemma assign_r_lt : forall n f x r i, i < n -> assign_r f x r n (x,i) = up_qft (f (x,i)) (lshift_fun r i).
Proof.
 induction n; intros; simpl.
 lia.
 bdestruct (i =? n). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma lshift_fun_0 : forall f, lshift_fun f 0 = f.
Proof.
  intros. apply functional_extensionality. intros.
  unfold lshift_fun. rewrite plus_0_r. easy.
Qed.

Lemma efresh_exp_sem_irrelevant :
  forall e aenv  p f,
    exp_WF aenv e -> 
    exp_fresh aenv p e ->
    exp_sem aenv e f p = f p.
Proof.
  induction e;intros.
  subst. simpl. easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq. easy. nor_sym.
  simpl.
  destruct (get_cua (f p)).
  eapply IHe. inv H. easy. inv H0. assumption. easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq. easy. nor_sym.
  simpl in *. inv H0.
  rewrite eupdate_index_neq. easy. nor_sym.
  inv H0.
  destruct H3.
  simpl. unfold sr_rotate.
  rewrite sr_rotate'_irrelevant; try easy.
  simpl. unfold sr_rotate.
  rewrite sr_rotate'_ge; try easy.
  inv H0.
  destruct H3.
  simpl. unfold srr_rotate.
  rewrite srr_rotate'_irrelevant; try easy.
  simpl. unfold srr_rotate.
  rewrite srr_rotate'_ge; try easy.
  simpl. unfold lshift. inv H0.
  unfold or_not_eq in H3.
  destruct H3.
  apply lshift'_irrelevant. easy.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (aenv v =? 0).  rewrite H1 in *. simpl.
  rewrite eupdate_same; try easy.
  rewrite lshift'_gt. easy. simpl in H0. lia.
  apply lshift'_irrelevant. iner_p.
  simpl. unfold rshift. inv H0.
  unfold or_not_eq in H3.
  destruct H3.
  apply rshift'_irrelevant. easy.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (aenv v =? 0).  rewrite H1 in *. simpl.
  rewrite eupdate_same; try easy.
  rewrite rshift'_gt. easy. simpl in H0. lia.
  apply rshift'_irrelevant. iner_p.
  simpl. unfold reverse. inv H0.
  unfold or_not_eq in H3. destruct H3.
  bdestruct ((fst p =? x)). lia. simpl. easy.
  bdestruct ((snd p <? aenv x)). lia. 
  bdestruct ((fst p =? x)). simpl. easy. simpl. easy.
  simpl. inv H0. unfold or_not_eq in H3.
  unfold turn_qft.
  destruct H3.
  rewrite assign_h_out; try easy.
  rewrite assign_r_out; try easy.
  inv H.
  destruct p.
  bdestruct (x =? v). subst.
  rewrite assign_h_ge; try easy.
  rewrite assign_r_ge; try easy. simpl in *. lia. simpl in *. lia.
  rewrite assign_h_out; try easy.
  rewrite assign_r_out; try easy. iner_p. iner_p.
  simpl. inv H0. unfold or_not_eq in H3.
  unfold turn_rqft.
  destruct H3.
  rewrite assign_h_r_out; try easy.
  rewrite assign_seq_out; try easy.
  destruct p.
  bdestruct (x =? v). subst.
  rewrite assign_h_r_ge; try easy.
  rewrite assign_seq_ge; try easy. simpl in *. inv H. lia. inv H. simpl in *. lia.
  rewrite assign_h_r_out; try easy.
  rewrite assign_seq_out; try easy. iner_p. iner_p.
  inv H0. simpl.
  apply (IHe1) with (aenv := aenv) (f := f) in H4.
  apply (IHe2) with (aenv := aenv) (f := (exp_sem aenv e1 f)) in H5.
  rewrite H5. rewrite H4. easy. inv H. easy. inv H. easy.
Qed.

Lemma two_cu_same : forall aenv f p e1 e2, get_cua (f p) = true ->
                     exp_WF aenv e1 -> 
                     exp_fresh aenv p e1 -> exp_sem aenv (e1 ; e2) f = exp_sem aenv (CU p e1; CU p e2) f. 
Proof.
  intros.
  simpl.
  destruct (get_cua (f p)) eqn:eq1.
  rewrite (efresh_exp_sem_irrelevant e1 aenv p f) by assumption.
  destruct (get_cua (f p)). easy.
  inv eq1. inv H.
Qed.

Lemma well_typed_right_mode_exp : forall e aenv env f, well_typed_exp env e
          -> right_mode_env aenv env f -> right_mode_env aenv env (exp_sem aenv e f).
Proof.
  intros. induction H; simpl; try easy.
  unfold right_mode_env in *. intros. 
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold exchange.
  specialize (H0 Nor p0 H1 H). 
  destruct (f p0) eqn:eq1.
  apply mapsto_always_same with (v1:=Nor) in H2; try easy.
  rewrite <- H2 in *. constructor. inv H0.
  rewrite eupdate_index_neq. apply H0; try easy. easy.
  unfold right_mode_env in *.
  intros.
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  apply mapsto_always_same with (v1:=Nor) in H2; try easy.  
  rewrite <- H2 in *.
  specialize (H0 Nor p0 H1 H).
  destruct (f p0) eqn:eq1.
  destruct b. constructor. constructor.
  inv H0.
  rewrite eupdate_index_neq by iner_p. apply H0. easy. easy.
  unfold right_mode_env in *.
  intros.
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold times_r_rotate.
  apply mapsto_always_same with (v1:=Nor) in H2; try easy.  
  rewrite <- H2 in *.
  specialize (H0 Nor p0 H1 H).
  destruct (f p0) eqn:eq1.
  destruct b. constructor. constructor.
  inv H0.
  rewrite eupdate_index_neq by iner_p. apply H0. easy. easy.
  unfold right_mode_env in *.
  intros.
  unfold sr_rotate.
  bdestruct (x =? fst p). subst.
  bdestruct (snd p <=? m).
  rewrite sr_rotate'_lt; try lia.
  apply mapsto_always_same with (v1:=(Phi b)) in H3; try easy.
  rewrite <- H3 in *.
  unfold times_rotate.
  specialize (H0 (Phi b) p H2 H).
  destruct (f p). inv H0. constructor.
  rewrite sr_rotate'_ge; try lia.
  apply H0 ; try easy.
  rewrite sr_rotate'_irrelevant.
  apply H0; try easy. lia.
  unfold right_mode_env in *.
  intros. unfold srr_rotate.
  bdestruct (x =? fst p). subst.
  bdestruct (snd p <=? m).
  rewrite srr_rotate'_lt; try lia.
  apply mapsto_always_same with (v1:=(Phi b)) in H3; try easy.
  rewrite <- H3 in *.
  unfold times_r_rotate.
  specialize (H0 (Phi b) p H2 H).
  destruct (f p). inv H0. constructor.
  rewrite srr_rotate'_ge; try lia.
  apply H0 ; try easy.
  rewrite srr_rotate'_irrelevant.
  apply H0; try easy. lia.
  unfold right_mode_env in *. intros.
  unfold lshift.
  destruct p. 
  bdestruct (x =? v). subst. simpl in H1.
  destruct n.
  rewrite lshift'_0 by lia.
  apply H0. simpl in *. lia. easy.
  rewrite lshift'_le by lia. apply H0. simpl in *. lia. easy.
  rewrite lshift'_irrelevant by iner_p.
  apply H0. simpl in *. easy. easy.
  unfold right_mode_env in *. intros.
  unfold rshift.
  destruct p. 
  bdestruct (x =? v). subst. simpl in H1.
  bdestruct (n <? (aenv v - 1)).
  rewrite rshift'_le by lia. apply H0. simpl in *. lia. easy.
  bdestruct (n =? (aenv v - 1)).
  subst.
  rewrite rshift'_0 by lia. apply H0. simpl in *. lia. easy. lia.
  rewrite rshift'_irrelevant by iner_p. apply H0. simpl in *. lia. easy.
  unfold right_mode_env in *. intros.
  destruct p. simpl in H1.
  unfold reverse. simpl.
  bdestruct (v =? x). bdestruct (n <? aenv x). simpl.
  subst. apply H0. simpl in *. lia. easy.
  simpl in *. apply H0. easy. easy.
  simpl in *. apply H0. easy. easy.
Qed.

(* Type Soundness theorem. *)
Lemma well_typed_right_mode_pexp : forall e aenv tenv tenv' f, 
        well_typed_oexp aenv tenv e tenv'
          -> right_mode_env aenv tenv f -> right_mode_env aenv tenv' (exp_sem aenv e f).
Proof.
  induction e; intros.
  inv H.
  apply well_typed_right_mode_exp; try easy.
  inv H.
  apply well_typed_right_mode_exp; try easy.
  inv H. inv H1.
  specialize (IHe aenv tenv' tenv' f).
  apply IHe in H8; try easy.
  unfold right_mode_env in *.
  intros.
  simpl.
  destruct (get_cua (f p)) eqn:eq1.
  apply H8; try easy.
  apply H0; try easy.
  inv H.
  apply well_typed_right_mode_exp; try easy.
  inv H.
  apply well_typed_right_mode_exp; try easy.
  inv H.
  apply well_typed_right_mode_exp; try easy.
  inv H.
  apply well_typed_right_mode_exp; try easy.
  inv H.
  apply well_typed_right_mode_exp; try easy.
  inv H.
  apply well_typed_right_mode_exp; try easy.
  inv H.
  apply well_typed_right_mode_exp; try easy.
  simpl. inv H. inv H1. 
  unfold turn_qft.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v (Phi b) tenv)) in H1; try easy.
  apply mapsto_add1 in H1. subst.
  bdestruct (n <? b).
  rewrite assign_h_lt_same by easy.
  apply assign_r_right_mode. lia.
  intros. apply H0. simpl. lia. easy.
  apply assign_h_right_mode with (size := aenv v); try easy. lia.
  intros. rewrite assign_r_ge by lia. apply H0. simpl. lia. simpl. easy.
  apply assign_h_right_mode_out; try lia.
  apply assign_r_right_mode_out; try lia.
  apply H0. easy. simpl.
  apply mapsto_equal with (s2 := (Env.add x (Phi b) tenv)) in H1; try easy.
  apply Env.add_3 in H1; try lia. easy.
  simpl.
  inv H. inv H1. unfold turn_rqft.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v Nor tenv)) in H1; try easy.
  apply mapsto_add1 in H1. subst.
  bdestruct (n <? b).
  rewrite assign_h_r_lt_same by easy.
  apply assign_seq_right_mode. easy.
  apply assign_h_r_right_mode with (size := aenv v); try easy. lia.
  intros. rewrite assign_seq_ge by lia. apply H0. simpl. lia. simpl. easy.
  apply assign_h_r_right_mode_out; try lia.
  apply assign_seq_right_mode_out; try lia.
  apply H0. easy. simpl.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H1; try easy.
  apply Env.add_3 in H1; try lia. easy.
  simpl.
  inv H. inv H1.
  specialize (IHe1 aenv tenv env' f H4 H0).
  specialize (IHe2 aenv env' tenv' (exp_sem aenv e1 f) H6 IHe1).
  easy.
Qed.

Lemma rev_twice_same : forall f st x, reverse (reverse st x (f x)) x (f x) = st.
Proof.
  intros. unfold reverse.
  apply functional_extensionality.
  intros.
  destruct x0. simpl.
  bdestruct (v =? x).
  subst.
  bdestruct ((n <? f x)).
  simpl.
  bdestruct ((x =? x)).
  bdestruct (( f x - 1 - n <? f x)).
  simpl.
  assert ( f x - 1 - ( f x - 1 - n)= n) by lia.
  rewrite H2. easy.
  simpl. lia.
  lia. simpl. easy.
  simpl. easy.
Qed.

(*
  The following defines the inverse function of a given RCIRplus circuit. 
*)

Lemma inv_exp_involutive :
  forall p,
    inv_exp (inv_exp p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite IHp. easy.
  - rewrite IHp1, IHp2. easy.
Qed.

Lemma fresh_inv_exp :
  forall aenv p e,
    exp_fresh aenv p e ->
    exp_fresh aenv p (inv_exp e).
Proof.
  intros. induction H; simpl; try constructor; try assumption.
Qed.

Lemma neu_l_inv_exp :
  forall e x l l',
    exp_neu_prop l ->
    exp_neu_l x l e l' ->
    exp_neu_l x l' (inv_exp e) l.
Proof.
  induction e; intros; simpl.
  1-7: inv H0 ; constructor.
  apply IHe. unfold exp_neu_prop. intros.
  simpl in H0. lia. easy.
  specialize (exp_neu_t_prop (Lshift x) x0 l l' H0 H) as eq1.
  inv H0.
  destruct l'.
  apply rshift_neul_b.
  unfold fst_not_opp. easy.
  apply rshift_neul_b.
  unfold fst_not_opp.
  unfold exp_neu_prop in H.
  specialize (H 0 Rs).
  assert (0 + 1 < length (Rs :: s :: l')). simpl. lia.
  apply H in H0.
  simpl in *. unfold opp_ls. destruct s. contradiction.
  intros R. inv R. intros R. inv R. simpl in *. easy.
  unfold fst_not_opp in H3. destruct l.
  apply rshift_neul_a.
  apply rshift_neul_a.
  apply rshift_neul_ne. easy.
  specialize (exp_neu_t_prop (Rshift x) x0 l l' H0 H) as eq1.
  inv H0.
  destruct l'.
  apply lshift_neul_b.
  unfold fst_not_opp. easy.
  apply lshift_neul_b.
  unfold fst_not_opp.
  unfold exp_neu_prop in H.
  specialize (H 0 Ls).
  assert (0 + 1 < length (Ls :: s :: l')). simpl. lia.
  apply H in H0.
  simpl in *. unfold opp_ls. destruct s.
  intros R. inv R. contradiction. intros R. inv R. simpl in *. easy.
  unfold fst_not_opp in H3. destruct l.
  apply lshift_neul_a.
  apply lshift_neul_a.
  apply lshift_neul_ne. easy.
  specialize (exp_neu_t_prop (Rev x) x0 l l' H0 H) as eq1.
  inv H0.
  destruct l'.
  apply rev_neul_b.
  unfold fst_not_opp. easy.
  apply rev_neul_b.
  unfold fst_not_opp.
  unfold exp_neu_prop in H.
  specialize (H 0 Re).
  assert (0 + 1 < length (Re :: s :: l')). simpl. lia.
  apply H in H0.
  simpl in *. unfold opp_ls. destruct s.
  intros R. inv R. intros R. inv R. contradiction. simpl in *. easy.
  unfold fst_not_opp in H3. destruct l.
  apply rev_neul_a.
  apply rev_neul_a.
  apply rev_neul_ne. easy.
  1-2: inv H0 ; constructor.
  inv H0. 
  specialize (exp_neu_t_prop e1 x l l'0 H4 H) as eq1.
  specialize (exp_neu_t_prop e2 x l'0 l' H6 eq1) as eq2.
  econstructor.
  apply IHe2.
  apply eq1. apply H6.
  apply IHe1; try easy.
Qed.


Lemma typed_inv_exp :
  forall tenv p,
    well_typed_exp tenv p ->
    well_typed_exp tenv (inv_exp p).
Proof.
  intros. induction p; simpl; try assumption.
  inv H. inv H. constructor. assumption.
  inv H.  constructor. easy.
  inv H. apply srr_phi with (b := b); try easy.
  inv H. apply sr_phi with (b := b); try easy.
  inv H. constructor. easy.
  inv H.
  constructor.  easy.
  inv H. inv H. inv H.
Qed.

Lemma inv_get_vars : forall e x, In x (get_vars (inv_exp e)) -> In x (get_vars e).
Proof.
  induction e; intros; simpl; try easy.
  simpl in H. destruct H. left. easy.
  right. apply IHe. easy.
  simpl in H.
  apply in_or_app.
  apply in_app_or in H.
  destruct H. right. apply IHe2. easy.
  left. apply IHe1. easy.
Qed.

(* Type Soundness on the inverse operations. *)
Lemma typed_inv_pexp :
  forall p aenv tenv tenv',
    well_typed_oexp aenv tenv p tenv' ->
    well_typed_oexp aenv tenv' (inv_exp p) tenv.
Proof.
  induction p; intros; simpl; try assumption.
  inv H. constructor. easy.
  inv H. constructor. easy.
  inv H. inv H0.
  apply pcu_nor; try easy.
  apply fresh_inv_exp. easy.
  unfold exp_neu. intros.
  apply neu_l_inv_exp.
  unfold exp_neu_prop. intros. simpl in *. lia.
  unfold exp_neu in H5.
  apply H5. apply inv_get_vars. easy.
  apply IHp. easy.
  inv H. constructor.
  apply typed_inv_exp in H0. simpl in H0. easy.
  inv H. constructor.
  apply typed_inv_exp in H0. simpl in H0. easy.
  inv H. constructor.
  apply typed_inv_exp in H0. simpl in H0. easy.
  inv H. constructor.
  apply typed_inv_exp in H0. simpl in H0. easy.
  inv H. constructor.
  apply typed_inv_exp in H0. simpl in H0. easy.
  inv H. constructor.
  apply typed_inv_exp in H0. simpl in H0. easy.
  inv H. constructor.
  apply typed_inv_exp in H0. simpl in H0. easy.
  inv H. inv H0.
  apply rqft_phi. easy.
  apply mapsto_equal with (s1 := (Env.add x (Phi b) tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H4. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H6.
  rewrite EnvFacts.add_neq_o; try easy.
  inv H. inv H0.
  apply qft_nor. easy.
  apply mapsto_equal with (s1 := (Env.add x Nor tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H4. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H6.
  rewrite EnvFacts.add_neq_o; try easy.
  inv H. inv H0.
  econstructor.
  apply IHp2. apply H5.
  apply IHp1. easy.
Qed.

Lemma exchange_twice_same :
   forall (f: posi -> val) p, exchange (exchange (f p)) = f p.
Proof.
  intros. unfold exchange.
  destruct (f p) eqn:eq1.
  assert ((¬ (¬ b)) = b) by btauto.
  rewrite H. easy.
  easy.
Qed.   


Lemma rotate_r_same : forall r q, (rotate (r_rotate r q) q) = r.
Proof.
  intros. unfold rotate,r_rotate.
  rewrite add_to_r_same.
  easy.
Qed.

Lemma rotate_same : forall r q, (r_rotate (rotate r q) q) = r.
Proof.
  intros. unfold rotate,r_rotate.
  rewrite add_to_same.
  easy.
Qed.


Lemma times_rotate_r_same: forall r q, times_rotate (times_r_rotate r q) q = r.
Proof.
  intros.
  unfold times_rotate, times_r_rotate.
  destruct r.
  destruct b.
  rewrite rotate_r_same.
  easy. easy.
  rewrite rotate_r_same.
  easy.
Qed.

Lemma times_rotate_same: forall r q, times_r_rotate (times_rotate r q) q = r.
Proof.
  intros.
  unfold times_rotate, times_r_rotate.
  destruct r.
  destruct b. 
  rewrite rotate_same.
  easy. easy.
  rewrite rotate_same.
  easy.
Qed.


Lemma lr_shift_same : forall n f x, 
                 lshift ((rshift f x n)) x n = f.
Proof.
  intros.
  unfold lshift,rshift.
  apply functional_extensionality.
  intros.
  destruct x0.
  bdestruct (v =? x). subst.
  bdestruct (n0 =? 0). subst.
  rewrite lshift'_0.
  rewrite rshift'_0. easy. easy. easy.
  destruct n0. lia.
  bdestruct (S n0 <=? n-1).
  rewrite lshift'_le.
  rewrite rshift'_le.
  easy. lia. lia.
  rewrite lshift'_gt.
  rewrite rshift'_gt. easy.
  lia. lia.
  rewrite lshift'_irrelevant.
  rewrite rshift'_irrelevant.
  easy. simpl; assumption.
  simpl;assumption.
Qed.

Lemma rl_shift_same : forall n f x,
                 rshift ((lshift f x n)) x n = f.
Proof.
  intros.
  unfold lshift,rshift.
  apply functional_extensionality.
  intros.
  destruct x0.
  bdestruct (v =? x). subst.
  bdestruct (n0 =? n-1). subst.
  rewrite rshift'_0.
  rewrite lshift'_0. easy. easy. easy.
  bdestruct (n0 <? n-1).
  rewrite rshift'_le.
  rewrite lshift'_le.
  easy. lia. lia.
  rewrite rshift'_gt.
  rewrite lshift'_gt. easy.
  lia. lia.
  rewrite rshift'_irrelevant.
  rewrite lshift'_irrelevant.
  easy. simpl; assumption.
  simpl;assumption.
Qed.

(*
Lemma h_sem_gt : forall m n f x v,
      m <= n -> 
       h_sem (f[(x,n) |-> v]) x m = (h_sem f x m)[(x,n) |-> v].
Proof.
  induction m; intros.
  simpl. easy.
  simpl.
  rewrite eupdate_twice_neq by iner_p.
  rewrite IHm by lia.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma had_twice_same : forall n f x t, 
     (forall i, i < n -> right_mode_val t (f (x,i))) ->
    h_sem (h_sem f x n) x n = f.
Proof.
  induction n; intros.
  simpl. easy.
  simpl.
  rewrite h_sem_gt by lia.
  rewrite eupdate_twice_eq.
  rewrite eupdate_index_eq.
  rewrite h_case_twice_same with (t := t).
  rewrite IHn with (t := t).
  rewrite eupdate_same. easy. easy.
  intros. apply H0. lia. apply H0. lia.
Qed.
*)
Lemma sr_rotate_up : forall m n f x size v, m <= n -> 
     sr_rotate' (f[(x,n) |-> v]) x m size = (sr_rotate' f x m size)[(x,n) |-> v].
Proof.
  induction m; intros; simpl.
  easy.
  rewrite eupdate_twice_neq by iner_p.
  rewrite <- (IHm n f).
  rewrite eupdate_index_neq by iner_p. easy. lia.
Qed.

Lemma sr_rotate_rotate: forall f x n size, sr_rotate' (srr_rotate' f x n size) x n size = f.
Proof.
  intros. induction n;simpl. easy.
  simpl. rewrite sr_rotate_up by lia.
  rewrite eupdate_twice_eq.
  rewrite IHn.
  rewrite eupdate_same. easy.
  rewrite eupdate_index_eq.
  rewrite times_rotate_r_same. easy.
Qed.

Lemma srr_rotate_up : forall m n f x size v, m <= n -> 
     srr_rotate' (f[(x,n) |-> v]) x m size = (srr_rotate' f x m size)[(x,n) |-> v].
Proof.
  induction m; intros; simpl.
  easy.
  rewrite eupdate_twice_neq by iner_p.
  rewrite <- (IHm n f).
  rewrite eupdate_index_neq by iner_p. easy. lia.
Qed.

Lemma srr_rotate_rotate: forall f x n size, srr_rotate' (sr_rotate' f x n size) x n size = f.
Proof.
  intros. induction n;simpl. easy.
  simpl. rewrite srr_rotate_up by lia.
  rewrite eupdate_twice_eq.
  rewrite IHn.
  rewrite eupdate_same. easy.
  rewrite eupdate_index_eq.
  rewrite times_rotate_same. easy.
Qed.


Lemma put_cu_get_r : forall c f b, nor_mode f c -> put_cu (f c) b = nval b (get_r (f c)).
Proof.
  intros.
  unfold put_cu, get_r.
  unfold nor_mode in H.
  destruct (f c). easy. lia.
Qed.

Lemma get_cus_qft_out : forall n x y b f aenv,
         exp_WF aenv (QFT y b) ->
          x <> y -> (get_cus n (exp_sem aenv (QFT y b) f) x) = get_cus n f x.
Proof.
  intros.
  unfold get_cus.
  apply functional_extensionality; intro.
  bdestruct (x0 <? n).
  rewrite efresh_exp_sem_irrelevant. easy. easy.
  constructor. unfold or_not_eq. left. easy. easy.
Qed.

Lemma get_cus_assign_seq_aux : forall n i size x f g, i < n <= size ->
      get_cus size (assign_seq f x g n) x i = g i.
Proof.
  induction n; intros; unfold get_cus in *; simpl.
  lia.
  specialize (IHn i size x f g).
  bdestruct (i <? size).
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn. easy. lia.
  lia.
Qed.

Lemma get_cus_assign_seq : forall size x f g,
      (get_cus size (assign_seq f x g size) x) = cut_n g size.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold cut_n.
  bdestruct (x0 <? size).
  rewrite get_cus_assign_seq_aux.
  easy. lia.
  unfold get_cus.
  bdestruct (x0 <? size). lia. easy.
Qed.

Lemma exp_sem_assoc : forall aenv f e1 e2 e3, 
               exp_sem aenv (e1 ; e2 ; e3) f = exp_sem aenv (e1 ; (e2 ; e3)) f.
Proof.
  intros. simpl. easy.
Qed.

(* QFT uniformity. For any varible x that is in Phi mode, 
   all qubits form a special format. *)
Lemma pexp_sem_assoc : forall env f e1 e2 e3, 
               exp_sem env (e1 ; e2 ; e3) f = exp_sem env (e1 ; (e2 ; e3)) f.
Proof.
  intros. simpl. easy.
Qed.

Definition phi_mode (f : posi -> val)  (x:posi) : Prop :=
       match f x with qval rc r => True | _ => False end.

Definition phi_modes (f:posi -> val) (x:var) (n:nat) :=
      forall i, i < n -> phi_mode f (x,i).

Lemma type_phi_mode :  forall f aenv env b p, 
    Env.MapsTo (fst p) (Phi b) env 
          -> snd p < aenv (fst p) -> right_mode_env aenv env f -> phi_mode f p.
Proof.
 intros. unfold right_mode_env in *.
 apply (H1 (Phi b)) in H0 ; try easy.
 inv H0. unfold phi_mode.
 rewrite <- H4. easy.
Qed.

Lemma type_phi_modes :  forall f aenv env x b, 
    Env.MapsTo x (Phi b) env -> right_mode_env aenv env f -> phi_modes f x (aenv x).
Proof.
 intros. unfold right_mode_env in *.
 unfold phi_modes. intros.
 specialize (H0 (Phi b) (x,i)).
 simpl in H0. apply H0 in H1; try easy.
 inv H1. unfold phi_mode.
 assert ((@pair var nat x i) = (@pair Env.key nat x i)) by easy.
 rewrite H1 in *.
 rewrite <- H4. easy.
Qed.

Lemma phi_mode_two_same : forall f g c, phi_mode f c -> phi_mode g c
      -> get_r (f c) = get_r (g c) -> get_snd_r f c = get_snd_r g c -> f c = g c.
Proof.
  intros. unfold phi_mode in *.
  destruct (f c) eqn:eq1.  easy.
  destruct (g c) eqn:eq2. easy.
  unfold get_r in *. subst.
  unfold get_snd_r in *. rewrite eq1 in *. rewrite eq2 in *. subst. easy.
Qed.

Lemma at_match_trans : forall aenv tenv tenv' e, well_typed_oexp aenv tenv e tenv' 
        -> at_match aenv tenv -> at_match aenv tenv'.
Proof.
  intros. induction H; simpl. easy.
  unfold at_match in *. intros.
  bdestruct (x =? x0). subst.
  apply mapsto_equal with (s2 := (Env.add x0 (Phi b) env)) in H3; try easy.
  apply mapsto_add1 in H3. inv H3. easy.
  apply mapsto_equal with (s2 := (Env.add x (Phi b) env)) in H3; try easy.
  apply Env.add_3 in H3. apply H0 in H3. easy. easy.
  unfold at_match in *. intros.
  bdestruct (x =? x0). subst.
  apply mapsto_equal with (s2 := (Env.add x0 Nor env)) in H3; try easy.
  apply mapsto_add1 in H3. inv H3.
  apply mapsto_equal with (s2 := (Env.add x Nor env)) in H3; try easy.
  apply Env.add_3 in H3. apply H0 in H3. easy. easy.
  easy.
  apply IHwell_typed_oexp2. apply IHwell_typed_oexp1. easy.
Qed.

Lemma assign_seq_lt : forall n i f x h, i < n -> assign_seq f x h n (x,i) = nval (h i) (get_r (f (x,i))).
Proof.
 induction n; intros; simpl.
 easy.
 bdestruct (i =? n). subst.
 rewrite eupdate_index_eq. 
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma assign_r_covers : forall m n i f x g h, i < m <= n ->
            phi_modes f x n -> lshift_fun h i  = get_snd_r f (x,i) ->
            assign_r (assign_seq f x g n) x h m (x,i) = f (x,i).
Proof.
 induction m; intros; simpl. lia.
 bdestruct (i =? m).
 subst.
 rewrite eupdate_index_eq.
 rewrite assign_seq_lt; try lia.
 unfold up_qft.
 unfold phi_modes in H1.
 specialize (H0 m).
 assert (m < n) by lia. apply H0 in H2.
 unfold phi_mode in H2.
 unfold get_snd_r in H1.
 destruct (f (x,m)). lia.
 rewrite <- H1.
 unfold get_r. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHm; try easy. lia.
Qed.

Lemma assign_h_hit : forall i j b f x size, b <= j < size -> j < b + i ->
             (assign_h f x b i (x,j)) = up_h (f (x,j)).
Proof.
  induction i;intros; simpl. lia.
  bdestruct (j =? b+i). subst. 
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq. rewrite IHi with (size := size); try easy. lia.
  iner_p.
Qed.

Lemma nor_to_phi_modes: forall x b size aenv f, aenv x >= size ->
        nor_modes f x size -> phi_modes (exp_sem aenv (QFT x b) f) x size.
Proof.
  intros.
  unfold phi_modes, nor_modes in *.
  intros.
  simpl.
  unfold turn_qft.
  apply H0 in H1 as eq1.
  unfold nor_mode,phi_mode in *.
  bdestruct (b <=? i).
  rewrite assign_h_hit with (size := aenv x); try lia.
  rewrite assign_r_ge ; try easy.
  unfold up_h. destruct (f (x,i)). destruct b0.
  1-3: easy.
  rewrite assign_h_lt_same; try lia.
  rewrite assign_r_lt by lia.
  unfold up_qft.
  destruct (f (x,i)).
  1-2: easy.
Qed.

Lemma assign_h_r_hit : forall i j b f x size, b <= j < size -> j < b + i ->
             (assign_h_r f x b i (x,j)) = up_h (f (x,j)).
Proof.
  induction i;intros; simpl. lia.
  bdestruct (j =? b+i). subst. 
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq. rewrite IHi with (size := size); try easy. lia.
  iner_p.
Qed.

Lemma assign_h_r_flip: forall i n x b f r, n <= b ->
   assign_h (assign_r f x r n) x b i = assign_r (assign_h f x b i) x r n.
Proof.
  induction i; intros; simpl.
  easy.
  apply functional_extensionality. intros.
  destruct x0.
  bdestruct (x =? v). subst.
  bdestruct (n0 <? n).
  rewrite eupdate_index_neq by iner_p.
  rewrite IHi by easy.
  rewrite assign_r_lt by lia.
  rewrite assign_r_lt by lia.
  rewrite eupdate_index_neq; iner_p. easy.
  rewrite assign_r_ge by lia.
  rewrite assign_r_ge by lia.
  bdestruct (n0 =? b+ i). subst.
  rewrite eupdate_index_eq; iner_p.
  rewrite eupdate_index_eq; iner_p. easy.
  rewrite eupdate_index_neq ; iner_p.
  rewrite eupdate_index_neq ; iner_p.
  rewrite IHi by easy.
  rewrite assign_r_ge by lia. easy.
  rewrite eupdate_index_neq ; iner_p.
  rewrite assign_h_out; iner_p.
  rewrite assign_r_out; iner_p.
  rewrite assign_r_out; iner_p.
  rewrite eupdate_index_neq ; iner_p.
  rewrite assign_h_out; iner_p.
  easy.
Qed.

Lemma assign_hr_seq_flip: forall i n x b f r, n <= b ->
   assign_h_r (assign_seq f x r n) x b i = assign_seq (assign_h_r f x b i) x r n.
Proof.
  induction i; intros; simpl.
  easy.
  apply functional_extensionality. intros.
  destruct x0.
  bdestruct (x =? v). subst.
  bdestruct (n0 <? n).
  rewrite eupdate_index_neq by iner_p.
  rewrite IHi by easy.
  rewrite assign_seq_lt by lia.
  rewrite assign_seq_lt by lia.
  rewrite eupdate_index_neq; iner_p. easy.
  rewrite assign_seq_ge by lia.
  rewrite assign_seq_ge by lia.
  bdestruct (n0 =? b+ i). subst.
  rewrite eupdate_index_eq; iner_p.
  rewrite eupdate_index_eq; iner_p. easy.
  rewrite eupdate_index_neq ; iner_p.
  rewrite eupdate_index_neq ; iner_p.
  rewrite IHi by easy.
  rewrite assign_seq_ge by lia. easy.
  rewrite eupdate_index_neq ; iner_p.
  rewrite assign_h_r_out; iner_p.
  rewrite assign_seq_out; iner_p.
  rewrite assign_seq_out; iner_p.
  rewrite eupdate_index_neq ; iner_p.
  rewrite assign_h_r_out; iner_p.
  easy.
Qed.

Lemma assign_hr_cancel_aux: forall i j n x b f, i <= n -> b <= j < b + i ->
        nor_mode f (x,j) ->
        assign_h_r (assign_h f x b n) x b i (x,j) = f (x,j).
Proof.
  induction i;intros;simpl.
  lia.
  bdestruct (j =? b + i). subst.
  rewrite eupdate_index_eq.
  rewrite assign_h_hit with (size := b+n); try lia.
  unfold nor_mode in H1.
  unfold up_h.
  destruct (f (x,b+i)) eqn:eq1. destruct b0.
  rewrite rotate_1_0; try easy. easy. easy.
  rewrite eupdate_index_neq; iner_p.
  rewrite IHi; try easy. lia. lia.
Qed.

Lemma assign_hr_cancel: forall n x b f, 
        (forall i, b <= i < b+ n -> nor_mode f (x,i)) ->
        assign_h_r (assign_h f x b n) x b n = f.
Proof.
  intros.
  apply functional_extensionality. intros.
  destruct x0. bdestruct (x =? v). subst.
  bdestruct (n0 <? b).
  rewrite assign_h_r_lt_same by easy. 
  rewrite assign_h_lt_same by easy.
  easy.
  bdestruct (n0 <? b+n).
  rewrite assign_hr_cancel_aux ; try lia. easy.
  apply H. lia.
  rewrite assign_h_ge; try lia.
  rewrite assign_h_r_ge; try lia.
  easy.
  rewrite assign_h_out; iner_p.
  rewrite assign_h_r_out; iner_p. easy.
Qed.


Lemma assign_rh_cancel_aux: forall i j n x b f, i <= n -> b <= j < b + i ->
        phi_mode f (x,j) ->
      (forall j, b <= j < b + n -> (forall i, 0 < i -> get_snd_r f (x,j) i = false )) ->
        assign_h (assign_h_r f x b n) x b i (x,j) = f (x,j).
Proof.
  induction i;intros;simpl.
  lia.
  bdestruct (j =? b + i). subst.
  rewrite eupdate_index_eq.
  rewrite assign_h_hit with (size := b+n); try lia.
  unfold phi_mode in *.
  specialize (H2 (b+i)).
  unfold up_h, get_snd_r in *.
  destruct (f (x,b+i)) eqn:eq1. easy. destruct (r 0) eqn:eq2.
  assert ((rotate allfalse 1) = r).
  apply functional_extensionality. intros.
  destruct x0.
  rewrite rotate_1_0; try easy.
  unfold rotate,addto. bdestruct (S x0 <? 1). lia.
  rewrite H2 by lia. easy.
  rewrite H3. easy.
  assert (allfalse = r).
  apply functional_extensionality. intros.
  destruct x0. rewrite eq2. easy.
  rewrite H2 by lia. easy.
  rewrite H3. easy.
  rewrite eupdate_index_neq; iner_p.
  rewrite IHi; try easy. lia. lia.
Qed.

Lemma assign_rh_cancel: forall n x b f, 
        (forall i, b <= i < b+ n -> phi_mode f (x,i)) ->
      (forall j, b <= j < b + n -> (forall i, 0 < i -> get_snd_r f (x,j) i = false )) ->
        assign_h (assign_h_r f x b n) x b n = f.
Proof.
  intros.
  apply functional_extensionality. intros.
  destruct x0. bdestruct (x =? v). subst.
  bdestruct (n0 <? b).
  rewrite assign_h_r_lt_same by easy. 
  rewrite assign_h_lt_same by easy.
  easy.
  bdestruct (n0 <? b+n).
  rewrite assign_rh_cancel_aux ; try lia. easy.
  apply H. lia. easy.
  rewrite assign_h_ge; try lia.
  rewrite assign_h_r_ge; try lia.
  easy.
  rewrite assign_h_out; iner_p.
  rewrite assign_h_r_out; iner_p. easy.
Qed.


Lemma phi_to_nor_modes: forall x b size aenv f, aenv x >= size ->
        phi_modes f x size -> nor_modes (exp_sem aenv (RQFT x b) f) x size.
Proof.
  intros.
  unfold phi_modes, nor_modes in *.
  intros.
  simpl.
  unfold turn_rqft.
  apply H0 in H1 as eq1.
  unfold phi_mode,nor_mode in *.
  bdestruct (b <=? i).
  rewrite assign_h_r_hit with (size := aenv x); try lia.
  rewrite assign_seq_ge ; try easy.
  unfold up_h. destruct (f (x,i)).
  1-2: easy.
  rewrite assign_h_r_lt_same; try lia.
  rewrite assign_seq_lt by lia.
  easy.
Qed.

Lemma rqft_start_phi_modes : forall aenv tenv tenv' x b f, well_typed_oexp aenv tenv (RQFT x b) tenv'
        -> right_mode_env aenv tenv f -> phi_modes f x (aenv x).
Proof.
  intros. inv H. inv H1.
  unfold right_mode_env in H0.
  unfold phi_modes. intros.
  specialize (H0 (Phi b) (x,i)). simpl in H0. 
  specialize (H0 H H5). inv H0.
  unfold phi_mode. rewrite <- H4. easy.
Qed.

Lemma sr_rotate'_lt_1
     : forall (n size : nat) (f : posi -> val) x i,
       i < n <= size ->
       sr_rotate' f x n size (x,i) = times_rotate (f (x,i)) (size - i).
Proof.
 intros. induction n.
 easy.
 simpl.
 bdestruct (n =? i). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma srr_rotate'_lt_1
     : forall (n size : nat) (f : posi -> val) x i,
       i < n <= size ->
       srr_rotate' f x n size (x,i) = times_r_rotate (f (x,i)) (size - i).
Proof.
 intros. induction n.
 easy.
 simpl.
 bdestruct (n =? i). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma addto_shift_same : forall r n size x, n < size -> addto (fun i => r (i+n)) (size - n) x = addto r size (x + n).
Proof.
  intros. unfold addto.
  unfold cut_n, fbrev.
  bdestruct (x <? size - n). bdestruct (x + n <? size). 
  assert ((size - 1 - (x + n)) = (size - n - 1 - x)) by lia. rewrite H2.
  unfold sumfb.
  bdestruct (size - n - 1 - x <? size - n).
  bdestruct (size - n - 1 - x <? size).
  assert ((size - n - 1 - (size - n - 1 - x) + n) = (size - 1 - (size - n - 1 - x))) by lia.
  rewrite H5.
  rewrite carry_lt_same with (n:= size - n) (g := (fun i : nat =>
    if i <? size
    then if i <? size then r (size - 1 - i) else r i
    else allfalse i)); try lia. easy.
  intros.
  bdestruct (i <? size - n).
  bdestruct (i <? size).
  assert (size - n - 1 - i + n = size - 1 - i) by lia. rewrite H9. easy.
  1-5:lia.
  bdestruct (x + n <? size). lia. easy.
Qed.

Lemma sumfb_lt_same : forall m n f g h h' b, m < n -> (forall i, i < n -> f i = g i)
               -> (forall i, i < n -> h i = h' i) -> sumfb b f h m = sumfb b g h' m.
Proof.
 intros. unfold sumfb.
 rewrite  carry_lt_same_1 with (n:= n) (g:=g) (h' := h'); try lia.
 rewrite H0 by lia. rewrite H1 by lia. easy.
 easy. easy.
Qed.


Lemma addto_n_shift_same : forall r n size x, n < size -> addto_n (fun i => r (i+n)) (size - n) x = addto_n r size (x + n).
Proof.
  intros. unfold addto_n.
  unfold cut_n, fbrev.
  bdestruct (x <? size - n). bdestruct (x + n <? size). 
  assert ((size - 1 - (x + n)) = (size - n - 1 - x)) by lia. rewrite H2.
  rewrite sumfb_lt_same with (n:= size - n) (g:= (fun i : nat =>
   if i <? size
   then if i <? size then r (size - 1 - i) else r i
   else allfalse i)) (h' := (negatem size (nat2fb 0))); try lia. easy.
  intros. 
  bdestruct (i <? size - n).
  bdestruct (i <? size).
  assert ((size - n - 1 - i + n) = (size - 1 - i)) by lia. rewrite H6. easy. lia. lia.
  intros.
  rewrite nat2fb_0. unfold negatem.
  bdestruct (i <? size - n).
  bdestruct (i <? size). easy.
  1-3:lia.
  bdestruct (x + n <? size). lia. easy.
Qed.

Lemma get_r_qft_lshift : forall f x m n, m < n -> (forall i, n <= i -> get_r_qft f x i = false) ->
            (forall i, n - m <= i -> lshift_fun (get_r_qft f x) m i = false).
Proof.
  intros.
  unfold lshift_fun.
  apply H0. lia.
Qed. 


Lemma sr_rotate'_get_snd_r_ge : forall n i size f x, n <= i -> n <= size -> 
         get_snd_r (sr_rotate' f x n size) (x,i) = get_snd_r f (x,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. lia. iner_p.
Qed.

Lemma sr_rotate'_get_snd_r_out : forall n i size f x x0, n <= size -> x <> x0 -> 
         get_snd_r (sr_rotate' f x n size) (x0,i) = get_snd_r f (x0,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. iner_p.
Qed.

Lemma srr_rotate'_get_snd_r_ge : forall n i size f x, n <= i -> n <= size -> 
         get_snd_r (srr_rotate' f x n size) (x,i) = get_snd_r f (x,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. lia. iner_p.
Qed.

Lemma srr_rotate'_get_snd_r_out : forall n i size f x x0, n <= size -> x <> x0 -> 
         get_snd_r (srr_rotate' f x n size) (x0,i) = get_snd_r f (x0,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. iner_p.
Qed.

Lemma qft_gt_exp_trans : 
    forall e f aenv tenv tenv', qft_gt aenv tenv f -> well_typed_oexp aenv tenv e tenv'
            -> right_mode_env aenv tenv f -> exp_WF aenv e -> qft_gt aenv tenv' (exp_sem aenv e f).
Proof.
  induction e; intros; simpl.
  inv H0. easy.
  inv H0.
  unfold qft_gt in *. intros.
  destruct p.
  bdestruct (v =? x). subst. inv H3. simpl in *.
  apply mapsto_always_same with (v1 := (Phi b)) in H6. inv H6. easy.
  apply H in H0. destruct H0.
  split. intros.
  unfold get_r_qft in *.
  rewrite eupdate_index_neq by iner_p. apply H0. easy.
  intros.
  unfold get_snd_r in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite H5; try easy.
  inv H0. easy. inv H2.
  destruct (get_cua (f p)). apply IHe with (tenv := tenv') (tenv' := tenv') ; try easy. easy.
  inv H0. inv H3. inv H2.
  unfold qft_gt in *. intros.
  destruct p.
  bdestruct (v =? x). subst. simpl in *.
  apply mapsto_always_same with (v1 := (Phi b)) in H5. inv H5. easy.
  apply H in H0. destruct H0.
  split. intros.
  unfold get_r_qft in *.
  rewrite eupdate_index_neq by iner_p. apply H0. easy.
  intros.
  unfold get_snd_r in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite H4; try easy.
  inv H0. inv H3. inv H2.
  unfold qft_gt in *. intros.
  destruct p.
  bdestruct (v =? x). subst. simpl in *.
  apply mapsto_always_same with (v1 := (Phi b)) in H5. inv H5. easy.
  apply H in H0. destruct H0.
  split. intros.
  unfold get_r_qft in *.
  rewrite eupdate_index_neq by iner_p. apply H0. easy.
  intros.
  unfold get_snd_r in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite H4; try easy.
  inv H0. inv H3.
  unfold qft_gt in *. intros.
  bdestruct (x =? x0). subst.
  apply mapsto_always_same with (v1 := (Phi b)) in H0; try easy. inv H0.
  split. intros.
  apply H in H6 as eq1. destruct eq1.
  unfold get_r_qft in *.
  unfold sr_rotate.
  rewrite sr_rotate'_lt_1; try lia.
  specialize (H3 i H0).
  unfold right_mode_env in H1.
  specialize (H1 (Phi b0) (x0,0)). simpl in H1. inv H2.
  apply H1 in H6; try lia. inv H6.
  unfold times_rotate.
  assert ((f (@pair Env.key nat x0 O)) = (f (@pair var nat x0 O))) by easy.
  rewrite H2 in *.
  rewrite <- H9 in *. unfold rotate,addto.
  bdestruct (i <? S q - 0). lia. easy.
  intros.
  apply H in H6 as eq1. destruct eq1.
  unfold sr_rotate.
  rewrite sr_rotate'_get_snd_r_ge; try easy.
  rewrite H5; try easy. lia.
  split. intros.
  apply H in H0 as eq1. destruct eq1.
  unfold get_r_qft in *. intros.
  unfold sr_rotate.
  rewrite sr_rotate'_irrelevant; try lia.
  apply H5. lia. iner_p.
  intros.
  unfold sr_rotate.
  rewrite sr_rotate'_get_snd_r_out; try lia.
  apply H in H0. destruct H0. rewrite H8. easy. easy. easy.
  inv H0. inv H3.
  unfold qft_gt in *. intros.
  bdestruct (x =? x0). subst.
  apply mapsto_always_same with (v1 := (Phi b)) in H0; try easy. inv H0.
  split. intros.
  apply H in H6 as eq1. destruct eq1.
  unfold get_r_qft in *.
  unfold srr_rotate.
  rewrite srr_rotate'_lt_1; try lia.
  specialize (H3 i H0).
  unfold right_mode_env in H1.
  specialize (H1 (Phi b0) (x0,0)). simpl in H1. inv H2.
  apply H1 in H6; try lia. inv H6.
  unfold times_r_rotate.
  assert ((f (@pair Env.key nat x0 O)) = (f (@pair var nat x0 O))) by easy.
  rewrite H2 in *.
  rewrite <- H9 in *. unfold r_rotate,addto_n.
  bdestruct (i <? S q - 0). lia. easy.
  intros.
  apply H in H6 as eq1. destruct eq1.
  unfold srr_rotate.
  rewrite srr_rotate'_get_snd_r_ge; try easy.
  rewrite H5; try easy. lia.
  split. intros.
  apply H in H0 as eq1. destruct eq1.
  unfold get_r_qft in *. intros.
  unfold srr_rotate.
  rewrite srr_rotate'_irrelevant; try lia.
  apply H5. lia. iner_p.
  intros.
  unfold srr_rotate.
  rewrite srr_rotate'_get_snd_r_out; try lia.
  apply H in H0. destruct H0. rewrite H8. easy. easy. easy.
  inv H0. inv H3. inv H2.
  unfold qft_gt in *. intros.
  bdestruct (x0 =? x). subst.
  apply mapsto_always_same with (v2:=Nor) in H0; try easy.
  apply H in H0 as eq1. destruct eq1. split. intros.
  unfold lshift,get_r_qft in *.
  rewrite lshift'_irrelevant by iner_p. apply H4; try easy.
  intros.
  unfold get_snd_r in *. unfold lshift.
  rewrite lshift'_irrelevant by iner_p. 
  rewrite H6; try easy.
  inv H0. inv H3. inv H2.
  unfold qft_gt in *. intros.
  bdestruct (x0 =? x). subst.
  apply mapsto_always_same with (v2:=Nor) in H0; try easy.
  apply H in H0 as eq1. destruct eq1. split. intros.
  unfold rshift,get_r_qft in *.
  rewrite rshift'_irrelevant by iner_p. apply H4; try easy.
  intros.
  unfold get_snd_r in *. unfold rshift.
  rewrite rshift'_irrelevant by iner_p. 
  rewrite H6; try easy.
  inv H0. inv H3. inv H2.
  unfold qft_gt in *.
  intros.
  bdestruct (x0 =? x). subst.
  apply mapsto_always_same with (v2:=Nor) in H0; try easy.
  apply H in H0 as eq1. destruct eq1.
  split. intros.
  unfold get_snd_r,reverse,get_r_qft in *.
  simpl in *.
  bdestruct (x0 =? x). lia. simpl. apply H4. lia.
  intros.
  unfold get_snd_r,reverse in *.
  simpl in *.
  bdestruct (x0 =? x). lia. simpl. apply H6. lia. easy.
  inv H0. inv H3. inv H2.
  unfold qft_gt in *. intros.
  bdestruct (x0 =? x). subst.
  split. intros.
  apply mapsto_equal with (s2 := (Env.add x (Phi b) tenv)) in H0 as eq1; try easy.
  apply mapsto_add1 in eq1. inv eq1.
  unfold right_mode_env in H1. specialize (H1 Nor (x,0)).
  simpl in *. specialize (H1 H6 H7). inv H1.
  unfold turn_qft,get_r_qft in *.
  rewrite assign_h_lt_same; try lia.
  rewrite assign_r_lt; try lia.
  rewrite lshift_fun_0.
  unfold up_qft.
  rewrite <- H3.
  unfold get_cus. bdestruct (i <? b). lia.
  easy.
  intros.
  apply mapsto_equal with (s2 := (Env.add x (Phi b) tenv)) in H0 as eq1; try easy.
  apply mapsto_add1 in eq1. inv eq1.
  unfold turn_qft,get_snd_r in *.
  unfold right_mode_env in H1. specialize (H1 Nor (x,j)).
  simpl in *. apply H1 in H7 ; try lia. inv H7.
  rewrite assign_h_hit with (size := aenv x); try lia. unfold up_h.
  rewrite assign_r_ge; try lia.
  rewrite <- H8. destruct b0.
  unfold rotate,addto. bdestruct (i <? 1). lia. easy. easy.
  apply mapsto_equal with (s2 := (Env.add x (Phi b) tenv)) in H0 as eq1; try easy.
  apply Env.add_3 in eq1. apply H in eq1 as eq2. destruct eq2.
  split. intros.
  unfold get_r_qft,turn_qft in *.
  rewrite assign_h_out; iner_p.
  rewrite assign_r_out; iner_p. apply H3. easy.
  intros.
  unfold get_snd_r,turn_qft in *.
  rewrite assign_h_out; iner_p.
  rewrite assign_r_out; iner_p. apply H8. easy. easy. lia.
  inv H0. inv H3. inv H2.
  unfold qft_gt in *. intros.
  bdestruct (x0 =? x). subst.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H0 as eq1; try easy.
  apply mapsto_add1 in eq1. inv eq1.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H0 as eq1; try easy.
  apply Env.add_3 in eq1.
  apply H in eq1 as eq2. destruct eq2.
  split. intros.
  unfold turn_rqft,get_r_qft in *.
  rewrite assign_h_out; iner_p.
  rewrite assign_seq_out; iner_p. apply H3. easy.
  intros.
  unfold get_snd_r,turn_rqft in *.
  rewrite assign_h_r_out; iner_p.
  rewrite assign_seq_out; iner_p. apply H8. easy. easy. lia.
  inv H0. inv H3. inv H2.
  specialize (IHe1 f aenv tenv env' H H6 H1 H4).
  apply IHe2 with (tenv:=env') (tenv' := tenv') ; try easy.
  apply well_typed_right_mode_pexp with (tenv:=tenv); easy.
Qed.

Lemma qft_gt_put_cu_same : 
    forall f c v aenv tenv, qft_gt aenv tenv f
                 -> qft_gt aenv tenv (f[c |-> put_cu (f c) v]).
Proof.
  intros. 
  unfold qft_gt in *. intros.
  unfold put_cu,get_r_qft in *.
  destruct c.
  simpl in *.
  specialize (H x b H0). destruct H.
  split. intros. specialize (H i H2).
  bdestruct ((v0, n) ==? (x,0)). inv H3.
  rewrite eupdate_index_eq.
  destruct (f (x,0)) eqn:eq1.
  assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy. 
  rewrite H3 in *. rewrite eq1 in *. easy.
  assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy. 
  rewrite H3 in *. rewrite eq1 in *. easy.
  assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy. 
  rewrite H4 in *.
  rewrite eupdate_index_neq. apply H. easy.
  intros. specialize (H1 j H2 i H3).
  unfold get_snd_r in *.
  bdestruct ((v0, n) ==? (x,j)). inv H4.
  rewrite eupdate_index_eq.
  destruct (f (x,j)) eqn:eq1.
  assert ((@pair Env.key nat x j) = (@pair var nat x j)) by easy. 
  rewrite H4 in *. rewrite eq1 in *. easy.
  assert ((@pair Env.key nat x j) = (@pair var nat x j)) by easy. 
  rewrite H4 in *. rewrite eq1 in *. easy.
  assert ((@pair Env.key nat x j) = (@pair var nat x j)) by easy. 
  rewrite H5 in *.
  rewrite eupdate_index_neq. apply H1. easy.
Qed.

Lemma qft_gt_put_cu_same_1 : 
    forall f f' c v aenv tenv, qft_gt aenv tenv f -> nor_mode f' c
                 -> qft_gt aenv tenv (f[c |-> put_cu (f' c) v]).
Proof.
  intros. 
  unfold qft_gt in *. intros.
  unfold put_cu,get_r_qft in *.
  destruct c.
  simpl in *.
  specialize (H x b H1). destruct H.
  split. intros. specialize (H i H3).
  bdestruct ((v0, n) ==? (x,0)). inv H4.
  rewrite eupdate_index_eq.
  unfold nor_mode in H0.
  destruct (f' (x,0)) eqn:eq1.
  assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy. 
  rewrite H4 in *. rewrite eq1 in *. easy.
  assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy. 
  rewrite H4 in *. rewrite eq1 in *. easy.
  assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy. 
  rewrite H5 in *.
  rewrite eupdate_index_neq. apply H. easy.
  intros. specialize (H2 j H3 i H4).
  unfold get_snd_r in *.
  bdestruct ((v0, n) ==? (x,j)). inv H5.
  rewrite eupdate_index_eq.
  unfold nor_mode in H0.
  destruct (f' (x,j)) eqn:eq1.
  assert ((@pair Env.key nat x j) = (@pair var nat x j)) by easy. 
  rewrite H5 in *. rewrite eq1 in *. easy.
  assert ((@pair Env.key nat x j) = (@pair var nat x j)) by easy. 
  rewrite H5 in *. rewrite eq1 in *. easy.
  assert ((@pair Env.key nat x j) = (@pair var nat x j)) by easy. 
  rewrite H6 in *. 
  rewrite eupdate_index_neq. apply H2. easy.
Qed.


Lemma qft_gt_put_cus_same : 
    forall f x g n aenv tenv, qft_gt aenv tenv f -> nor_modes f x n
                 -> qft_gt aenv tenv (put_cus f x g n).
Proof.
  intros. 
  unfold qft_gt in *. intros.
  unfold put_cus,get_r_qft in *.
  simpl in *. 
  split. intros.
  bdestruct (x0 =? x). subst.
  bdestruct (0 <? n).
  unfold put_cu.
  unfold nor_modes in H0. specialize (H0 0 H3).
  unfold nor_mode in H0.
  destruct (f (x,0)) eqn:eq1. easy. lia.
  specialize (H x b H1). destruct H.
  apply H; try easy.
  specialize (H x0 b H1). destruct H.
  apply H; try easy.
  intros.
  specialize (H x0 b H1). destruct H.
  specialize (H4 j H2 i H3).
  unfold get_snd_r in *. simpl.
  bdestruct (x0 =? x). subst.
  bdestruct (j <? n). 
  unfold nor_modes in H0. specialize (H0 j H5).
  unfold nor_mode in H0.
  destruct (f (x,j)) eqn:eq1.
  unfold put_cu.
  assert ((f (@pair Env.key nat x j)) = (f (@pair var nat x j))) by easy.
  rewrite H6.
  rewrite eq1. easy.
  lia. easy.
  easy.
Qed.
(*
Lemma assign_r_cover_full : forall n f x g aenv tenv,
            0 < aenv x -> n <= aenv x ->
            Env.MapsTo x (Phi n) tenv -> qft_uniform aenv tenv f 
           -> qft_gt aenv tenv f -> right_mode_env aenv tenv f ->
            assign_r (assign_seq f x g n) x (get_r_qft f x) n = f.
Proof.
  intros. 
  assert (phi_modes f x (aenv x)).
  apply type_phi_modes with (b := n) (env := tenv); try easy.
  apply functional_extensionality. intros.
  destruct x0.
  bdestruct (v =? x). subst.
  bdestruct (n0 <? aenv x).
  rewrite assign_r_covers; try easy.
  unfold qft_uniform in *.
  rewrite H2; try easy.
  rewrite assign_r_ge by lia.
  rewrite assign_seq_ge by lia. easy.
  rewrite assign_r_out by iner_p.
  rewrite assign_seq_out by iner_p. easy.
Qed.
*)

Lemma qft_uniform_sr_rotate : forall n i b size f x, i < n <= b -> b <= size -> phi_modes f x size ->
           get_snd_r f (x, i) = lshift_fun (get_r_qft f x) i
     -> get_snd_r (sr_rotate' f x n b) (x, i) = lshift_fun (get_r_qft (sr_rotate' f x n b) x) i.
Proof.
 induction n;intros;simpl. lia.
 bdestruct (i =? n). subst.
 unfold get_snd_r,get_r_qft.
 bdestruct (n =? 0). subst.
 rewrite eupdate_index_eq.
 unfold lshift_fun.
 apply functional_extensionality. intros.
 rewrite plus_0_r. easy.
 rewrite eupdate_index_eq.
 rewrite eupdate_index_neq by iner_p.
 rewrite sr_rotate'_lt_1 by lia.
 unfold lshift_fun.
 unfold get_snd_r,get_r_qft,lshift_fun in H2.
 apply functional_extensionality. intros.
 unfold times_rotate.
 unfold phi_modes in H1.
 assert (eq1 := H1).
 assert (n < size) by lia. assert (0 < size) by lia.
 specialize (H1 n H4).
 specialize (eq1 0 H5).
 unfold phi_mode in *.
 destruct (f (x, n)). lia.
 destruct (f (x,0)). lia.
 subst. unfold rotate.
 rewrite addto_shift_same; try lia.
 assert ((b - 0)  = b) by lia. rewrite H2. easy.
 apply functional_extensionality. intros.
 unfold get_snd_r,get_r_qft in *.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn with (size := size); try easy. lia.
Qed.

Lemma qft_uniform_srr_rotate : forall n i b size f x, i < n <= b -> b <= size -> phi_modes f x size ->
           get_snd_r f (x, i) = lshift_fun (get_r_qft f x) i
     -> get_snd_r (srr_rotate' f x n b) (x, i) = lshift_fun (get_r_qft (srr_rotate' f x n b) x) i.
Proof.
 induction n;intros;simpl. lia.
 bdestruct (i =? n). subst.
 unfold get_snd_r,get_r_qft.
 bdestruct (n =? 0). subst.
 rewrite eupdate_index_eq.
 unfold lshift_fun.
 apply functional_extensionality. intros.
 rewrite plus_0_r. easy.
 rewrite eupdate_index_eq.
 rewrite eupdate_index_neq by iner_p.
 rewrite srr_rotate'_lt_1.
 unfold lshift_fun.
 unfold get_snd_r,get_r_qft,lshift_fun in H2.
 apply functional_extensionality. intros.
 unfold times_r_rotate.
 unfold phi_modes in H1.
 assert (eq1 := H1).
 assert (n < size) by lia. assert (0 < size) by lia.
 specialize (H1 n H4).
 specialize (eq1 0 H5).
 unfold phi_mode in *.
 destruct (f (x, n)). lia.
 destruct (f (x,0)). lia.
 subst. unfold r_rotate.
 rewrite addto_n_shift_same; try lia.
 assert ((b - 0)  = b) by lia. rewrite H2. easy. lia.
 unfold get_snd_r,get_r_qft in *.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn with (size := size); try easy. lia.
Qed.


(* Type soundness for QFT-uniformity. *)
Lemma qft_uniform_exp_trans : 
    forall e f aenv tenv tenv', at_match aenv tenv ->
            qft_uniform aenv tenv f -> well_typed_oexp aenv tenv e tenv'
            -> right_mode_env aenv tenv f -> qft_uniform aenv tenv' (exp_sem aenv e f).
Proof.
  induction e; intros; simpl.
  inv H1. easy.
  inv H1.
  unfold qft_uniform in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  simpl in *. inv H3.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  simpl in *.
  unfold get_snd_r,get_r_qft in *.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite H0 with (b := b); try easy.
  inv H1. inv H3.
  destruct (get_cua (f p)) eqn:eq1.
  apply IHe with (tenv := tenv'); try easy. easy.
  inv H1.
  unfold qft_uniform in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  inv H3. simpl in *.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  unfold get_snd_r,get_r_qft in *.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite H0 with (b := b); try easy.
  inv H1.
  unfold qft_uniform in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  inv H3.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  unfold get_snd_r,get_r_qft in *.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite H0 with (b := b); try easy.
  inv H1.
  unfold qft_uniform in *. intros.
  unfold sr_rotate.
  bdestruct (x =? x0). subst.
  bdestruct (i <? S q).
  rewrite qft_uniform_sr_rotate with (size := b). easy. lia.
  inv H3.
  apply mapsto_always_same with (v2:=(Phi b)) in H9; try easy. inv H9. lia.
  unfold right_mode_env in H2.
  unfold phi_modes. intros. inv H3.
  unfold at_match in *. apply H in H10 as X1.
  specialize (H2 (Phi b) (x0,i0)).
  simpl in H2.
  apply H2 in H1; try easy.
  inv H1. unfold phi_mode.
  assert ((f (@pair Env.key nat x0 i0)) = (f (@pair var nat x0 i0))) by easy.
  rewrite H1 in *. rewrite <- H8. easy.
  apply mapsto_always_same with (v2:=(Phi b)) in H10; try easy. inv H10. lia.
  rewrite H0 with (b := b); try easy.
  rewrite sr_rotate'_get_snd_r_ge; try lia.
  rewrite H0 with (b := b); try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  inv H3.
  unfold at_match in *. apply H in H9 as X1.
  apply mapsto_always_same with (v2:=(Phi b)) in H9; try easy.
  inv H9.
  rewrite sr_rotate'_lt_1; try lia.
  unfold right_mode_env in H2.
  specialize (H2 (Phi b) (x0,0)).
  simpl in *.
  apply H2 in H1 as eq1 ; try lia.
  inv eq1.
  assert ((f (@pair Env.key nat x0 0)) = (f (@pair var nat x0 0))) by easy.
  rewrite H3 in *. rewrite <- H7.
  unfold times_rotate, rotate,addto.
  bdestruct (x + i <? S q). lia. easy. simpl.
  unfold get_snd_r,get_r_qft in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  rewrite sr_rotate'_irrelevant; iner_p.
  rewrite sr_rotate'_irrelevant; iner_p.
  rewrite H0 with (b := b); try easy.
  inv H1. inv H3.
  unfold at_match in *. apply H in H6 as X1.
  unfold qft_uniform in *. intros.
  unfold srr_rotate.
  bdestruct (x =? x0). subst.
  bdestruct (i <? S q).
  rewrite qft_uniform_srr_rotate with (size := aenv x0). easy. lia. lia.
  apply mapsto_always_same with (v2:=(Phi b)) in H1; try easy.
  inv H1.
  unfold right_mode_env in H2.
  unfold phi_modes. intros.
  specialize (H2 (Phi b) (x0,i0)).
  simpl in H2. assert (i0 < aenv x0) by lia.
  apply H2 in H6; try easy.
  inv H6. unfold phi_mode.
  assert ((f (@pair Env.key nat x0 i0)) = (f (@pair var nat x0 i0))) by easy.
  rewrite H6 in *. rewrite <- H10. lia.
  rewrite H0 with (b := b); try easy. lia.
  rewrite srr_rotate'_get_snd_r_ge; try lia.
  rewrite H0 with (b := b); try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  apply mapsto_always_same with (v2:=(Phi b)) in H1; try easy.
  inv H1.
  rewrite srr_rotate'_lt_1; try lia.
  unfold right_mode_env in H2.
  specialize (H2 (Phi b) (x0,0)).
  apply H2 in H6.
  inv H6.
  assert ((f (@pair Env.key nat x0 0)) = (f (@pair var nat x0 0))) by easy.
  rewrite H1 in *. rewrite <- H8.
  unfold times_r_rotate, r_rotate,addto_n.
  bdestruct (x + i <? S q - 0). lia. easy. simpl. lia.
  apply mapsto_always_same with (v2:=(Phi b)) in H1; try easy.
  inv H1. lia.
  rewrite srr_rotate'_get_snd_r_out; try lia.
  rewrite H0 with (b := b0); try easy.
  unfold get_r_qft.
  rewrite srr_rotate'_irrelevant; try lia. easy.
  iner_p. 
  inv H1. inv H3.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  assert (get_snd_r (lshift f x (aenv x)) (x0, i) = get_snd_r f (x0,i)).
  unfold get_snd_r,lshift. rewrite lshift'_irrelevant. easy. easy.
  rewrite H6. rewrite H0 with (b := b); try easy.
  assert ((get_r_qft (lshift f x (aenv x)) x0) = get_r_qft f x0).
  unfold get_r_qft,lshift.
  rewrite lshift'_irrelevant. easy. easy.
  rewrite H7. easy.
  inv H1. inv H3.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  assert (get_snd_r (rshift f x (aenv x)) (x0, i) = get_snd_r f (x0,i)).
  unfold get_snd_r,rshift. rewrite rshift'_irrelevant. easy. easy.
  rewrite H6. rewrite H0 with (b := b); try easy.
  assert ((get_r_qft (rshift f x (aenv x)) x0) = get_r_qft f x0).
  unfold get_r_qft,rshift.
  rewrite rshift'_irrelevant. easy. easy.
  rewrite H7. easy.
  inv H1. inv H3.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  assert (get_snd_r (reverse f x (aenv x)) (x0, i) = get_snd_r f (x0,i)).
  unfold get_snd_r,reverse.
  simpl. bdestruct (x0 =? x). lia. simpl. easy.
  rewrite H6. rewrite H0 with (b := b); try easy.
  assert ((get_r_qft (reverse f x (aenv x)) x0) = get_r_qft f x0).
  unfold get_r_qft,reverse.
  simpl. bdestruct (x0 =? x). lia. simpl. easy.
  rewrite H7. easy.
  apply (at_match_trans aenv tenv tenv' (QFT x b) H1) in H.
  inv H1. inv H3.
  unfold qft_uniform in *. intros.
  bdestruct (x0 =? x). subst. 
  unfold turn_qft,get_snd_r.
  apply mapsto_equal with (s2 := (Env.add x (Phi b) tenv)) in H1; try easy.
  apply mapsto_add1 in H1 ; try lia. inv H1.
  rewrite assign_h_lt_same; try lia. 
  rewrite assign_r_lt; try lia.
  unfold get_r_qft.
  rewrite assign_h_lt_same; try lia. 
  rewrite assign_r_lt; try lia.
  unfold up_qft.
  unfold right_mode_env in H2. 
  specialize (H2 Nor (x,i)) as eq1. simpl in eq1. 
  specialize (H2 Nor (x,0)) as eq2. simpl in eq2.
  unfold at_match in H.
  assert (Env.MapsTo x (Phi b) tenv') as X2.
  apply mapsto_equal with (s1 := (Env.add x (Phi b) tenv)); try easy.
  apply Env.add_1. easy.
  apply H in X2 as X3.
  apply eq1 in H7 as eq3; try lia.
  assert (0 < aenv x) by lia.
  specialize (eq2 H1 H7).
  inv eq3. inv eq2.
  rewrite lshift_fun_0. easy.
  apply mapsto_equal with (s2 := (Env.add x (Phi b) tenv)) in H1; try easy.
  apply Env.add_3 in H1 ; try lia. 
  assert (get_snd_r (turn_qft f x b (aenv x)) (x0, i) = get_snd_r f (x0, i)).
  unfold get_snd_r,turn_qft.
  rewrite assign_h_out; try easy.
  rewrite assign_r_out; try easy. rewrite H6.
  rewrite H0 with (b := b0); try easy.
  unfold get_r_qft,turn_qft.
  rewrite assign_h_out; try easy.
  rewrite assign_r_out; try easy.
  unfold qft_uniform in *. intros.
  apply (at_match_trans aenv tenv tenv' (RQFT x b) H1) in H as X1.
  inv H1. inv H5.
  unfold at_match in H. apply H in H9 as X2.
  unfold qft_uniform in *. intros.
  bdestruct (x0 =? x). subst. 
  unfold turn_rqft,get_snd_r.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H3; try easy.
  apply mapsto_add1 in H3 ; try lia. inv H3.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H3; try easy.
  apply Env.add_3 in H3 ; try lia. 
  assert (get_snd_r (turn_rqft f x b (aenv x)) (x0, i) = get_snd_r f (x0, i)).
  unfold get_snd_r,turn_rqft.
  rewrite assign_h_r_out; try easy.
  rewrite assign_seq_out; try easy. rewrite H5.
  rewrite H0 with (b := b0); try easy.
  unfold get_r_qft,turn_rqft.
  rewrite assign_h_r_out; try easy.
  rewrite assign_seq_out; try easy. 
  inv H1. inv H3.
  apply (at_match_trans aenv tenv env' e1 H6) in H as X1.
  specialize (IHe1 f aenv tenv env' H H0 H6 H2).
  apply well_typed_right_mode_pexp with (e := e1) (tenv' := env') in H2; try easy.
  specialize (IHe2 (exp_sem aenv e1 f) aenv env' tenv' X1 IHe1). apply IHe2; try easy.
Qed.

Lemma qft_uniform_put_cu_same : 
    forall f c v aenv tenv, qft_uniform aenv tenv f 
                 -> qft_uniform aenv tenv (f[c |-> put_cu (f c) v]).
Proof.
 intros. unfold qft_uniform in *.
 intros. 
 destruct c.
 unfold get_snd_r,get_r_qft in *.
 bdestruct ((v0, n) ==? (x,i)). inv H2. 
 rewrite eupdate_index_eq.
 specialize (H x b H0 i H1).
 unfold put_cu.
 destruct (f (x,i)) eqn:eq1.
 assert ((@pair Env.key nat x i) = (@pair var nat x i)) by easy.
 rewrite H2 in *.
 rewrite eq1 in *.
 bdestruct (i =? 0). subst.
 rewrite eupdate_index_eq.
 rewrite eq1 in H. easy.
 rewrite eupdate_index_neq. easy. iner_p.
 assert ((@pair Env.key nat x i) = (@pair var nat x i)) by easy.
 rewrite H2 in *. 
 rewrite eq1 in *.
 bdestruct (i =? 0). rewrite H3 in *. clear H3.
 rewrite eupdate_index_eq.
 rewrite eq1 in H. easy.
 rewrite eupdate_index_neq. easy. iner_p.
 assert ((@pair Env.key nat x i) = (@pair var nat x i)) by easy.
 rewrite H3 in *.
 rewrite eupdate_index_neq. rewrite H with (b := b); try easy.
 bdestruct ((v0, n) ==? (x,0)). inv H4.
 rewrite eupdate_index_eq.
 unfold put_cu. 
 destruct (f (x,0)) eqn:eq1.
 assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy.
 rewrite H4 in *. 
 rewrite eq1 in *. easy.
 assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy.
 rewrite H4 in *. 
 rewrite eq1 in *. easy.
 assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy.
 rewrite H5 in *. 
 rewrite eupdate_index_neq. easy. easy. easy.
Qed.

Lemma qft_uniform_put_cu_same_1 : 
    forall f c1 c2 v1 v2 aenv tenv, qft_uniform aenv tenv f -> Env.MapsTo (fst c1) Nor tenv -> Env.MapsTo (fst c2) Nor tenv
                 -> qft_uniform aenv tenv (f[c2 |-> put_cu (f c2) v2][c1 |-> put_cu (f c1) v1]).
Proof.
 intros. unfold qft_uniform in *.
 intros. 
 unfold get_snd_r,get_r_qft in *.
 destruct c1. destruct c2.
 bdestruct ((k,n) ==? (k0,n0)). inv H4.
 rewrite eupdate_twice_eq.
 specialize (qft_uniform_put_cu_same f (k0,n0) v1 aenv tenv) as eq1.
 apply eq1 in H. unfold qft_uniform in H.
 specialize (H x b H2 i H3). easy.
 bdestruct ((k,n) ==? (x,i)). inv H5.
 simpl in *.
 apply mapsto_always_same with (v1 := Nor) in H2; try easy.
 rewrite eupdate_index_neq by iner_p.
 bdestruct ((k,n) ==? (x,0)). inv H6.
 apply mapsto_always_same with (v1 := Nor) in H2; try easy.
 bdestruct ((k0,n0) ==? (x,i)). inv H7.
 apply mapsto_always_same with (v1 := Nor) in H2; try easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_neq by iner_p.
 bdestruct ((k0,n0) ==? (x,0)). inv H8.
 apply mapsto_always_same with (v1 := Nor) in H2; try easy.
 rewrite eupdate_index_neq by iner_p.
 apply H with (b := b); try easy.
Qed.


Lemma qft_uniform_put_cu_same_2 : 
    forall f f' c v aenv tenv, qft_uniform aenv tenv f -> Env.MapsTo (fst c) Nor tenv ->
              right_mode_env aenv tenv f -> right_mode_env aenv tenv f' ->
                at_match aenv tenv -> qft_uniform aenv tenv (f[c |-> put_cu (f' c) v]).
Proof.
 intros. unfold qft_uniform in *.
 intros. 
 destruct c.
 unfold get_snd_r,get_r_qft in *.
 bdestruct (k =? x). subst. 
 bdestruct (n =? i). subst.
 rewrite eupdate_index_eq.
 simpl in *.
 bdestruct (i =? 0). rewrite H6 in *. clear H6.
 rewrite eupdate_index_eq.
 unfold put_cu.
 destruct (f' (x,0)) eqn:eq1. easy. unfold lshift_fun.
 apply functional_extensionality. intros. rewrite plus_0_r. easy.
 rewrite eupdate_index_neq by iner_p.
 assert (nor_mode f' (x,i)).
 unfold right_mode_env in *. 
 specialize (H2 Nor (x,i)).
 simpl in H2. apply H2 in H0. inv H0.
 unfold nor_mode. rewrite <- H7. easy.
 apply H3 in H4 as X1. lia.
 assert (nor_mode f (x,0)).
 unfold right_mode_env in *. 
 specialize (H1 Nor (x,0)).
 simpl in H1. apply H1 in H0. inv H0.
 unfold nor_mode. rewrite <- H8.  easy.
 apply H3 in H4 as X1. lia. 
 unfold nor_mode in *. 
 destruct (f (x,0)) eqn:eq1.
 assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy.
 rewrite H9 in *.
 rewrite eq1 in *.
 destruct (f' (x,i)) eqn:eq2.
 unfold put_cu. easy. easy. easy.
 bdestruct (n =? 0). subst.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_eq. 
 assert (nor_mode f' (x,0)).
 unfold right_mode_env in *. 
 specialize (H2 Nor (x,0)).
 simpl in H2. apply H2 in H0. inv H0.
 unfold nor_mode. rewrite <- H7. easy.
 apply H3 in H4. lia.
 assert (nor_mode f (x,i)).
 unfold right_mode_env in *. 
 specialize (H1 Nor (x,i)).
 simpl in H1. apply H1 in H0. inv H0.
 unfold nor_mode. rewrite <- H8.  easy.
 apply H3 in H4. lia. 
 unfold nor_mode in *. 
 destruct (f (x,i)) eqn:eq1.
 destruct (f' (x,0)) eqn:eq2.
 unfold put_cu. easy. easy. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_neq by iner_p.
 assert (nor_mode f (x,i)).
 unfold right_mode_env in *. 
 specialize (H1 Nor (x,i)).
 simpl in H1. apply H1 in H0. inv H0.
 unfold nor_mode. rewrite <- H8. easy.
 apply H3 in H4. lia.
 assert (nor_mode f (x,0)).
 unfold right_mode_env in *. 
 specialize (H1 Nor (x,0)).
 simpl in H1. apply H1 in H0. inv H0.
 unfold nor_mode. rewrite <- H9.  easy.
 apply H3 in H4. lia. 
 unfold nor_mode in *. 
 destruct (f (x,i)) eqn:eq1.
 destruct (f (x, 0)) eqn:eq2.
 assert ((@pair Env.key nat x 0) = (@pair var nat x 0)) by easy.
 rewrite H10 in *.
 rewrite eq2 in *. easy. easy. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_neq by iner_p.
 apply H with (b := b). easy. easy.
Qed.

Lemma qft_uniform_put_cus_same : 
    forall f x g n aenv tenv, qft_uniform aenv tenv f -> right_mode_env aenv tenv f ->
               at_match aenv tenv -> qft_uniform aenv tenv (put_cus f x g n).
Proof.
  intros. 
  unfold qft_uniform in *. intros.
  unfold put_cus,get_snd_r,get_r_qft in *.
  simpl in *.
  bdestruct (x0 =? x). subst.
  unfold right_mode_env in H0.
  specialize (H0 (Phi b) (x,i)) as eq1.
  simpl in eq1.
  unfold at_match in H1.
  apply H1 in H2 as Y1.
  assert (i < aenv x) as Y2 by lia.
  apply eq1 in Y2 as X1; try easy.
  specialize (H0 (Phi b) (x,0)) as eq2.
  simpl in eq2.
  apply H1 in H2 as X2.
  assert (0 < aenv x) by lia.
  specialize (eq2 H4 H2).
  bdestruct (i <? n). simpl.
  bdestruct (0 <? n).
  specialize (H x b H2 i H3).
  unfold put_cu.
  inv X1. inv eq2.
  assert ((@pair var nat x i) = (@pair Env.key nat x i)) by easy.
  rewrite H7 in *.
  rewrite <- H9 in *.
  assert ((@pair var nat x 0) = (@pair Env.key nat x 0)) by easy.
  rewrite H8 in *.
  rewrite <- H10 in *.
  easy. lia.
  bdestruct (0 <? n).
  specialize (H x b H2 i H3).
  unfold put_cu.
  inv X1. inv eq2.
  assert ((@pair var nat x i) = (@pair Env.key nat x i)) by easy.
  rewrite H7 in *.
  rewrite <- H9 in *.
  assert ((@pair var nat x 0) = (@pair Env.key nat x 0)) by easy.
  rewrite H8 in *.
  rewrite <- H10 in *. easy.
  assert (n = 0) by lia. subst.
  apply H with (b := b); try easy.
  apply H1 in H2 as X1; try easy.
  apply H with (b := b); try easy.
Qed.


Lemma nor_modes_trans: forall f x b size, b <= size -> nor_modes f x size -> nor_modes f x b.
Proof.
  intros. unfold nor_modes in *.
  intros. apply H0. lia.
Qed.

Lemma phi_modes_trans: forall f x b size, b <= size -> phi_modes f x size -> phi_modes f x b.
Proof.
  intros. unfold phi_modes in *.
  intros. apply H0. lia.
Qed.


Lemma inv_exp_correct_rev :
  forall e tenv tenv' aenv f,
    well_typed_oexp aenv tenv e tenv' -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> 
    exp_WF aenv e -> at_match aenv tenv -> exp_sem aenv (e; inv_exp e) f = f.
Proof.
  induction e; intros.
  - simpl. easy.
  - simpl.
    remember (f [p |-> exchange (f p)]) as f'.
    assert (f = f'[p |-> exchange (f' p)]).
    subst.
    rewrite eupdate_index_eq.
    rewrite eupdate_twice_eq.
    rewrite exchange_twice_same.
    rewrite eupdate_same. easy. easy.
    rewrite H5. easy.
  - specialize (typed_inv_pexp (CU p e) aenv tenv tenv' H) as eq1.
    simpl in eq1.
    assert (inv_exp (CU p e) = CU p (inv_exp e)). simpl. easy.
    rewrite H5. inv H3. inv H. inv H3.
    destruct (get_cua (f p)) eqn:eq3.
    rewrite <- two_cu_same.
    apply IHe with (tenv := tenv') (tenv' := tenv'); try easy.
    easy. easy. easy.
    inv eq1. easy.
    simpl. rewrite eq3. rewrite eq3. easy.
  - simpl.
    assert ((f [p |-> times_rotate (f p) q])
                  [p |-> times_r_rotate ((f [p |-> times_rotate (f p) q]) p) q] = f).
    rewrite eupdate_index_eq.
    rewrite eupdate_twice_eq.
    apply functional_extensionality.
    intros. 
    bdestruct (x ==? p).
    subst.
    rewrite eupdate_index_eq.
    rewrite times_rotate_same. easy.
    rewrite eupdate_index_neq. easy. nor_sym.
    rewrite H5. easy.
  - simpl.
    assert ((f [p |-> times_r_rotate (f p) q])
                  [p |-> times_rotate ((f [p |-> times_r_rotate (f p) q]) p) q] = f).
    rewrite eupdate_index_eq.
    rewrite eupdate_twice_eq.
    apply functional_extensionality.
    intros. 
    bdestruct (x ==? p).
    subst.
    rewrite eupdate_index_eq.
    rewrite times_rotate_r_same. easy.
    rewrite eupdate_index_neq. easy. nor_sym.
    rewrite H5. easy.
  - simpl.
    unfold sr_rotate,srr_rotate.
    rewrite srr_rotate_rotate. easy.
  - simpl.
    unfold sr_rotate,srr_rotate.
    rewrite sr_rotate_rotate. easy.
 - simpl.
   rewrite rl_shift_same. easy.
 - simpl.
   rewrite lr_shift_same. easy.
 - simpl.
   rewrite rev_twice_same. easy.
 - simpl. unfold turn_qft,turn_rqft. 
   apply functional_extensionality. intros.
   destruct x0.
   bdestruct (x =? v). subst.
   bdestruct (n <? b).
   rewrite assign_hr_seq_flip by easy.
   rewrite assign_hr_cancel.
   rewrite assign_seq_covers; try easy.
   apply nor_modes_trans with (size := aenv v); try easy.
   inv H3. easy.
   eapply qft_start_nor_modes. apply H. easy.
   unfold get_r_qft.
   rewrite assign_h_lt_same; try lia.
   rewrite assign_r_same_0 with (size := (aenv v)); try lia.
   rewrite get_cus_cua. easy. lia. inv H3. lia.
   eapply qft_start_nor_modes. apply H. easy.
   intros. unfold nor_mode. rewrite assign_r_ge by lia.
   inv H. inv H7.
   apply type_nor_modes with (f := f) (aenv := aenv) in H11; try easy.
   unfold nor_modes in *.
   apply H11. lia.
   bdestruct (n <? aenv v).
   rewrite assign_h_r_hit with (size := aenv v); try lia.
   rewrite assign_seq_ge by lia.
   rewrite assign_h_hit with (size := aenv v); try lia.
   rewrite assign_r_ge by lia.
   inv H. inv H7.
   apply type_nor_modes with (f := f) (aenv := aenv) in H11; try easy.
   unfold nor_modes in *. apply H11 in H6. unfold nor_mode in *.
   unfold up_h. destruct (f (v,n)). destruct b0.
   rewrite rotate_1_0. easy. easy. easy. easy.
   rewrite assign_h_r_ge by lia.
   rewrite assign_seq_ge by lia.
   rewrite assign_h_ge by lia.
   rewrite assign_r_ge by lia. easy.
   rewrite assign_h_r_out by iner_p.
   rewrite assign_seq_out by iner_p.
   rewrite assign_h_out by iner_p.
   rewrite assign_r_out by iner_p. easy.
 - simpl. unfold turn_qft,turn_rqft.
   apply functional_extensionality. intros.
   destruct x0.
   bdestruct (x =? v). subst.
   bdestruct (n <? b).
   rewrite assign_h_r_flip by easy.
   rewrite assign_rh_cancel.
   rewrite assign_r_covers; try easy.
   apply phi_modes_trans with (size :=aenv v). inv H3. easy.
   eapply rqft_start_phi_modes. apply H. easy.
   unfold qft_uniform in H1.
   inv H. inv H6. rewrite H1 with (b := b); try easy.
   unfold qft_gt in H2. 
   assert ((get_cus b
     (assign_h_r (assign_seq f v (get_r_qft f v) b) v b (aenv v - b)) v)
           = (get_r_qft f v)).
   apply functional_extensionality. intros.
   bdestruct (x <? b).
   rewrite get_cus_cua; try lia.
   rewrite assign_h_lt_same; try lia.
   rewrite assign_seq_lt; try lia.
   unfold get_cua. easy.
   unfold get_cus in *. bdestruct (x <? b). lia.
   unfold get_r_qft in *. assert (0 < b) by lia.
   specialize (H2 v b H10). destruct H2. specialize (H2 x).
   rewrite H2. easy. lia.
   rewrite H. easy.
   intros.
   inv H. inv H7. unfold right_mode_env in H0.
   specialize (H0 (Phi b) (v,i)). simpl in *.
   apply H0 in H11 as eq1; try lia. inv eq1.
   unfold phi_mode in *.
   rewrite assign_seq_ge; try lia. rewrite <- H. easy.
   intros.
   unfold qft_gt in H2.
   inv H. inv H8. specialize (H2 v b H12). destruct H2.
   specialize (H2 j).
   unfold get_snd_r in *.
   rewrite assign_seq_ge; try lia.
   rewrite H2. easy. lia. lia.
   rewrite assign_h_r_flip by easy.
   rewrite assign_rh_cancel.
   rewrite assign_r_ge; try lia.
   rewrite assign_seq_ge; try lia. easy.
   intros.
   inv H. inv H7. unfold right_mode_env in H0.
   specialize (H0 (Phi b) (v,i)). simpl in *.
   apply H0 in H11 as eq1; try lia. inv eq1.
   unfold phi_mode in *.
   rewrite assign_seq_ge; try lia. rewrite <- H. easy.
   intros.
   unfold qft_gt in H2.
   inv H. inv H8. specialize (H2 v b H12). destruct H2.
   specialize (H2 j).
   unfold get_snd_r in *.
   rewrite assign_seq_ge; try lia.
   rewrite H2. easy. lia. lia.
   rewrite assign_h_out; try iner_p.
   rewrite assign_r_out; try iner_p.
   rewrite assign_h_r_out; try iner_p.
   rewrite assign_seq_out; try iner_p.
   easy.
 - assert (inv_exp (e1; e2) = inv_exp e2; inv_exp e1). simpl. easy.
   rewrite H5.
   rewrite pexp_sem_assoc.
   assert (exp_sem aenv (e1; (e2; (inv_exp e2; inv_exp e1))) f
             = exp_sem aenv (e2 ; (inv_exp e2 ; inv_exp e1)) (exp_sem aenv (e1) f)).
   simpl. easy.
   rewrite H6.
   rewrite <- pexp_sem_assoc.
   assert ( forall f', exp_sem aenv ((e2; inv_exp e2); inv_exp e1) f'
            = exp_sem aenv (inv_exp e1) (exp_sem aenv ((e2; inv_exp e2)) f')).
   intros. simpl. easy.
   rewrite H7.
   inv H. inv H8.
   rewrite (IHe2 env' tenv' aenv).
   assert (exp_sem aenv (inv_exp e1) (exp_sem aenv e1 f) = exp_sem aenv (e1 ; inv_exp e1) f).
   simpl. easy.
   rewrite H.
   rewrite (IHe1 tenv env'). easy.
   1-4:easy. inv H3. easy. easy. easy.
   apply well_typed_right_mode_pexp with (tenv := tenv) (tenv' := env'). easy. easy.
   apply qft_uniform_exp_trans with (tenv := tenv); try easy.
   apply qft_gt_exp_trans with (tenv := tenv); try easy. inv H3. easy. inv H3. easy.
   apply at_match_trans with (tenv := tenv) (e := e1); try easy.
Qed.

Lemma exp_WF_inv : forall aenv e, exp_WF aenv e -> exp_WF aenv (inv_exp e).
Proof.
   intros. induction e; eauto.
   inv H. simpl. constructor. easy. apply IHe. easy.
   simpl. inv H. constructor. easy.
   simpl. inv H. constructor. easy.
   simpl. inv H. constructor. easy.
   simpl. inv H. constructor. easy.
   simpl. inv H. constructor. easy.
   simpl. inv H. constructor. easy.
   simpl. inv H. constructor. easy. easy.
   simpl. inv H. constructor. easy. easy.
   simpl. constructor. apply IHe2. inv H. easy.
   apply IHe1. inv H. easy.
Qed.

Lemma inv_exp_correct :
  forall e tenv tenv' aenv f,
    well_typed_oexp aenv tenv e tenv' -> right_mode_env aenv tenv' f ->
    qft_uniform aenv tenv' f -> qft_gt aenv tenv' f
    -> exp_WF aenv e -> at_match aenv tenv -> exp_sem aenv (inv_exp e;e) f = f.
Proof.
  intros.
  assert ((inv_exp e;e) = inv_exp e; inv_exp (inv_exp e)).
  rewrite inv_exp_involutive. easy.
  rewrite H5.
  apply (inv_exp_correct_rev (inv_exp e) tenv' tenv aenv).
  apply typed_inv_pexp. easy.
  1-3:assumption. simpl. apply exp_WF_inv. easy.
  apply at_match_trans with (tenv := tenv) (e := e); try easy.
Qed.

Lemma exp_sem_same_out:
   forall e aenv f g1 g2, exp_sem aenv e f = g1 -> exp_sem aenv e f = g2 -> g1 = g2.
Proof.
 intros e.
 induction e;simpl; intros; subst; try easy.
Qed.

Lemma inv_pexp_reverse :
  forall (tenv tenv':env) (aenv: var -> nat) e f g,
    well_typed_oexp aenv tenv e tenv' -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_WF aenv e -> at_match aenv tenv ->
    exp_sem aenv e f = g ->
    exp_sem aenv (inv_exp e) g = f.
Proof.
  intros. 
  specialize (inv_exp_correct_rev e tenv tenv' aenv f H H0 H1 H2 H3 H4) as G.
  simpl in G.
  subst. easy.
Qed.


Ltac nor_mode_simpl := repeat (try (apply nor_mode_up ; iner_p); try apply nor_mode_cus_eq; try easy). 

Lemma right_mode_val_cus_same : 
   forall f t p x g n, right_mode_val t (f p)
    -> right_mode_val t (put_cus f x g n p).
Proof.
  intros. unfold put_cus.
  destruct p.
  simpl. 
  bdestruct (v =? x). subst.
  bdestruct (n0 <? n).
  unfold put_cu.
  destruct (f (x,n0)). inv H. constructor.
  inv H. constructor. easy.
  inv H.  constructor. constructor.
Qed.

Lemma right_mode_exp_put_cus_same :
    forall aenv tenv f x g n,
     right_mode_env aenv tenv f ->
     right_mode_env aenv tenv (put_cus f x g n).
Proof.
  intros. 
  unfold right_mode_env in *. intros.
  unfold put_cus.
  destruct p. simpl in *.
  bdestruct (v=?x). bdestruct (n0 <? n).
  specialize (H t (v,n0)). simpl in H.
  apply H in H0; try easy.
  unfold put_cu.
  destruct (f (v,n0)). inv H0. constructor.
  easy. apply H; try easy.
  apply H; try easy.
Qed.

Lemma right_mode_exp_up_same_1 :
    forall aenv tenv f f' c b,
     nor_mode f c -> nor_mode f' c ->
     right_mode_env aenv tenv f ->
     right_mode_env aenv tenv (f[c |-> put_cu (f' c) b]).
Proof.
  intros. 
  unfold right_mode_env in *. intros.
  bdestruct (p ==? c).
  subst. rewrite eupdate_index_eq.
  unfold nor_mode in *.
  destruct (f' c).
  unfold put_cu.
  apply H1 in H3. inv H3. rewrite <- H6 in *. constructor.
  rewrite <- H6 in *. lia. easy.
  lia.
  rewrite eupdate_index_neq by iner_p. apply H1; try easy.
Qed.

Lemma put_cus_update_flip : forall n f g x c v, fst c <> x -> put_cus (f[c |-> v]) x g n = (put_cus f x g n)[c |-> v].
Proof.
  intros.
  apply functional_extensionality; intro.
  bdestruct (c ==? x0). subst. rewrite eupdate_index_eq.
  destruct x0. rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  destruct x0.
  bdestruct (v0 =? x). subst. bdestruct (n0 <? n). 
  rewrite put_cus_eq by iner_p.
  rewrite put_cus_eq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_out by lia.
  rewrite put_cus_out by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq by iner_p.
  rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma right_mode_exp_up_same :
    forall aenv tenv f c b,
     right_mode_env aenv tenv f ->
     right_mode_env aenv tenv (f[c |-> put_cu (f c) b]).
Proof.
  intros.
  unfold right_mode_env in *.
  intros.
  bdestruct (c ==? p). subst.
  rewrite eupdate_index_eq.
  apply (H t) in H0; try easy.
  destruct (f p). unfold put_cu. inv H0. constructor.
  unfold put_cu. easy.
  unfold put_cu.
  rewrite eupdate_index_neq by iner_p.
  apply H; try easy.
Qed.

Ltac right_simpl := repeat (try apply right_mode_exp_put_cus_same; try apply right_mode_exp_up_same;
                 (try (apply right_mode_exp_up_same_1; nor_mode_simpl)); try easy).


Lemma sr_rotate'_out_1 : forall n size f x p v, n <= size -> fst p <> x ->
       sr_rotate' (f[p |-> v]) x n size = (sr_rotate' f x n size)[p |-> v].
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_twice_neq.
  rewrite IHn; try easy.
  rewrite eupdate_index_neq. easy.
  destruct p. iner_p. lia.
  destruct p. iner_p.
Qed.

Lemma sr_rotate'_gt_1 : forall n size f x p v, n <= size -> size <= snd p ->
       sr_rotate' (f[p |-> v]) x n size = (sr_rotate' f x n size)[p |-> v].
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_twice_neq.
  rewrite IHn; try easy.
  rewrite eupdate_index_neq. easy.
  destruct p. intros R. inv R. simpl in H0. lia.
  lia.
  destruct p. intros R. inv R. simpl in H0. lia.
Qed.

Lemma srr_rotate'_out_1 : forall n size f x p v, n <= size -> fst p <> x ->
       srr_rotate' (f[p |-> v]) x n size = (srr_rotate' f x n size)[p |-> v].
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_twice_neq.
  rewrite IHn; try easy.
  rewrite eupdate_index_neq. easy.
  destruct p. iner_p. lia.
  destruct p. iner_p.
Qed.

Lemma srr_rotate'_gt_1 : forall n size f x p v, n <= size -> size <= snd p ->
       srr_rotate' (f[p |-> v]) x n size = (srr_rotate' f x n size)[p |-> v].
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_twice_neq.
  rewrite IHn; try easy.
  rewrite eupdate_index_neq. easy.
  destruct p. intros R. inv R. simpl in H0. lia.
  lia.
  destruct p. intros R. inv R. simpl in H0. lia.
Qed.

Lemma lshift'_out : forall n size f x p v, n <= size -> fst p <> x ->
       lshift' n size (f[p |-> v]) x = (lshift' n size f x)[p |-> v].
Proof.
  induction n; intros; simpl. destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  rewrite IHn; try easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy. lia.
Qed.

Lemma lshift'_ge_switch : forall n size f x p v, n <= size -> size < snd p ->
       lshift' n size (f[p |-> v]) x = (lshift' n size f x)[p |-> v].
Proof.
  induction n; intros; simpl. destruct p.
  simpl in H0.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  rewrite IHn; try easy.
  destruct p. simpl in H0.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy. lia.
Qed.

Lemma rshift'_out : forall n size f x p v, n <= size -> fst p <> x ->
       rshift' n size (f[p |-> v]) x = (rshift' n size f x)[p |-> v].
Proof.
  induction n; intros; simpl. destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  rewrite IHn; try easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy. lia.
Qed.


Lemma rshift'_ge_switch : forall n size f x p v, n <= size -> size < snd p ->
       rshift' n size (f[p |-> v]) x = (rshift' n size f x)[p |-> v].
Proof.
  induction n; intros; simpl. destruct p.
  simpl in H0.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  rewrite IHn; try easy.
  destruct p. simpl in H0.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy. lia.
Qed.

Lemma assign_r_out_fun : forall n f x h p v, fst p <> x ->
            assign_r (f[p |-> v]) x h n = ((assign_r f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn by easy.
  rewrite eupdate_twice_neq by iner_p. easy.
Qed.

Lemma assign_h_out_fun : forall i f x b p v, fst p <> x ->
            assign_h (f[p |-> v]) x b i = ((assign_h f x b i)[p |-> v]).
Proof.
  induction i; intros;simpl. easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHi by easy.
  rewrite eupdate_twice_neq by iner_p. easy.
Qed.

Lemma assign_r_ge_fun : forall n f x h p v, n <= snd p ->
            assign_r (f[p |-> v]) x h n = ((assign_r f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p. simpl in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  rewrite eupdate_twice_neq by iner_p. easy. simpl. lia.
Qed.

Lemma assign_h_ge_fun : forall n f x h p v, h+n <= snd p ->
            assign_h (f[p |-> v]) x h n = ((assign_h f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p. simpl in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  rewrite eupdate_twice_neq by iner_p. easy. simpl. lia.
Qed.

Lemma assign_hr_out_fun : forall i f x b p v, fst p <> x ->
            assign_h_r (f[p |-> v]) x b i = ((assign_h_r f x b i)[p |-> v]).
Proof.
  induction i; intros;simpl. easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHi by easy.
  rewrite eupdate_twice_neq by iner_p. easy.
Qed.

Lemma assign_hr_ge_fun : forall n f x h p v, h+n <= snd p ->
            assign_h_r (f[p |-> v]) x h n = ((assign_h_r f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p. simpl in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  rewrite eupdate_twice_neq by iner_p. easy. simpl. lia.
Qed.

Lemma assign_seq_out_fun : forall n f x h p v, fst p <> x ->
            assign_seq (f[p |-> v]) x h n = ((assign_seq f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn by easy.
  rewrite eupdate_twice_neq by iner_p. easy.
Qed.

Lemma assign_seq_ge_fun : forall n f x h p v, n <= snd p ->
            assign_seq (f[p |-> v]) x h n = ((assign_seq f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p. simpl in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  rewrite eupdate_twice_neq by iner_p. easy. simpl; lia.
Qed.

(*
Lemma h_sem_out_fun : forall n f x p v, fst p <> x ->
            h_sem (f[p |-> v]) x n = ((h_sem f x n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn by easy.
  rewrite eupdate_twice_neq by iner_p. easy.
Qed.

Lemma h_sem_ge_fun : forall n f x p v, n <= snd p ->
            h_sem (f[p |-> v]) x n = ((h_sem f x n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p. simpl in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  rewrite eupdate_twice_neq by iner_p. easy. simpl;lia.
Qed.
*)
Lemma efresh_exp_sem_out :
  forall e aenv  p f v,
    exp_fresh aenv p e ->
    exp_WF aenv e ->
    exp_sem aenv e (f[p |-> v]) = ((exp_sem aenv e f)[p |-> v]).
Proof.
  induction e;intros.
  subst. simpl. easy.
  simpl in *. inv H.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  simpl.
  inv H. rewrite eupdate_index_neq by iner_p.
  destruct (get_cua (f p)) eqn:eq1.
  rewrite IHe; try easy. inv H0. easy. easy.
  simpl in *. inv H.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  simpl in *. inv H.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  simpl in *. inv H.
  unfold or_not_r in H3. destruct H3.
  unfold sr_rotate.
  rewrite sr_rotate'_out_1; try easy.
  unfold sr_rotate.
  rewrite sr_rotate'_gt_1; try easy.
  simpl in *. inv H.
  unfold or_not_r in H3. destruct H3.
  unfold srr_rotate.
  rewrite srr_rotate'_out_1; try easy.
  unfold srr_rotate.
  rewrite srr_rotate'_gt_1; try easy.
  inv H. unfold or_not_eq in H3. simpl.
  unfold lshift.
  destruct H3.
  rewrite lshift'_out; try lia. easy.
  destruct p.
  bdestruct (x =? v0). subst.
  simpl in H.
  bdestruct (aenv v0 =? 0). rewrite H1 in *. simpl.
  rewrite eupdate_same.
  apply eupdate_same_1.
  rewrite eupdate_same; try easy. easy. easy.
  rewrite lshift'_ge_switch; try lia. easy. simpl. lia.
  rewrite lshift'_out; try lia. easy. iner_p.
  inv H. unfold or_not_eq in H3. simpl.
  unfold rshift.
  destruct H3.
  rewrite rshift'_out; try lia. easy.
  destruct p.
  bdestruct (x =? v0). subst.
  simpl in H.
  bdestruct (aenv v0 =? 0). rewrite H1 in *. simpl.
  rewrite eupdate_same.
  apply eupdate_same_1.
  rewrite eupdate_same; try easy. easy. easy.
  rewrite rshift'_ge_switch; try lia. easy. simpl. lia.
  rewrite rshift'_out; try lia. easy. iner_p.
  inv H. unfold or_not_eq in H3. simpl.
  unfold reverse.
  apply functional_extensionality; intros; simpl.
  destruct p.
  destruct H3.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (fst x0 =? x). 
  bdestruct (snd x0 <? aenv x). simpl.
  destruct x0. simpl in H.
  subst. rewrite eupdate_index_neq.
  simpl. bdestruct (v1 =? v1).
  bdestruct ((n0 <? aenv v1)). simpl. easy. simpl in H2. lia. lia.
  iner_p. simpl in *.
  bdestruct ((v0,n) ==? x0).
  rewrite <- H3.  repeat rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (fst x0 =? x). 
  bdestruct (snd x0 <? aenv x). simpl. lia. simpl. easy. simpl. easy.
  simpl.
  bdestruct ((v0,n) ==? x0).
  rewrite <- H2.  repeat rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (fst x0 =? x). 
  bdestruct (snd x0 <? aenv x). simpl. lia. simpl. easy. simpl. easy.
  simpl in *.
  bdestruct (fst x0 =? x). 
  bdestruct (snd x0 <? aenv x). simpl.
  destruct x0. simpl in *.
  subst. repeat rewrite eupdate_index_neq by iner_p.
  simpl. bdestruct (x =? x).
  bdestruct ((n0 <? aenv x)). simpl. easy. lia. lia.
  destruct x0. simpl in *.
  subst. bdestruct (n0 =? n). subst.
  bdestruct (x =? v0). subst.
  repeat rewrite eupdate_index_eq. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  simpl in *.
  bdestruct (x =? x).
  bdestruct ((n <? aenv x)). simpl. lia. simpl. easy.
  simpl. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  simpl in *.
  bdestruct (x =? x).
  bdestruct ((n0 <? aenv x)). simpl. lia. simpl. easy.
  simpl. easy.
  destruct x0. simpl in *.
  bdestruct (v0 =? v1). bdestruct (n =? n0). subst.
  repeat rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. simpl.
  bdestruct (v1 =? x). lia. simpl. easy. 
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. simpl.
  bdestruct (v1 =? x). lia. simpl. easy. 
  simpl in *. inv H.
  unfold turn_qft.
  unfold or_not_eq in H3. destruct H3.
  rewrite get_cus_up by easy.
  rewrite assign_r_out_fun by easy.
  rewrite assign_h_out_fun by easy. easy. inv H0.
  rewrite get_cus_up_ge by lia.
  rewrite assign_r_ge_fun by lia.
  rewrite assign_h_ge_fun by lia. easy.
  simpl. inv H. unfold turn_rqft.
  unfold or_not_eq in H3. destruct H3.
  unfold get_r_qft.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite assign_seq_out_fun by iner_p.
   rewrite assign_hr_out_fun by iner_p. easy.
  unfold get_r_qft.
  destruct p. simpl in *.
  bdestruct (v0 =? x). bdestruct (n =? 0). subst.
  rewrite eupdate_index_eq.
  inv H0. assert (b = 0) by lia.
  assert (aenv x = 0) by lia. rewrite H1 in *. rewrite H0 in *.
  simpl. easy. inv H0.
  rewrite eupdate_index_neq by iner_p.
  rewrite assign_seq_ge_fun.
  rewrite assign_hr_ge_fun.
  easy. simpl. lia. simpl. lia.
  rewrite eupdate_index_neq by iner_p.
  rewrite assign_seq_out_fun by iner_p.
  rewrite assign_hr_out_fun by iner_p. easy.
  simpl. inv H. inv H0.
  rewrite IHe1 by easy.
  rewrite IHe2 by easy. easy.
Qed.

Lemma inv_pexp_reverse_1 :
  forall (tenv tenv':env) (aenv: var -> nat) e f g c v,
    well_typed_oexp aenv tenv e  tenv' -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_fresh aenv c e ->
    exp_WF aenv e ->
    at_match aenv tenv ->
    exp_sem aenv e f = g ->
    exp_sem aenv (inv_exp e) (g[c |-> v]) = (f[c |-> v]).
Proof.
  intros. 
  Check inv_pexp_reverse.
  specialize (inv_pexp_reverse tenv tenv' aenv e f g H H0 H1 H2 H4 H5) as G.
  apply functional_extensionality; intros.
  bdestruct (x ==? c). rewrite H7 in *.
  rewrite efresh_exp_sem_out. rewrite G. easy. easy.
  apply fresh_inv_exp. easy.
  apply exp_WF_inv. easy.
  rewrite efresh_exp_sem_out. rewrite G. easy. easy.
  apply fresh_inv_exp. easy.
  apply exp_WF_inv. easy.
Qed.


(*  Compilation to bcom. *)
(* Controlled rotation cascade on n qubits. *)

(* States that is useful in compiling RCIR+ to SQIR. *)
Definition id_fun := fun (i:nat) => i.

Definition adj_offset (index:nat) (offset:nat) (size:nat) :=
    (index + offset) mod size.

Definition vars := nat -> (nat * nat * (nat -> nat) * (nat -> nat)).

Definition start (vs :vars) (x:var) := fst (fst (fst (vs x))).

Definition vsize (vs:vars) (x:var) := snd (fst (fst (vs x))).

Definition vmap (vs:vars) (x:var) := snd (fst (vs x)).

Definition avmap (vs:vars) (x:var) := snd (vs x).

Definition find_pos (f : vars) (p:posi) :=
      let (a,b) := p in start f a + (vmap f a b).

(* Compilinng input variables to a format that will be used on RCIR+. *)


Fixpoint compile_var' (l: list (var * nat)) (dim:nat) :=
   match l with [] => fun _ => (0,0,id_fun,id_fun)
              | (x,n):: l' => fun i => if x =? i
                           then (dim,n,id_fun,id_fun) else (compile_var' l' (dim + n)) i
   end.

Definition compile_var l := compile_var' l 0.

Fixpoint get_dim (l: list (var * nat)) :=
   match l with [] => 0
             | (x,n) :: l' => n + get_dim l'
   end.


Inductive vars_WF : (list (var * nat)) -> Prop :=
    vars_WF_empty : vars_WF (List.nil)
    | vars_WF_many : forall x y xl, 0 < y -> vars_WF xl -> vars_WF ((x,y)::xl).

Fixpoint avars (l: list (var * nat)) (dim:nat) : (nat -> posi) :=
    match l with [] => fun i => (dim,dim)
              | (x,n):: l' => fun i => if (dim <? i) && (i - dim <? n) then (x, i - dim)
                                       else avars l' (dim + n) i
    end.
       

Lemma compile_var'_WF : forall l dim p vs, vs = compile_var' l dim
              -> snd p < vsize vs (fst p) -> find_pos vs p < dim + get_dim l.
Proof.
 induction l; intros; simpl in *.
 rewrite H in H0. unfold vsize in H0. simpl in H0. lia.
 destruct a eqn:eq1.
 destruct p eqn:eq2.
 simpl in *. subst.
 unfold start,vsize,vmap. unfold vsize in H0.
 bdestruct (v =? v0). subst. simpl in *.
 unfold id_fun. lia.
 remember (compile_var' l (dim + n)) as vs'.
 assert (snd (fst (fst (vs' v0))) = vsize vs' v0) by easy.
 rewrite H1 in H0.
 specialize (IHl (dim + n) (v0,n0) vs' Heqvs' H0).
 subst.
 unfold find_pos,start,vmap in IHl. lia.
Qed.

Lemma compile_var_WF : forall l p vs, vs = compile_var l
              -> snd p < vsize vs (fst p) -> find_pos vs p < get_dim l.
Proof.
  intros. unfold compile_var.
  specialize (compile_var'_WF l 0 p vs H H0) as eq1. lia.
Qed.
(*
Definition inter_num (size:nat) (t : varType) :=
   match t with NType => size
              | SType => size+1
   end.
*)


(* the compilation state properties with lemmas. *)
Definition vars_start_diff (vs: vars) :=
        forall x y,  x <> y -> start vs x <> start vs y.

(* A weaker property sometimes easier to prove. *)
Definition weak_finite_bijection (n : nat) (f : nat -> nat) :=
  (forall x, x < n -> f x < n)%nat /\ 
  (exists g, (forall y, y < n -> g y < n)%nat /\
        (forall x, (x < n)%nat -> g (f x) = x) /\ 
        (forall y, (y < n)%nat -> f (g y) = y)).

Definition vars_finite_bij (vs:vars) :=
   forall x,  weak_finite_bijection (vsize vs x) (vmap vs x).

Definition vars_sparse (vs:vars) :=
   forall x y, x <> y -> (forall i j, i < vsize vs x -> j < vsize vs y -> start vs x + i <> start vs y + j).

Lemma finite_bij_lt : forall vs, vars_finite_bij vs 
         -> (forall x i, i < vsize vs x -> vmap vs x i < vsize vs x).
Proof.
  intros. unfold vars_finite_bij in H.
  unfold weak_finite_bijection in H.
  destruct (H x).
  apply H1. easy.
Qed.

Lemma finite_bij_inj : forall vs x, vars_finite_bij vs 
         -> (forall i j, i < vsize vs x -> j < vsize vs x -> i <> j -> vmap vs x i <> vmap vs x j).
Proof.
  intros. unfold vars_finite_bij in H.
  unfold weak_finite_bijection in H.
  destruct (H x).
  destruct H4. destruct H4. destruct H5.
  specialize (H5 i H0) as eq1.
  specialize (H5 j H1) as eq2.
  intros R.
  rewrite R in eq1. rewrite eq1 in eq2. subst. contradiction.
Qed.



(* Compiled RCIR+ circuit well-formedness. *)
Inductive exp_rmax (aenv: var -> nat): nat -> exp -> Prop :=
      | skip_rmax : forall rs p, exp_rmax aenv rs (SKIP p)
      | x_rmax : forall rs p, exp_rmax aenv rs (X p)
     (* | hcnot_rmax : forall rs p1 p2, exp_rmax aenv rs (HCNOT p1 p2) *)
      | cu_rmax : forall vs p e, exp_rmax aenv vs e -> exp_rmax aenv vs (CU p e)
      | rz_rmax : forall rs p q, q < rs -> exp_rmax aenv rs (RZ q p)
      | rrz_rmax : forall rs p q, q < rs -> exp_rmax aenv rs (RRZ q p)
      | sr_rmax : forall rs n x, S n < rs -> exp_rmax aenv rs (SR n x)
      | srr_rmax : forall rs n x, S n < rs -> exp_rmax aenv rs (SRR n x)
      | seq_rmax : forall rs e1 e2, exp_rmax aenv rs e1 -> exp_rmax aenv rs e2 -> exp_rmax aenv rs (Seq e1 e2)
      | lshift_rmax : forall vs x, exp_rmax aenv vs (Lshift x)
      | rshift_rmax : forall vs x, exp_rmax aenv vs (Rshift x)
      | rev_rmax : forall vs x, exp_rmax aenv vs (Rev x)
      | qft_rmax : forall vs x b, b < vs -> exp_rmax aenv vs (QFT x b)
      | rqft_rmax: forall vs x b, b < vs -> exp_rmax aenv vs (RQFT x b).
      (*| h_rmax : forall vs x, 0 < vs -> exp_rmax aenv vs (H x) *)


Fixpoint gen_sr_gate' (f:vars) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
   match n with 0 => SQIR.ID (find_pos f (x,0))
             | S m => SQIR.useq (gen_sr_gate' f dim x m size) (SQIR.Rz (rz_ang (size - m)) (find_pos f (x,m)))
   end.
Definition gen_sr_gate (f:vars) (dim:nat) (x:var) (n:nat) := gen_sr_gate' f dim x (S n) (S n).

Fixpoint gen_srr_gate' (f:vars) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
   match n with 0 => SQIR.ID (find_pos f (x,0))
             | S m => SQIR.useq (gen_srr_gate' f dim x m size) (SQIR.Rz (rrz_ang (size - m)) (find_pos f (x,m)))
   end.
Definition gen_srr_gate (f:vars) (dim:nat) (x:var) (n:nat) := gen_srr_gate' f dim x (S n) (S n).

Definition shift_fun (f:nat -> nat) (offset:nat) (size:nat) :=
         fun i => if i <? size then f ((i + offset) mod size) else f i.

Definition ashift_fun (f:nat -> nat) (offset:nat) (size:nat) :=
         fun i => if i <? size then (((f i) + offset) mod size) else f i.

Lemma shift_fun_back : forall f g off size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) -> off <= size ->
          (forall i, ashift_fun f off size (shift_fun g (size - off) size i) = i).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (i <? size).
  bdestruct (g ((i + (size - off)) mod size) <? size).
  rewrite H3.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((i + (size - off) + off) = i + size) by lia.
  rewrite H8.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  assert (g ((i + (size - off)) mod size) < size).
  apply H1.
  apply Nat.mod_bound_pos. lia. lia. lia.
  apply H2 in H6.
  bdestruct (g i <? size). lia.
  rewrite H3. easy.
Qed.

Lemma shift_fun_back_1 : forall f g off size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) -> off <= size ->
          (forall i, shift_fun f (size-off) size (ashift_fun g off size i) = i).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (i <? size).
  bdestruct ((g i + off) mod size <? size).
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((g i + off + (size - off)) = g i + size) by lia.
  rewrite H8.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small.
  rewrite H3. easy. apply H1. easy.
  assert ((g i + off) mod size < size).
  apply Nat.mod_bound_pos. lia. lia. lia.
  bdestruct (g i <? size).
  apply H2 in H6. lia.
  rewrite H3. easy.
Qed.

Definition afbrev (f:nat -> nat) (size:nat) :=
         fun (x : nat) => if (x <? size) then size - 1 - f x else f x.


Lemma fbrev_back : forall f g size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) ->
          (forall i, afbrev f size (fbrev size g i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (g (size - 1 - i) <? size).
  rewrite H3. lia.
  assert (size - 1 - i < size) by lia.
  apply H1 in H7. lia.
  bdestruct (g i <? size ).
  apply H2 in H5. lia. 
  rewrite H3. easy.
Qed.


Lemma afbrev_back : forall f g size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) ->
          (forall i, fbrev size f (afbrev g size i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (size - 1 - g i <? size).
  assert (g i < size). apply H1 in H5. easy.
  assert ((size - 1 - (size - 1 - g i)) = g i) by lia.
  rewrite H8. rewrite H3. easy. lia. 
  bdestruct (g i <? size ).
  apply H2 in H5. lia. 
  rewrite H3. easy.
Qed.

Definition trans_lshift (f:vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size, 
               shift_fun g (size - 1) size,ashift_fun ag 1 size) else f i
     end.

Definition trans_rshift (f:vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size,
                              shift_fun g 1 size,ashift_fun ag (size - 1) size) else f i
     end.

Definition lshift_avs (dim:nat) (f : vars) (avs : nat -> posi) (x:var)
           := (fun i => if (i <? dim) && (start f x <=? i) && (i - start f x  <? vsize f x)
                                       then (x, avmap (trans_lshift f x) x (i - start f x)) else avs i).

Definition rshift_avs (dim:nat) (f : vars) (avs : nat -> posi) (x:var)
           := (fun i => if (i <? dim) && (start f x <=? i) && (i - start f x <? vsize f x)
                            then (x,avmap (trans_rshift f x) x (i - start f x)) else avs i).

Definition trans_rev (f: vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size, fbrev size g,afbrev ag size) else f i
     end.

(* generalized Controlled rotation cascade on n qubits. *)

(* SQIR.Rz (rz_ang q) (find_pos f p) *)

Fixpoint controlled_rotations_gen (f : vars) (dim:nat) (x:var) (n : nat) (i:nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.ID (find_pos f (x,i))
  | S m  => SQIR.useq (controlled_rotations_gen f dim x m i)
                 (control (find_pos f (x,m+i)) (SQIR.Rz (rz_ang n) (find_pos f (x,i))))
  end.

(* generalized Quantum Fourier transform on n qubits. 
   We use the definition below (with cast and map_qubits) for proof convenience.
   For a more standard functional definition of QFT see Quipper:
   https://www.mathstat.dal.ca/~selinger/quipper/doc/src/Quipper/Libraries/QFT.html *)

Fixpoint QFT_gen (f : vars) (dim:nat) (x:var) (n : nat) (size:nat) : base_ucom dim :=
  match n with
  | 0    => SQIR.ID (find_pos f (x,0))
  | S m => SQIR.useq  (QFT_gen f dim x m size)
             (SQIR.useq (SQIR.H (find_pos f (x,m))) ((controlled_rotations_gen f dim x (size-m) m)))
  end.

Fixpoint nH (f : vars) (dim:nat) (x:var) (n:nat) (b:nat) : base_ucom dim :=
     match n with 0 => SQIR.ID (find_pos f (x,0))
               | S m => SQIR.useq (nH f dim x m b) (SQIR.H (find_pos f (x,b+m))) 
     end.

Definition trans_qft (f:vars) (dim:nat) (x:var) (b:nat) : base_ucom dim :=
         SQIR.useq (QFT_gen f dim x b b) (nH f dim x (vsize f x - b) b).

Definition trans_rqft (f:vars) (dim:nat) (x:var) (b:nat) : base_ucom dim :=
          invert (SQIR.useq (QFT_gen f dim x b b) (nH f dim x (vsize f x - b) b)).

(*
Fixpoint nH (f : vars) (dim:nat) (x:var) (n:nat) : base_ucom dim :=
     match n with 0 => SQIR.ID (find_pos f (x,0))
               | S m => SQIR.useq (nH f dim x m) (SQIR.H (find_pos f (x,m))) 
     end.

Definition trans_h (f : vars) (dim:nat) (x:var) : base_ucom dim := nH f dim x (vsize f x).
*)

Definition rev_avs (dim:nat) (f : vars) (avs : nat -> posi) (x:var)
           := (fun i => if (i <? dim) && (start f x <=? i) && (i - start f x <? vsize f x)
                            then (x,avmap (trans_rev f x) x (i - start f x)) else avs i).

Fixpoint trans_exp (f : vars) (dim:nat) (exp:exp) (avs: nat -> posi) : (base_ucom dim * vars  * (nat -> posi)) :=
  match exp with SKIP p => (SQIR.ID (find_pos f p), f, avs)
              | X p => (SQIR.X (find_pos f p), f, avs)
              | RZ q p => (SQIR.Rz (rz_ang q) (find_pos f p), f, avs)
              | RRZ q p => (SQIR.Rz (rrz_ang q) (find_pos f p), f, avs)
              | SR n x => (gen_sr_gate f dim x n, f, avs)
              | SRR n x => (gen_srr_gate f dim x n, f, avs)
              | Lshift x => (SQIR.ID (find_pos f (x,0)), trans_lshift f x, lshift_avs dim f avs x)
              | Rshift x => (SQIR.ID (find_pos f (x,0)), trans_rshift f x, rshift_avs dim f avs x)
              | Rev x => (SQIR.ID (find_pos f (x,0)), trans_rev f x, rev_avs dim f avs x)
              (*| HCNOT p1 p2 => (SQIR.CNOT (find_pos f p1) (find_pos f p2), f, avs) *)
              | QFT x b => (trans_qft f dim x b, f, avs)
              | RQFT x b => (trans_rqft f dim x b, f, avs)
           (*   | H x => (trans_h f dim x, f, avs) *)
              | CU p e1 => match trans_exp f dim e1 avs with (e1', f',avs')
                              => (control (find_pos f p) e1', f, avs) end
              | e1 ; e2 => match trans_exp f dim e1 avs with (e1', f', avs') => 
                                  match trans_exp f' dim e2 avs' with (e2',f'',avs'') => (SQIR.useq e1' e2', f'', avs'') end
                           end
   end.

(*
  (base_ucom dim * vars  * (nat -> posi)) :=
  match exp with Lshift x => (SQIR.ID (find_pos f (x,0)), trans_lshift f x, 
                              lshift_avs dim f avs x)

              | Rshift x => (SQIR.ID (find_pos f (x,0)),trans_rshift f x, rshift_avs dim f avs x)

              | Rev x => (SQIR.ID (find_pos f (x,0)),trans_rev f x,rev_avs dim f avs x)
*)

Definition exp_com_WF (vs:vars) (dim:nat) :=
    forall p, snd p < vsize vs (fst p) -> find_pos vs p < dim.

Definition exp_com_gt (vs:vars) (avs: nat -> posi) (dim:nat) :=
    forall i, i >= dim -> vsize vs (fst (avs i)) = 0.


Fixpoint turn_angle_r (rval :nat -> bool) (n:nat) (size:nat) : R :=
   match n with 0 => (0:R)
             | S m => (if (rval m) then (1/ (2^ (size - m))) else (0:R)) + turn_angle_r rval m size
   end.
Definition turn_angle (rval:nat -> bool) (n:nat) : R :=
      turn_angle_r (fbrev n rval) n n.

Definition z_phase (b:bool) : R := if b then 1%R else (-1)%R.

Definition compile_val (v:val) (r_max : nat) : Vector 2 := 
   match v with nval b r => Cexp (2*PI * (turn_angle r r_max)) .* ∣ Nat.b2n b ⟩
            (* | hval b1 b2 r => RtoC(/ √ 2) * Cexp (2*PI * (turn_angle r r_max)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩) *)
             | qval q r => RtoC(/ √ 2) * Cexp (2*PI * (turn_angle q r_max)) .* (∣0⟩ .+ (Cexp (2*PI * (turn_angle r r_max))) .* ∣1⟩)
  end.

Lemma WF_compile_val : forall v r, WF_Matrix (compile_val v r).
Proof.
  intros. unfold compile_val.
  destruct v;auto with wf_db.
Qed.

Hint Resolve WF_compile_val : wf_db.

(*example *)
Definition trans_state (avs : nat -> posi) (rmax : nat) (f : posi -> val) : (nat -> Vector 2) :=
        fun i => compile_val (f (avs i)) rmax.

Lemma WF_trans_state : forall avs r f i, WF_Matrix (trans_state avs r f i).
Proof.
  intros. unfold trans_state. auto with wf_db.
Qed.


Hint Resolve WF_trans_state : wf_db.

Lemma WF_trans_state_up : forall avs r f i x v, WF_Matrix v -> WF_Matrix (update (trans_state avs r f) x v i).
Proof.
  intros. unfold update. bdestruct (i =? x). easy. auto with wf_db.
Qed.

Hint Resolve WF_trans_state_up : wf_db.


Lemma find_pos_prop : forall vs p1 p2, vars_start_diff vs -> vars_finite_bij vs ->
            vars_sparse vs ->
            snd p1 < vsize vs (fst p1) -> snd p2 < vsize vs (fst p2) ->
            p1 <> p2 -> find_pos vs p1 <> find_pos vs p2.
Proof.
  intros.
  unfold find_pos,vars_start_diff in *.
  destruct p1. destruct p2.
  simpl in *.
  destruct (vs v) eqn:eq1.
  destruct (vs v0) eqn:eq2.
  destruct p. destruct p0.
  bdestruct (v =? v0).
  subst.
  assert (n <> n0). intros R. subst. contradiction.
  rewrite eq1 in eq2.
  inv eq2.
  specialize (finite_bij_inj vs v0 H0) as eq3.
  specialize (eq3 n n0 H2 H3 H5) as eq4. lia.
  specialize (H1 v v0 H5).
  apply H1.
  apply finite_bij_lt;  assumption.
  apply finite_bij_lt;  assumption.
Qed.

Lemma trans_state_update : forall dim (vs:vars) (avs: nat -> posi) rmax f (p:posi) v,
      (snd p < vsize vs (fst p)) ->
     (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
     (forall i, i < dim -> find_pos vs (avs i) = i) ->
    (forall x , x < dim -> (trans_state avs rmax (f [p |-> v]))  x
            = update (trans_state avs rmax f) (find_pos vs p) (compile_val v rmax) x).
Proof.
  intros.
  unfold trans_state.
  bdestruct (x =? (find_pos vs p)).
  subst.
  rewrite H0 by assumption.
  rewrite eupdate_index_eq.
  rewrite update_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite update_index_neq. easy. lia.
  intros R. subst. rewrite H1 in H3. lia. lia.
Qed.

(*We define helper properties for vars during translation. *)
Definition size_env (vs : vars):= fun i => vsize vs i.

Definition vars_anti_same (vs:vars) :=
     forall x, (forall i, i < vsize vs x -> vmap vs x i < vsize vs x) /\
     (forall i, i >= vsize vs x -> vmap vs x i >= vsize vs x) /\
     (forall i, i < vsize vs x -> avmap vs x i < vsize vs x) /\
     (forall i, i >= vsize vs x -> avmap vs x i >= vsize vs x) /\
     (forall i, vmap vs x (avmap vs x i) = i) /\ (forall i, avmap vs x (vmap vs x i) = i).

Definition avs_prop (vs:vars) (avs: nat -> posi) (dim : nat) :=
       forall i, i < dim -> (start vs (fst (avs i)) <= i /\ i - start vs (fst (avs i))  < vsize vs (fst (avs i))
              /\ avmap vs (fst (avs i)) (i - start vs (fst (avs i))) = snd (avs i)).
(*
Definition avs_prop_gt (vs:vars) (avs: nat -> posi) (dim : nat) :=
       forall i, i >= dim -> i - start vs (fst (avs i))  >= vsize vs (fst (avs i))
     /\ avs (find_pos vs n) = n.
*)
(* This defines when avs i and avs j will be the same. *)
Lemma var_not_over_lap : forall (p1 p2:posi) (vs:vars),  vars_sparse vs -> 
       vars_anti_same vs -> (snd p2 < vsize vs (fst p2))
       ->  fst p1 <> fst p2 ->
       start vs (fst p1) > find_pos vs p2 \/ find_pos vs p2 - start vs (fst p1) >= vsize vs (fst p1).
Proof.
  intros. unfold vars_sparse in H. 
  bdestruct (start vs (fst p1) <=? find_pos vs p2).
  right.
  specialize (H (fst p1) (fst p2) H2).
  unfold find_pos in *. destruct p2. destruct p1. simpl in *.
  bdestruct (start vs v + vmap vs v n - start vs v0 <? vsize vs v0).
  unfold vars_anti_same in H0.
  destruct (H0 v). apply H5 in H1.
  specialize (H (start vs v + vmap vs v n - start vs v0) (vmap vs v n) H4 H1).
  assert (start vs v0 + (start vs v + vmap vs v n - start vs v0) = start vs v + vmap vs v n) by lia.
  rewrite H7 in H. lia. assumption.
  left. assumption.
Qed.

Lemma var_not_over_lap_1 : forall (x:var) (p:posi) (vs:vars),  vars_sparse vs -> 
       vars_anti_same vs -> (snd p < vsize vs (fst p))
       ->  fst p <> x ->
       start vs x > find_pos vs p \/ find_pos vs p - start vs x >= vsize vs x.
Proof.
  intros. unfold vars_sparse in H. 
  bdestruct (start vs x <=? find_pos vs p).
  right.
  specialize (H (fst p) x H2).
  unfold find_pos in *. destruct p. simpl in *.
  bdestruct (start vs v + vmap vs v n - start vs x <? vsize vs x).
  unfold vars_anti_same in H0.
  destruct (H0 v). apply H5 in H1.
  specialize (H (vmap vs v n) (start vs v + vmap vs v n - start vs x) H1 H4).
  assert (start vs x + (start vs v + vmap vs v n - start vs x) = start vs v + vmap vs v n) by lia.
  rewrite H7 in H. lia. assumption.
  left. assumption.
Qed.

Lemma var_over_lap_1 : forall (x:var) (p:posi) (vs:vars),  vars_sparse vs -> 
       vars_anti_same vs -> (snd p < vsize vs (fst p))
       -> start vs x <= find_pos vs p  -> find_pos vs p - start vs x < vsize vs x
          -> fst p = x.
Proof.
  intros.
  bdestruct (fst p =? x). easy.
  specialize (var_not_over_lap_1 x p vs H H0 H1 H4) as eq1.
  destruct eq1. lia. lia.
Qed.


Lemma var_over_lap_exists : forall (x:var) (n:nat) (vs:vars), 
       vars_anti_same vs -> start vs x <= n -> n - start vs x < vsize vs x
       -> exists p, find_pos vs (x,p) = n.
Proof.
  intros. unfold find_pos.
  unfold vars_anti_same in H. specialize (H x).
  destruct H as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  exists (avmap vs x (n - start vs x)).
  rewrite X5. lia.
Qed.

Lemma vs_avs_bij_l : forall vs avs dim, avs_prop vs avs dim -> vars_anti_same vs -> vars_sparse vs ->
           exp_com_WF vs dim -> (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i).
Proof.
  intros. 
  bdestruct (avs (find_pos vs i) ==? i). easy.
  unfold avs_prop in H.
  specialize (H (find_pos vs i)).
  assert (find_pos vs i < dim ).
  apply H2. easy.
  specialize (H H5).
  bdestruct (avs (find_pos vs i) ==? i). easy.
  destruct (avs (find_pos vs i)) eqn:eq1. destruct i eqn:eq2.
  bdestruct (v =? v0). subst.
  assert (n <> n0). intros R. subst. contradiction.
  destruct H as [V1 [ V2 V3]]. simpl in V3.
  assert ((start vs v0 + vmap vs v0 n0 - start vs v0) = vmap vs v0 n0) by lia. rewrite H in V3.
  unfold vars_anti_same in H0.
  destruct (H0 v0) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite X6 in V3. subst. lia.
  specialize (var_not_over_lap (avs (find_pos vs (v0, n0))) (v0, n0) vs H1 H0 H3) as eq3.
  rewrite eq1 in eq3. simpl in eq3.
  apply eq3 in H7.
  destruct H7. destruct H.
  unfold find_pos in H. simpl in H. lia.
  destruct H as [V1 [V2 V3]].
  unfold find_pos in V2. simpl in V2. lia.
Qed.

Lemma vs_avs_bij_r : forall vs avs dim, avs_prop vs avs dim -> vars_anti_same vs ->
           (forall i, i < dim -> find_pos vs (avs i) = i).
Proof.
  intros. 
  bdestruct (find_pos vs (avs i) =? i). easy.
  unfold avs_prop in H.
  specialize (H i H1).
  unfold find_pos in H2.
  destruct (avs i) eqn:eq1. simpl in H.
  destruct H as [V1 [V2 V3]]. 
  unfold vars_anti_same in H0.
  destruct (H0 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  assert (vmap vs v (avmap vs v (i - start vs v)) = vmap vs v n).
  rewrite V3. easy.
  rewrite X5 in H.
  rewrite <- H in H2. lia. 
Qed.


Lemma vs_avs_size : forall vs avs dim, avs_prop vs avs dim -> vars_anti_same vs ->
             (forall i, i < dim -> snd (avs i) < vsize vs (fst (avs i))).
Proof.
  intros. 
  unfold avs_prop in H.
  specialize (H i H1).
  destruct H as [V1 [V2 V3]]. 
  unfold vars_anti_same in H0.
  destruct (H0 (fst (avs i))) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  apply X3. easy.
Qed.

Lemma lshift_avs_lshift_same : forall vs avs dim rmax f x,
          vars_sparse vs -> vars_anti_same vs -> avs_prop vs avs dim -> exp_com_WF vs dim
         -> exp_com_gt vs avs dim -> 0 < vsize vs x
            -> (trans_state avs rmax f) = ((trans_state (lshift_avs dim vs avs x) rmax (lshift f x (vsize vs x)))).
Proof.
  intros. unfold trans_state.
  apply functional_extensionality.
  intros.
  unfold lshift_avs,trans_lshift. 
  destruct (vs x) eqn:eq1.
  destruct p. destruct p.
  bdestruct (x0 <? dim).
  bdestruct ((start vs x <=? x0)).
  bdestruct ((x0 - start vs x <? vsize vs x)). simpl.
  unfold avmap. bdestruct (x =? x). simpl.
  unfold lshift.
  unfold start,vsize. rewrite eq1. simpl.
  assert (fst (avs x0) = x).
  apply var_over_lap_1 with (vs := vs); try assumption.
  apply vs_avs_size with (dim := dim); try assumption.
  unfold avs_prop in H1. specialize (H1 x0 H5). 
  unfold find_pos. destruct (avs x0). simpl in H1.
  destruct H1 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H0.
  destruct (H0 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  unfold avs_prop in H1. specialize (H1 x0 H5). 
  unfold find_pos. destruct (avs x0). simpl in H1.
  destruct H1 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H0.
  destruct (H0 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  destruct (avs x0) eqn:eq2. simpl in H9. subst.
  unfold ashift_fun.
  bdestruct (x0 - n1 <? n2).
  unfold avs_prop in H1.
  specialize (H1 x0 H5). rewrite eq2 in H1. simpl in H1.
  destruct H1 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H0.
  destruct (H0 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  unfold avmap,start in V3. rewrite eq1 in V3. simpl in V3.
  rewrite V3.
  bdestruct (n3 =? n2 -1 ). rewrite H1.
  assert ((n2 - 1 + 1) = n2) by lia.
  rewrite H10.
  rewrite Nat.mod_same by lia.
  rewrite lshift'_0 by lia. easy.
  unfold start,vsize in V2. rewrite eq1 in V2. simpl in V2. 
  specialize (X3 (x0 - n1)).
  unfold vsize,avmap in X3. rewrite eq1 in X3. simpl in X3.
  apply X3 in V2. rewrite V3 in V2.
  rewrite Nat.mod_small by lia.
  assert (n3 + 1 = S n3) by lia. rewrite H10.
  rewrite lshift'_le by lia. easy.
  unfold start,vsize in H7. rewrite eq1 in H7. simpl in H7. lia. lia.
  unfold avs_prop in H1. specialize (H1 x0 H5).
  simpl.
  bdestruct (fst (avs x0) =? x).
  rewrite H8 in H1.
  destruct H1 as [V1 [V2 V3]]. lia.
  unfold lshift.
  rewrite lshift'_irrelevant by assumption. easy.
  simpl.
  unfold avs_prop in H1. specialize (H1 x0 H5).
  simpl.
  bdestruct (fst (avs x0) =? x).
  rewrite H7 in H1.
  destruct H1 as [V1 [V2 V3]]. lia.
  unfold lshift.
  rewrite lshift'_irrelevant by assumption. easy.
  apply H3 in H5.
  bdestruct (fst (avs x0) =? x).
  rewrite H6 in H5. lia.
  simpl.
  unfold lshift.
  rewrite lshift'_irrelevant by assumption. easy.
Qed.

Lemma rshift_avs_rshift_same : forall vs avs dim rmax f x,
          vars_sparse vs -> vars_anti_same vs -> avs_prop vs avs dim -> exp_com_WF vs dim
         -> exp_com_gt vs avs dim -> 0 < vsize vs x
            -> (trans_state avs rmax f) = ((trans_state (rshift_avs dim vs avs x) rmax (rshift f x (vsize vs x)))).
Proof.
  intros. unfold trans_state.
  apply functional_extensionality.
  intros.
  unfold rshift_avs,trans_rshift. 
  destruct (vs x) as [p ag] eqn:eq1.
  destruct p as [p g]. destruct p as [st size].
  bdestruct (x0 <? dim).
  bdestruct ((start vs x <=? x0)).
  bdestruct ((x0 - start vs x <? vsize vs x)). simpl.
  unfold avmap. bdestruct (x =? x). simpl.
  unfold ashift_fun,vsize. rewrite eq1. simpl.
  unfold vsize in H7. rewrite eq1 in H7. simpl in H7.
  specialize (H1 x0 H5) as eq2.
  bdestruct (x0 - start vs x <? size).
  assert (fst (avs x0) = x).
  apply var_over_lap_1 with (vs := vs); try assumption.
  apply vs_avs_size with (dim := dim); try assumption.
  unfold find_pos. destruct (avs x0). simpl in eq2.
  destruct eq2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H0.
  destruct (H0 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  unfold find_pos. destruct (avs x0). simpl in eq2.
  destruct eq2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H0.
  destruct (H0 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. unfold vsize. rewrite eq1. simpl. lia.
  unfold rshift.
  destruct (avs x0) eqn:eq3. simpl in H10. subst. simpl in *.
  destruct eq2 as [V1 [V2 V3]].
  unfold avmap in V3. rewrite eq1 in V3. simpl in V3.
  rewrite V3. 
  destruct n eqn:eq4. rewrite plus_0_l.
  rewrite Nat.mod_small by lia.
  rewrite rshift'_0 by lia. easy.
  assert ( (S n0 + (size - 1)) = n0 + size) by lia. rewrite H10.
  rewrite Nat.add_mod by lia.
  destruct (H0 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  apply X3 in V2.
  unfold avmap,vsize in V2. rewrite eq1 in V2. simpl in V2.
  rewrite V3 in V2.
  rewrite (Nat.mod_small n0) by lia.
  rewrite Nat.mod_same by lia. rewrite plus_0_r.
  rewrite Nat.mod_small by lia.
  rewrite rshift'_le by lia. easy. lia. lia.
  simpl.
  unfold avs_prop in H1. specialize (H1 x0 H5).
  bdestruct (fst (avs x0) =? x).
  rewrite H8 in H1.
  destruct H1 as [V1 [V2 V3]]. lia.
  unfold rshift.
  rewrite rshift'_irrelevant by lia. easy.
  unfold avs_prop in H1. specialize (H1 x0 H5).
  simpl.
  bdestruct (fst (avs x0) =? x).
  rewrite H7 in H1.
  destruct H1 as [V1 [V2 V3]]. lia.
  unfold rshift.
  rewrite rshift'_irrelevant by assumption. easy.
  apply H3 in H5.
  bdestruct (fst (avs x0) =? x).
  rewrite H6 in H5. lia.
  simpl.
  unfold rshift.
  rewrite rshift'_irrelevant by assumption. easy.
Qed.

Lemma rev_avs_rev_same : forall vs avs dim rmax f x,
          vars_sparse vs -> vars_anti_same vs -> avs_prop vs avs dim -> exp_com_WF vs dim
         -> exp_com_gt vs avs dim -> 0 < vsize vs x
            -> trans_state avs rmax f
                   = trans_state (rev_avs dim vs avs x) rmax (reverse f x (vsize vs x)).
Proof.
  intros. unfold trans_state.
  apply functional_extensionality.
  intros.
  unfold rev_avs,reverse,trans_rev,afbrev. 
  bdestruct (x0 <? dim).
  bdestruct ((start vs x <=? x0)).
  bdestruct ((x0 - start vs x <? vsize vs x)). simpl.
  destruct (vs x) as [p ag] eqn:eq1.
  destruct p as [p g]. destruct p as [st size].
  unfold avmap. bdestruct (x =? x). simpl.
  bdestruct ( x0 - start vs x <? size).
  bdestruct (size - 1 - ag (x0 - start vs x) <? vsize vs x).
  assert (fst (avs x0) = x).
  apply var_over_lap_1 with (vs := vs); try assumption.
  apply vs_avs_size with (dim := dim); try assumption.
  unfold avs_prop in H1. specialize (H1 x0 H5). 
  unfold find_pos. destruct (avs x0). simpl in H1.
  destruct H1 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H0.
  destruct (H0 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  unfold avs_prop in H1. specialize (H1 x0 H5). 
  unfold find_pos. destruct (avs x0). simpl in H1.
  destruct H1 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H0.
  destruct (H0 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia. 
  unfold avs_prop in H1. specialize (H1 x0 H5).
  rewrite H11 in H1. simpl in H1. 
  destruct H1 as [V1 [V2 V3]].
  unfold vsize. rewrite eq1. simpl.
  destruct (H0 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  apply X3 in V2.
  unfold avmap,vsize in V2. rewrite eq1 in V2. simpl in V2.
  assert (size - 1 - (size - 1 -
      ag (x0 - start vs x)) = ag (x0 - start vs x)) by lia.
  rewrite H1.
  destruct (avs x0). simpl in H11. subst.
  unfold avmap in V3. rewrite eq1 in V3. simpl in V3.
  rewrite V3. easy. unfold vsize in H10. rewrite eq1 in H10. simpl in H10. lia.
  unfold vsize in H7. rewrite eq1 in H7. simpl in H7. lia. lia.
  simpl.
  bdestruct ((fst (avs x0) =? x)).
  specialize (H1 x0 H5). rewrite H8 in H1. 
  destruct H1 as [V1 [V2 V3]].  lia. simpl. easy.
  simpl.
  bdestruct ((fst (avs x0) =? x)).
  specialize (H1 x0 H5). rewrite H7 in H1. 
  destruct H1 as [V1 [V2 V3]].  lia. simpl. easy.
  simpl.
  apply H3 in H5.
  bdestruct ((fst (avs x0) =? x)).
  rewrite H6 in H5. lia.
  simpl. easy.
Qed.

Lemma vsize_vs_same: forall e dim vs vs' avs p,
         vs' = (snd (fst (trans_exp vs dim e avs))) -> vsize vs' p = vsize vs p.
Proof.
 induction e; intros;subst; try easy.
 simpl.
 destruct (trans_exp vs dim e avs) eqn:eq1. destruct p1.
 simpl. easy.
 simpl.
 unfold trans_lshift, vsize.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rshift, vsize.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rev, vsize.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p0.
 destruct (trans_exp v dim e2 p1) eqn:eq2. destruct p0.
 simpl.
 specialize (IHe1 dim vs v avs p).
 rewrite eq1 in IHe1. simpl in IHe1.
 rewrite <- IHe1.
 rewrite (IHe2 dim v v0 p1). easy.
 rewrite eq2. easy. easy.
Qed.

Lemma size_env_vs_same : forall vs vs' e dim avs,
         vs' = (snd (fst (trans_exp vs dim e avs))) -> size_env vs' = size_env vs.
Proof.
 intros. unfold size_env.
  apply functional_extensionality.
  intros.
  erewrite vsize_vs_same. reflexivity. apply H.
Qed.

Lemma start_vs_same: forall e dim vs vs' avs p, vs' = (snd (fst (trans_exp vs dim e avs))) -> start vs' p = start vs p.
Proof.
 induction e; intros;subst; try easy.
 simpl.
 destruct ( trans_exp vs dim e avs). destruct p1.
 simpl. easy.
 simpl.
 unfold trans_lshift, start.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rshift, start.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rev, start.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p0.
 destruct (trans_exp v dim e2 p1) eqn:eq2. destruct p0.
 simpl.
 specialize (IHe1 dim vs v avs p).
 rewrite eq1 in IHe1. simpl in IHe1.
 rewrite <- IHe1.
 rewrite (IHe2 dim v v0 p1). easy.
 rewrite eq2. easy. easy.
Qed.

Lemma vars_start_diff_vs_same : forall vs vs' e dim avs, vs' = (snd (fst (trans_exp vs dim e avs)))
                    -> vars_start_diff vs -> vars_start_diff vs'.
Proof.
  intros.
  unfold vars_start_diff in *.
  intros.
  rewrite (start_vs_same e dim vs vs' avs).
  rewrite (start_vs_same e dim vs vs' avs).
  apply H0. easy. easy. easy.
Qed.



Lemma shift_fun_lt : forall g off size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> shift_fun g off size i < size). 
Proof.
  intros. unfold shift_fun.
  bdestruct (i <? size).
  apply H. apply Nat.mod_bound_pos. 
  lia. lia. lia.
Qed.

Lemma fbrev_lt : forall g size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> fbrev size g i < size). 
Proof.
  intros. unfold fbrev.
  bdestruct (i <? size).
  apply H. lia. 
  lia.
Qed.

Lemma vars_fun_lt : forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs)))
          -> (forall i, i < vsize vs x -> vmap vs x i < vsize vs x)
          -> (forall i, i < vsize vs x -> vmap vs' x i < vsize vs x).
Proof.
  induction e; intros.
  1-2:subst; simpl; apply H0; easy.
  simpl in *.
  destruct (trans_exp vs dim e avs) eqn:eq1. destruct p0. simpl in *. subst.
  apply H0. easy.
  1-4:subst; simpl; apply H0; easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_lshift in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (shift_fun_lt n0 (n2 - 1) n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H0. rewrite eq1 in H1. simpl in *.
  apply H0. easy. rewrite eq1 in H1. simpl in *. easy.
  apply H0. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rshift in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (shift_fun_lt n0 1 n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H0. rewrite eq1 in H1. simpl in *.
  apply H0. easy. rewrite eq1 in H1. simpl in *. easy.
  apply H0. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rev in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (fbrev_lt n0 n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H0. rewrite eq1 in H1. simpl in *.
  apply H0. easy. rewrite eq1 in H1. simpl in *. easy.
  apply H0. easy.
  simpl in H. subst. apply H0. easy.
  simpl in H. subst. apply H0. easy.
  simpl in *.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
  simpl in *. subst.
  assert (v = snd (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H H0).
  assert (v0 = snd (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H2).
  assert ((forall i : nat,
        i < vsize v x -> vmap v x i < vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H3).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.


Lemma ashift_fun_lt : forall g off size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> ashift_fun g off size i < size). 
Proof.
  intros. unfold ashift_fun.
  bdestruct (i <? size).
  apply Nat.mod_bound_pos. 
  lia. lia. apply H. lia.
Qed.


Lemma afbrev_lt : forall g size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> afbrev g size i < size). 
Proof.
  intros. unfold afbrev.
  bdestruct (i <? size). lia. lia.
Qed.


Lemma vars_afun_lt : forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs)))
          -> (forall i, i < vsize vs x -> avmap vs x i < vsize vs x)
          -> (forall i, i < vsize vs x -> avmap vs' x i < vsize vs x).
Proof.
  induction e; intros.
  1-2:subst; simpl; apply H0; easy.
  simpl in *. 
  destruct (trans_exp vs dim e avs). destruct p0.
  simpl in *. subst. apply H0. easy.
  1-4:subst; simpl; apply H0; easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_lshift in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (ashift_fun_lt n 1 n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H0. rewrite eq1 in H1. simpl in *.
  apply H0. easy. rewrite eq1 in H1. simpl in *. easy.
  apply H0. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rshift in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (ashift_fun_lt n (n2-1) n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H0. rewrite eq1 in H1. simpl in *.
  apply H0. easy. rewrite eq1 in H1. simpl in *. easy.
  apply H0. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rev in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (afbrev_lt n n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H0. rewrite eq1 in H1. simpl in *.
  apply H0. easy. rewrite eq1 in H1. simpl in *. easy.
  apply H0. easy.
  simpl in H. subst. apply H0. easy.
  simpl in H. subst. apply H0. easy.
  simpl in H.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl in *. subst.
  assert (v = snd (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H H0).
  assert (v0 = snd (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H2).
  assert ((forall i : nat,
        i < vsize v x -> avmap v x i < vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H3).
  rewrite <- (vsize_vs_same e1 dim vs v avs). 
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy. easy. easy.
Qed.

Lemma shift_fun_twice : forall f g off size, off <= size -> 
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> g (f x) = x) ->
           (forall x, x < size -> ashift_fun g (size - off) size (shift_fun f off size x) = x).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (x <? size).
  bdestruct ( off =? size). subst.
  bdestruct (f ((x + size) mod size) <? size).
  assert ((size - size) = 0) by lia. rewrite H6.
  rewrite plus_0_r.
  rewrite H2.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small x) by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  rewrite H2.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small) by lia.
  easy.
  apply Nat.mod_bound_pos. lia. lia.
  bdestruct (off =? 0). subst.
  assert (size - 0 = size) by lia. rewrite H6.
  rewrite plus_0_r.
  bdestruct (f (x mod size) <? size).
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite H2.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  rewrite H2. 
  rewrite Nat.mod_small by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  bdestruct (f ((x + off) mod size) <? size).
  rewrite H2.
  assert (size - off < size) by lia.
  rewrite <- (Nat.mod_small (size - off) size) by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((x + off + (size - off)) = x + size) by lia.
  rewrite H9.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small x) by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  assert (f ((x + off) mod size) < size).
  apply H0. 
  apply Nat.mod_bound_pos. lia. lia. lia. lia.
Qed.

Lemma ashift_fun_twice : forall f g off size, off <= size -> 
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> f (g x) = x) ->
           (forall x, x < size -> (shift_fun f off size (ashift_fun g (size - off) size x)) = x).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (x <? size).
  bdestruct ( off =? size). subst.
  bdestruct ((g x + (size - size)) mod size <? size).
  assert ((size - size) = 0) by lia. rewrite H6.
  rewrite plus_0_r.
  rewrite (Nat.mod_small (g x)).
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small (g x)).
  rewrite H2. easy. easy.
  apply H1. easy. apply H1. easy.
  assert ((g x + (size - size)) mod size < size). 
  apply Nat.mod_bound_pos. lia. lia.
  lia.
  bdestruct ((g x + (size - off)) mod size <? size).
  rewrite <- (Nat.mod_small off size) by lia.
  rewrite <- Nat.add_mod by lia.
  rewrite (Nat.mod_small off) by lia.
  assert ((g x + (size - off) + off) = g x + size) by lia.
  rewrite H7.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small (g x)).
  rewrite H2. easy. easy. apply H1. lia.
  assert ((g x + (size - off)) mod size < size).
  apply Nat.mod_bound_pos. lia. lia. lia. lia.
Qed.

Lemma afbrev_back_lt : forall f g size,
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> f (g x) = x) ->
          (forall i, i < size -> afbrev f size (fbrev size g i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (g (size - 1 - i) <? size).
  rewrite H1. lia. lia.
  assert (size - 1 - i < size) by lia.
  apply H0 in H5. lia. lia.
Qed.

Lemma fbrev_back_lt : forall f g size,
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> f (g x) = x) ->
          (forall i, i < size -> fbrev size f (afbrev g size i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (size - 1 - g i <? size).
  assert (g i < size). apply H0. easy.
  assert ((size - 1 - (size - 1 - g i)) = g i) by lia.
  rewrite H6. rewrite H1. lia. lia. lia. lia.
Qed.

Definition exists_fun_bij (vs:vars) (x:var) := exists g : nat -> nat,
  (forall y : nat, y < vsize vs x -> g y < vsize vs x) /\
  (forall x0 : nat,
   x0 < vsize vs x -> g (vmap vs x x0) = x0) /\
  (forall y : nat, y < vsize vs x -> vmap vs x (g y) = y).

Lemma trans_same_bij:  forall e dim vs vs' avs x, 
    (forall i, i < vsize vs x -> vmap vs x i < vsize vs x) ->
      vs' = (snd (fst (trans_exp vs dim e avs)))
       -> 0 < vsize vs x ->
       exists_fun_bij vs x -> exists_fun_bij vs' x.
Proof.
  induction e; intros; subst; try easy.
- simpl in *. destruct (trans_exp vs dim e avs).
  destruct p0. simpl. easy.
- unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Lshift x) dim vs) with (avs := avs).
  simpl in *.
  destruct H2 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_lshift.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (ashift_fun g 1 n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check shift_fun_lt.
  specialize (ashift_fun_lt g 1 n2) as eq2.
  apply eq2. intros.
  unfold vsize in Ht. 
  rewrite eq1 in Ht. simpl in Ht.
  apply Ht. easy. 
  unfold vsize in H0.
  rewrite eq1 in H0. simpl in H0.
  easy.
  unfold vsize,vmap in H.
  rewrite eq1 in H. simpl in H.
  unfold vsize in Ht. rewrite eq1 in Ht. simpl in Ht.
  unfold vsize,vmap in Hf. rewrite eq1 in Hf. simpl in Hf.
  unfold vsize,vmap in Hb. rewrite eq1 in Hb. simpl in Hb.
  split.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H2. simpl.
  assert (n2 - 1 <= n2).
  unfold vsize in H0. rewrite eq1 in H0. simpl in H0. lia.
  specialize (shift_fun_twice n0 g (n2 - 1) n2 H2 H Ht Hf x1) as eq2.
  unfold vsize in H0. rewrite eq1 in H0. simpl in H0.
  assert (n2 - (n2 -1) = 1) by lia. rewrite H3 in eq2.
  rewrite eq2. easy. assumption. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H2. simpl.
  assert ((n2 - 1) <= n2).
  unfold vsize in H0. rewrite eq1 in H0. simpl in H0. lia.
  Check ashift_fun_twice.
  specialize (ashift_fun_twice n0 g (n2 - 1) n2 H2 H Ht Hb) as eq2.
  unfold vsize in H0. rewrite eq1 in H0. simpl in H0. 
  assert ((n2 - (n2 - 1)) = 1) by lia. rewrite H3 in eq2.
  rewrite eq2. easy. easy.
  lia.
  exists g. split. easy.
  split.
  unfold vmap,trans_lshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert ((snd (fst (vs x0)) x1) = vmap vs x0 x1) by easy.
  rewrite H4. rewrite Hf. easy. assumption.
  unfold vmap,trans_lshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert (snd (fst (vs x0)) (g y) = vmap vs x0 (g y)) by easy.
  rewrite H4. rewrite Hb. easy. assumption. easy.
- unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Rshift x) dim vs) with (avs := avs).
  simpl in *.
  destruct H2 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_rshift.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (ashift_fun g (n2 - 1) n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check shift_fun_lt.
  specialize (ashift_fun_lt g (n2 - 1) n2) as eq2.
  apply eq2. intros.
  unfold vsize in Ht. 
  rewrite eq1 in Ht. simpl in Ht.
  apply Ht. easy. 
  unfold vsize in H0.
  rewrite eq1 in H0. simpl in H0.
  easy.
  unfold vsize,vmap in H.
  rewrite eq1 in H. simpl in H.
  unfold vsize in Ht. rewrite eq1 in Ht. simpl in Ht.
  unfold vsize,vmap in Hf. rewrite eq1 in Hf. simpl in Hf.
  unfold vsize,vmap in Hb. rewrite eq1 in Hb. simpl in Hb.
  split.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H2. simpl.
  unfold vsize in H0. rewrite eq1 in H0. simpl in H0.
  assert (1 <= n2) by lia.
  specialize (shift_fun_twice n0 g 1 n2 H2 H Ht Hf) as eq2.
  rewrite eq2. easy. easy. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H2. simpl.
  unfold vsize in H0. rewrite eq1 in H0. simpl in H0.
  assert (1 <= n2) by lia.
  Check ashift_fun_twice.
  specialize (ashift_fun_twice n0 g 1 n2 H2 H Ht Hb) as eq2.
  rewrite eq2. easy.
  easy.
  lia.
  exists g. split. easy.
  split.
  unfold vmap,trans_rshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert ((snd (fst (vs x0)) x1) = vmap vs x0 x1) by easy.
  rewrite H4. rewrite Hf. easy. assumption.
  unfold vmap,trans_rshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert (snd (fst (vs x0)) (g y) = vmap vs x0 (g y)) by easy.
  rewrite H4. rewrite Hb. easy. assumption. easy.
- unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Rev x) dim vs) with (avs := avs).
  simpl in *.
  destruct H2 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_rev.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (afbrev g n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check afbrev_lt.
  specialize (afbrev_lt g n2) as eq2.
  apply eq2. intros.
  unfold vsize in Ht. 
  rewrite eq1 in Ht. simpl in Ht.
  apply Ht. easy. 
  unfold vsize in H0.
  rewrite eq1 in H0. simpl in H0.
  easy.
  unfold vsize,vmap in H.
  rewrite eq1 in H. simpl in H.
  unfold vsize in Ht. rewrite eq1 in Ht. simpl in Ht.
  unfold vsize,vmap in Hf. rewrite eq1 in Hf. simpl in Hf.
  unfold vsize,vmap in Hb. rewrite eq1 in Hb. simpl in Hb.
  split.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H2. simpl.
  unfold vsize in H0. rewrite eq1 in H0. simpl in H0.
  Check afbrev_back_lt.
  specialize (afbrev_back_lt g n0 n2 Ht H Hf) as eq2.
  rewrite eq2. easy. easy. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H2. simpl.
  unfold vsize in H0. rewrite eq1 in H0. simpl in H0.
  Check fbrev_back_lt.
  specialize (fbrev_back_lt n0 g n2 H Ht Hb) as eq2.
  rewrite eq2. easy.
  easy.
  lia.
  exists g. split. easy.
  split.
  unfold vmap,trans_rev. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert ((snd (fst (vs x0)) x1) = vmap vs x0 x1) by easy.
  rewrite H4. rewrite Hf. easy. assumption.
  unfold vmap,trans_rev. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert (snd (fst (vs x0)) (g y) = vmap vs x0 (g y)) by easy.
  rewrite H4. rewrite Hb. easy. assumption. easy.
- simpl in *.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
  simpl in *.
  assert (v = (snd (fst (trans_exp vs dim e1 avs)))).
  rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H H0 H1 H2).
  assert ((forall i : nat, i < vsize v x -> vmap v x i < vsize v x) ).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs).
  rewrite (vsize_vs_same e1 dim vs v avs) in H3.
  apply (vars_fun_lt e1 dim) with (avs := avs). easy. apply H. easy. easy. easy.
  assert (v0 = snd (fst (trans_exp v dim e2 p0))).
  rewrite eq2. easy.
  assert (0 < vsize v x).
  rewrite (vsize_vs_same e1 dim vs) with (avs := avs). easy. rewrite eq1. easy.
  specialize (IHe2 dim v v0 p0 x H3 H4 H5 IHe1). easy.
Qed.

Lemma vars_finite_bij_vs_same : forall e dim vs vs' avs, vs' = (snd (fst (trans_exp vs dim e avs)))
                    -> vars_finite_bij vs -> vars_finite_bij vs'.
Proof.
  intros. unfold vars_finite_bij in *.
  intros.
  unfold weak_finite_bijection in *.
  split.
  intros. specialize (H0 x).
  destruct H0.
  rewrite (vsize_vs_same e dim vs vs' avs).
  apply (vars_fun_lt e dim vs vs' avs). assumption. easy.
  rewrite <- (vsize_vs_same e dim vs vs' avs). easy. easy. easy.
  specialize (H0 x). destruct H0.
  bdestruct (vsize vs x =? 0).
  assert (vsize vs' x = 0).
  rewrite (vsize_vs_same e dim vs vs' avs). easy. easy.
  destruct H1. exists x0.
  split. intros. lia.
  split. intros. lia.
  intros. lia.
  assert (0 < vsize vs x) by lia.
  specialize (trans_same_bij e dim vs vs' avs x H0 H H3 H1) as eq1. easy.
Qed.

Lemma vars_sparse_vs_same : forall e dim vs vs' avs, vs' = (snd (fst (trans_exp vs dim e avs)))
                    -> vars_sparse vs -> vars_sparse vs'.
Proof.
  intros.
  unfold vars_sparse in *.
  intros.
  repeat rewrite (start_vs_same e dim vs vs' avs) by easy.
  rewrite (vsize_vs_same e dim vs vs' avs) in H2 by easy.
  rewrite (vsize_vs_same e dim vs vs' avs) in H3 by easy.
  apply H0; easy.
Qed.

Lemma vars_fun_ge : forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs)))
          -> (forall i, i >= vsize vs x -> vmap vs x i >= vsize vs x)
          -> (forall i, i >= vsize vs x -> vmap vs' x i >= vsize vs x).
Proof.
  induction e; intros.
  1-2:subst; simpl; apply H0; easy.
  simpl in *. destruct (trans_exp vs dim e avs). destruct p0.
  subst. simpl in *. apply H0. easy.
  1-4:subst; simpl; apply H0; easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_lshift in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H1. simpl in H1.
  unfold shift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H0. simpl in H0. apply H0. easy.
  apply H0. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rshift in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H1. simpl in H1.
  unfold shift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H0. simpl in H0. apply H0. easy.
  apply H0. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rev in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H1. simpl in H1.
  unfold fbrev.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H0. simpl in H0. apply H0. easy.
  apply H0. easy.
  subst. simpl. apply H0. easy.
  subst. simpl. apply H0. easy.
  subst. simpl.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl.
  assert (v = snd (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H H0).
  assert (v0 = snd (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H2).
  assert ((forall i : nat,
        i >= vsize v x -> vmap v x i >= vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs) with (avs := avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H3).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.

Lemma vars_afun_ge : forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs)))
          -> (forall i, i >= vsize vs x -> avmap vs x i >= vsize vs x)
          -> (forall i, i >= vsize vs x -> avmap vs' x i >= vsize vs x).
Proof.
  induction e; intros.
  1-2:subst; simpl; apply H0; easy.
  simpl in *. destruct (trans_exp vs dim e avs). destruct p0. subst. simpl.
  apply H0. easy.
  1-4:subst; simpl; apply H0; easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_lshift in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H1. simpl in H1.
  unfold ashift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H0. simpl in H0. apply H0. easy.
  apply H0. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rshift in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H1. simpl in H1.
  unfold ashift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H0. simpl in H0. apply H0. easy.
  apply H0. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rev in H.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H1. simpl in H1.
  unfold afbrev.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H0. simpl in H0. apply H0. easy.
  apply H0. easy.
  subst. simpl. apply H0. easy.
  subst. simpl. apply H0. easy.
  subst. simpl.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl.
  assert (v = snd (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H H0).
  assert (v0 = snd (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H2).
  assert ((forall i : nat,
        i >= vsize v x -> avmap v x i >= vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H3).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.

Lemma vars_vs_anti_bij :
    forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs))) ->
     (forall i : nat, i < vsize vs x -> vmap vs x i < vsize vs x) ->
     (forall i : nat, i >= vsize vs x -> vmap vs x i >= vsize vs x) ->
    (forall i : nat, i < vsize vs x -> avmap vs x i < vsize vs x) ->
       (forall i : nat, i >= vsize vs x -> avmap vs x i >= vsize vs x) ->
      (forall i : nat, vmap vs x (avmap vs x i) = i) -> 
       (forall i : nat, avmap vs x (vmap vs x i) = i) ->
      (forall i : nat, vmap vs' x (avmap vs' x i) = i) /\ (forall i : nat, avmap vs' x (vmap vs' x i) = i).
Proof.
 induction e; intros.
 1-2:subst; simpl; easy.
 simpl in *. destruct (trans_exp vs dim e avs). destruct p0. simpl in *. subst.
 easy.
 1-4:subst; simpl; easy.
-
 subst. simpl. split. intros.
 unfold trans_lshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back_1 ; try easy.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n i <? n2).
 unfold vsize,avmap in H3. rewrite eq1 in H3. simpl in H3.
 apply H3 in H6. lia.
 unfold vmap,avmap in H4. rewrite eq1 in H4. simpl in H4.
 rewrite H4. easy.
 unfold vmap,avmap in H4.
 rewrite H4. easy.
 intros.
 unfold trans_lshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back ; try easy.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n0 i <? n2).
 unfold vsize,avmap in H1. rewrite eq1 in H1. simpl in H1.
 apply H1 in H6. lia.
 unfold vmap,avmap in H5. rewrite eq1 in H5. simpl in H5.
 rewrite H5. easy.
 unfold vmap,avmap in H5.
 rewrite H5. easy.
- subst. simpl.
 split. intros.
 unfold trans_rshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 assert (shift_fun n0 1 n2 (ashift_fun n (n2 - 1) n2 i) 
           = shift_fun n0 (n2 - (n2 - 1)) n2 (ashift_fun n (n2 - 1) n2 i)).
 assert (n2 - (n2 -1) = 1) by lia.
 rewrite H6. easy.
 rewrite H6.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back_1 ; try easy. lia.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n i <? n2).
 unfold vsize,avmap in H3. rewrite eq1 in H3. simpl in H3.
 apply H3 in H6. lia.
 unfold vmap,avmap in H4. rewrite eq1 in H4. simpl in H4.
 rewrite H4. easy.
 unfold vmap,avmap in H4.
 rewrite H4. easy.
 intros.
 unfold trans_rshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 assert (ashift_fun n (n2 - 1) n2 (shift_fun n0 1 n2 i) 
           = ashift_fun n (n2 - 1) n2 (shift_fun n0 (n2 - (n2 -1)) n2 i)).
 assert (n2 - (n2 -1) = 1) by lia.
 rewrite H6. easy.
 rewrite H6.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back ; try easy. lia.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n0 i <? n2).
 unfold vsize,avmap in H1. rewrite eq1 in H1. simpl in H1.
 apply H1 in H6. lia.
 unfold vmap,avmap in H5. rewrite eq1 in H5. simpl in H5.
 rewrite H5. easy.
 unfold vmap,avmap in H5.
 rewrite H5. easy.
-
 subst. simpl. split. intros.
 unfold trans_rev.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite afbrev_back ; try easy.
 unfold vmap,avmap in H4. rewrite H4. easy.
 intros.
 unfold trans_rev.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite fbrev_back ; try easy.
 unfold vmap,avmap in H5. rewrite H5. easy.
- subst. simpl. easy.
- subst. simpl. easy.
-
 subst. simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl.
 specialize (IHe1 dim vs v avs x).
 rewrite eq1 in IHe1.
 assert (v = snd (fst (b, v, p0))) by easy.
 specialize (IHe1 H H0 H1 H2 H3 H4 H5).
 specialize (IHe2 dim v v0 p0 x).
 rewrite eq2 in IHe2.
 assert (v0 = snd (fst (b0, v0, p1))) by easy.
 apply IHe2 in H6. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_fun_lt e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_fun_ge e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_afun_lt e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_afun_ge e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy. easy. easy.
Qed.

Lemma vars_anti_vs_same: forall e dim vs vs' avs, vs' = (snd (fst (trans_exp vs dim e avs)))
                    -> vars_anti_same vs -> vars_anti_same vs'.
Proof.
  intros.
  unfold vars_anti_same in *.
  intro x. specialize (H0 x).
  destruct H0.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_fun_lt e dim vs vs' avs). easy. assumption.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_fun_ge e dim vs) with (avs := avs) ; easy.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_afun_lt e dim vs vs' avs). easy. easy.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_afun_ge e dim vs vs' avs) ; easy.
  destruct H1 as [H1 [H2 [H3 [H5 H6]]]].
  specialize (vars_vs_anti_bij e dim vs vs' avs x H H0 H1 H2 H3 H5 H6) as eq1.
  destruct eq1. easy.
Qed.


Lemma wf_vs_same: forall e1 e2 avs dim vs vs', exp_WF (size_env vs) e1 -> 
                vs' = (snd (fst (trans_exp vs dim e2 avs))) -> exp_WF (size_env vs') e1.
Proof.
  intros.
  induction H. constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  apply IHexp_WF1. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
Qed.


Lemma exists_same_vs_var : forall e dim x n avs vs vs', vs' = (snd (fst (trans_exp vs dim e avs)))->
                  n < vsize vs x -> 
                 (exists n', n' < vsize vs x /\ find_pos vs' (x,n) = find_pos vs (x,n')).
Proof.
 induction e; intros.
 1-2:subst; exists n; easy.
 simpl in *.
 destruct (trans_exp vs dim e avs) eqn:eq1. destruct p0.
 simpl in *. subst.
 exists n. easy.
 1-4:subst; exists n; easy.
- 
 specialize (start_vs_same (Lshift x) dim vs vs' avs x0 H) as eq1.
 specialize (vsize_vs_same (Lshift x) dim vs vs' avs x0 H) as eq2.
 simpl.
 rewrite eq1. 
 bdestruct (x =? x0). subst.
 unfold vmap. simpl.
 simpl in eq2.
 unfold trans_lshift in *.
 destruct (vs x0) eqn:eq3.
 destruct p. destruct p.
 unfold vsize in eq2. 
 bdestruct (x0 =? x0). simpl in *.
 unfold vsize in *. rewrite <- eq2 in *.
 unfold shift_fun.
 bdestruct (n <? n3).
 exists (((n + (n3 - 1)) mod n3)).
 split.
 apply Nat.mod_bound_pos. lia. lia. easy. lia. lia.
 exists n. 
 rewrite H. simpl.
 unfold trans_lshift,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
-
 specialize (start_vs_same (Rshift x) dim vs vs' avs x0 H) as eq1.
 specialize (vsize_vs_same (Rshift x) dim vs vs' avs x0 H) as eq2.
 simpl.
 rewrite eq1. 
 bdestruct (x =? x0). subst.
 unfold vmap. simpl.
 simpl in eq2.
 unfold trans_rshift in *.
 destruct (vs x0) eqn:eq3.
 destruct p. destruct p.
 unfold vsize in eq2. 
 bdestruct (x0 =? x0). simpl in *.
 unfold vsize in *. rewrite <- eq2 in *.
 unfold shift_fun.
 bdestruct (n <? n3).
 exists (((n + 1) mod n3)).
 split.
 apply Nat.mod_bound_pos. lia. lia. easy. lia.
 exists n. 
 rewrite eq3. simpl. easy.
 exists n.
 split. easy.
 rewrite H. simpl.
 unfold trans_rshift,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
- 
 specialize (start_vs_same (Rev x) dim vs vs' avs x0 H) as eq1.
 specialize (vsize_vs_same (Rev x) dim vs vs' avs x0 H) as eq2.
 simpl.
 rewrite eq1. 
 bdestruct (x =? x0). subst.
 unfold vmap. simpl.
 simpl in eq2.
 unfold trans_rev in *.
 destruct (vs x0) eqn:eq3.
 destruct p. destruct p.
 unfold vsize in eq2. 
 bdestruct (x0 =? x0). simpl in *.
 unfold vsize in *. rewrite <- eq2 in *.
 unfold fbrev.
 bdestruct (n <? n3).
 exists ((n3 - 1 - n)).
 split. lia. easy. lia. lia. 
 exists n.
 split. easy.
 rewrite H. simpl.
 unfold trans_rev,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
- simpl in H. subst. exists n. easy.
- simpl in H. subst. exists n. easy.
- 
 simpl in H.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0 ) eqn:eq2. destruct p.
 simpl in H. subst.
 specialize (IHe2 dim x n p0 v v0).
 rewrite eq2 in IHe2.
 assert (v0 = snd (fst (b0, v0, p1))) by easy.
 apply IHe2 in H. destruct H. destruct H.
 specialize (IHe1 dim x x0 avs vs v).
 rewrite eq1 in IHe1. assert (v = snd (fst (b, v, p0))) by easy.
 apply IHe1 in H2. destruct H2.
 destruct H2.
 exists x1.
 split. assumption. 
 rewrite H1. easy.
 erewrite <- vsize_vs_same.
 apply H. rewrite eq1. easy.
 erewrite vsize_vs_same.
 apply H0.
 rewrite eq1. easy.
Qed.

Lemma exp_com_WF_vs_same : forall e dim avs vs vs', vs' = (snd (fst (trans_exp vs dim e avs)))
          -> exp_com_WF vs dim -> exp_com_WF vs' dim.
Proof.
 induction e; intros.
 1-2:subst; easy.
 simpl in *.
 destruct (trans_exp vs dim e avs). destruct p0. simpl in *. subst. easy.
 1-4:subst; easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Lshift x) dim vs vs' avs (fst p) H) as eq1.
 rewrite eq1 in H1.
 specialize (exists_same_vs_var (Lshift x) dim (fst p) (snd p) avs vs vs' H H1) as eq5.
 destruct eq5. destruct H2.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H4 in H3. rewrite H3.
 apply H0. simpl. easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Rshift x) dim vs vs' avs (fst p) H) as eq1.
 rewrite eq1 in H1.
 specialize (exists_same_vs_var (Rshift x) dim (fst p) (snd p) avs vs vs' H H1) as eq5.
 destruct eq5. destruct H2.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H4 in H3. rewrite H3.
 apply H0. simpl. easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Rev x) dim vs vs' avs (fst p) H) as eq1.
 rewrite eq1 in H1.
 specialize (exists_same_vs_var (Rev x) dim (fst p) (snd p) avs vs vs' H H1) as eq5.
 destruct eq5. destruct H2.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H4 in H3. rewrite H3.
 apply H0. simpl. easy.
 simpl in *. subst. easy.
 simpl in *. subst. easy.
 rewrite H. simpl in *.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
 specialize (IHe1 dim avs vs v).
 specialize (IHe2 dim p0 v v0).
 subst.
 apply IHe2. rewrite eq2. easy.
 apply IHe1. rewrite eq1. easy.
 assumption. 
Qed.

Lemma exp_com_gt_vs_same :
    forall e dim vs vs' avs avs', vs' = (snd (fst (trans_exp vs dim e avs)))
      -> avs' = snd (trans_exp vs dim e avs)
          -> exp_com_gt vs avs dim -> exp_com_gt vs' avs' dim.
Proof.
 induction e; intros.
 1-2:subst; easy.
 simpl in *. destruct (trans_exp vs dim e avs). destruct p0.
 simpl in *. subst. easy.
 1-4:subst; easy.
 unfold exp_com_gt in *. intros.
 rewrite (vsize_vs_same (Lshift x) dim vs vs' avs) by try assumption.
 rewrite H0. simpl. unfold lshift_avs.
 bdestruct ((i <? dim)). lia. simpl. apply H1. easy.
 unfold exp_com_gt in *. intros.
 rewrite (vsize_vs_same (Rshift x) dim vs vs' avs) by try assumption.
 rewrite H0. simpl. unfold rshift_avs.
 bdestruct ((i <? dim)). lia. simpl. apply H1. easy.
 unfold exp_com_gt in *. intros.
 rewrite (vsize_vs_same (Rev x) dim vs vs' avs) by try assumption.
 rewrite H0. simpl. unfold rev_avs.
 bdestruct ((i <? dim)). lia. simpl. apply H1. easy.
 simpl in *. subst. easy.
 simpl in *. subst. easy.
 rewrite H0. rewrite H. simpl in *.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl in *.
 specialize (IHe1 dim vs v avs p0).
 rewrite eq1 in IHe1. simpl in IHe1.
 apply IHe1 in H1.
 apply (IHe2 dim v v0 p0 p1). rewrite eq2. easy. rewrite eq2. easy.
 1-3:easy.
Qed.

Lemma avs_prop_vs_same : forall e dim vs vs' avs avs', vs' = (snd (fst (trans_exp vs dim e avs)))
      -> avs' = snd (trans_exp vs dim e avs) -> vars_anti_same vs -> vars_sparse vs
          -> avs_prop vs avs dim -> avs_prop vs' avs' dim.
Proof.
 induction e; intros.
 1-2:subst; easy.
 simpl in *.
 destruct (trans_exp vs dim e avs). destruct p0.
 simpl in *. subst. easy.
 1-4:subst; easy.
-
 specialize (vs_avs_bij_r vs avs dim H3 H1) as Q1.
 specialize (vs_avs_size vs avs dim H3 H1) as Q2.
 unfold avs_prop. intros.
 subst.
 simpl. unfold trans_lshift,lshift_avs.
 destruct (vs x) as [p ag] eqn:eq1.
 destruct p as [p g]. destruct p as [st size].
 bdestruct (i <? dim).
 bdestruct ((start vs x <=? i)).
 bdestruct ((i - start vs x <? vsize vs x)). simpl.
 split.
 unfold start. bdestruct (x =? x). simpl.
 specialize (H3 i H4).
 bdestruct (fst (avs i) =? x). rewrite H7 in H3.
 destruct H3 as [V1 [V2 V3]]. unfold start in V1. rewrite eq1 in V1. simpl in V1. easy.
 specialize (var_not_over_lap_1 x (avs i) vs H2 H1) as eq2.
 apply eq2 in H7. destruct H7. rewrite Q1 in H7. lia. easy.
 rewrite Q1 in H7. lia. easy. apply Q2. easy. rewrite eq1. simpl.
 unfold start in H0. rewrite eq1 in H0. simpl in H0. easy. 
 split. unfold start,vsize. simpl.
 bdestruct (x =? x). simpl. unfold start,vsize in H5. rewrite eq1 in H5. simpl in H5. lia. lia.
 unfold avmap,start,trans_lshift.
 rewrite eq1. bdestruct (x =? x). simpl. easy. lia.
 simpl.
 specialize (H3 i H4).
 bdestruct (fst (avs i) =? x). rewrite H6 in H3.
 destruct H3 as [V1 [V2 V3]]. unfold start in V2. rewrite eq1 in V2. simpl in V2.
 unfold start in H5. rewrite eq1 in H5. simpl in H5. lia. 
 unfold start,vsize,avmap.
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H3. easy.
 specialize (H3 i H4).
 bdestruct (fst (avs i) =? x). rewrite H5 in H3.
 destruct H3 as [V1 [V2 V3]]. lia. simpl.
 unfold start,vsize,avmap. 
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H3. easy. lia.
-
 specialize (vs_avs_bij_r vs avs dim H3 H1) as Q1.
 specialize (vs_avs_size vs avs dim H3 H1) as Q2.
 unfold avs_prop. intros.
 subst.
 simpl. unfold trans_rshift,rshift_avs.
 destruct (vs x) as [p ag] eqn:eq1.
 destruct p as [p g]. destruct p as [st size].
 bdestruct (i <? dim).
 bdestruct ((start vs x <=? i)).
 bdestruct ((i - start vs x <? vsize vs x)). simpl.
 split.
 unfold start. bdestruct (x =? x). simpl.
 specialize (H3 i H4).
 bdestruct (fst (avs i) =? x). rewrite H7 in H3.
 destruct H3 as [V1 [V2 V3]]. unfold start in V1. rewrite eq1 in V1. simpl in V1. easy.
 specialize (var_not_over_lap_1 x (avs i) vs H2 H1) as eq2.
 apply eq2 in H7. destruct H7. rewrite Q1 in H7. lia. easy.
 rewrite Q1 in H7. lia. easy. apply Q2. easy. rewrite eq1. simpl.
 unfold start in H0. rewrite eq1 in H0. simpl in H0. easy. 
 split. unfold start,vsize. simpl.
 bdestruct (x =? x). simpl. unfold start,vsize in H5. rewrite eq1 in H5. simpl in H5. lia. lia.
 unfold avmap,start,trans_rshift.
 rewrite eq1. bdestruct (x =? x). simpl. easy. lia.
 simpl.
 specialize (H3 i H4).
 bdestruct (fst (avs i) =? x). rewrite H6 in H3.
 destruct H3 as [V1 [V2 V3]]. unfold start in V2. rewrite eq1 in V2. simpl in V2.
 unfold start in H5. rewrite eq1 in H5. simpl in H5. lia. 
 unfold start,vsize,avmap.
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H3. easy.
 specialize (H3 i H4).
 bdestruct (fst (avs i) =? x). rewrite H5 in H3.
 destruct H3 as [V1 [V2 V3]]. lia. simpl.
 unfold start,vsize,avmap. 
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H3. easy. lia.
-
 specialize (vs_avs_bij_r vs avs dim H3 H1) as Q1.
 specialize (vs_avs_size vs avs dim H3 H1) as Q2.
 unfold avs_prop. intros.
 subst.
 simpl. unfold trans_rev,rev_avs.
 destruct (vs x) as [p ag] eqn:eq1.
 destruct p as [p g]. destruct p as [st size].
 bdestruct (i <? dim).
 bdestruct ((start vs x <=? i)).
 bdestruct ((i - start vs x <? vsize vs x)). simpl.
 split.
 unfold start. bdestruct (x =? x). simpl.
 specialize (H3 i H4).
 bdestruct (fst (avs i) =? x). rewrite H7 in H3.
 destruct H3 as [V1 [V2 V3]]. unfold start in V1. rewrite eq1 in V1. simpl in V1. easy.
 specialize (var_not_over_lap_1 x (avs i) vs H2 H1) as eq2.
 apply eq2 in H7. destruct H7. rewrite Q1 in H7. lia. easy.
 rewrite Q1 in H7. lia. easy. apply Q2. easy. rewrite eq1. simpl.
 unfold start in H0. rewrite eq1 in H0. simpl in H0. easy. 
 split. unfold start,vsize. simpl.
 bdestruct (x =? x). simpl. unfold start,vsize in H5. rewrite eq1 in H5. simpl in H5. lia. lia.
 unfold avmap,start,trans_rev.
 rewrite eq1. bdestruct (x =? x). simpl. easy. lia.
 simpl.
 specialize (H3 i H4).
 bdestruct (fst (avs i) =? x). rewrite H6 in H3.
 destruct H3 as [V1 [V2 V3]]. unfold start in V2. rewrite eq1 in V2. simpl in V2.
 unfold start in H5. rewrite eq1 in H5. simpl in H5. lia. 
 unfold start,vsize,avmap.
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H3. easy.
 specialize (H3 i H4).
 bdestruct (fst (avs i) =? x). rewrite H5 in H3.
 destruct H3 as [V1 [V2 V3]]. lia. simpl.
 unfold start,vsize,avmap. 
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H3. easy. lia.
- simpl in *. subst. easy.
- simpl in *. subst. easy.
-
 subst. simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
 simpl.
 specialize (IHe1 dim vs v avs p0).
 rewrite eq1 in IHe1. simpl in IHe1.
 assert (v = v) by easy. assert (p0 = p0) by easy.
 specialize (IHe1 H H0 H1 H2 H3).
 apply (vars_anti_vs_same e1 dim vs v avs) in H1.
 apply (vars_sparse_vs_same e1 dim vs v avs) in H2.
 apply (IHe2 dim v v0 p0 p1). rewrite eq2. easy.
 rewrite eq2. easy. easy. easy. easy. rewrite eq1. easy.
 rewrite eq1. easy.
Qed.

Lemma efresh_trans_same: forall e dim vs vs' avs p, exp_fresh (size_env vs) p e -> 
                vs' = (snd (fst (trans_exp vs dim e avs))) ->
                 find_pos vs p = find_pos vs' p.
Proof.
 induction e; intros; subst; try easy.
 simpl in *.
 destruct (trans_exp vs dim e avs). destruct p1.
  simpl in *. easy.
 inv H. simpl. unfold or_not_eq in H2. destruct H2.
 unfold find_pos,trans_lshift,shift_fun.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap.
 bdestruct (v =? x). simpl in *. lia. easy.
 unfold find_pos,trans_lshift,shift_fun, size_env in *.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap,vsize in *.
 rewrite eq1 in *.
 bdestruct (v =? x). subst. simpl in *.
 bdestruct (n <? n3). lia. rewrite eq1 in *. simpl in *. easy. easy.
 inv H. simpl. unfold or_not_eq in H2. destruct H2.
 unfold find_pos,trans_rshift,shift_fun.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap.
 bdestruct (v =? x). simpl in *. lia. easy.
 unfold find_pos,trans_rshift,shift_fun, size_env in *.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap,vsize in *.
 rewrite eq1 in *.
 bdestruct (v =? x). subst. simpl in *.
 bdestruct (n <? n3). lia. rewrite eq1 in *. simpl in *. easy. easy.
 inv H. simpl. unfold or_not_eq in H2. destruct H2.
 unfold find_pos,trans_rev,shift_fun.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap.
 bdestruct (v =? x). simpl in *. lia. easy.
 unfold find_pos,trans_rev,shift_fun, size_env in *.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap,vsize in *.
 rewrite eq1 in *.
 bdestruct (v =? x). subst. simpl in *.
 rewrite eq1. simpl.
 unfold fbrev.
 bdestruct (n <? n3). lia. easy. easy.
 inv H. simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p0.
 destruct (trans_exp v dim e2 p1) eqn:eq2. destruct p0. simpl.
 specialize (IHe1 dim vs v avs p H3).
 rewrite IHe1.
 apply (IHe2 dim) with (avs := p1); try assumption.
 assert (size_env v = size_env vs).
 unfold size_env.
 apply functional_extensionality; intro.
 erewrite vsize_vs_same. easy.
 rewrite eq1. easy. rewrite H. easy.
 rewrite eq2. easy.
 rewrite eq1. easy.
Qed.

Check trans_exp.

Lemma list_neq {A:Type} : forall (l :list A) a, l <> (a :: l).
Proof.
  induction l; intros.
  easy.
  intros R. inv R. specialize (IHl a0). contradiction.
Qed.

(* Define two properties for neu. First, we show that for every x exp_neu_l l l',
        l' is either a subsequence of l or l is a subsequence of l'. 
   The secord property relates l l' with avs and avs', so
   for every exp_neu_l l l', if l is lated to avs then l' is also linked to avs' in someway. *)
Definition inter_neu_elem (s:sexp) (f:vars) (x:var) :=
   match s with Ls => trans_lshift f x
              | Rs => trans_rshift f x
              | Re => trans_rev f x
   end.


Fixpoint inter_neu_l (l :list sexp) (f:vars) (x:var) :=
    match l with [] => f
            | (a::al) => inter_neu_elem a (inter_neu_l al f x) x
    end.

Definition inter_neu_elem_anti (s:sexp) (f:vars) (x:var) :=
   match s with Ls => trans_rshift f x
              | Rs => trans_lshift f x
              | Re => trans_rev f x
   end.


Fixpoint inter_neu_l_anti (l :list sexp) (f:vars) (x:var) :=
    match l with [] => f
            | (a::al) => (inter_neu_l_anti al (inter_neu_elem_anti a f x) x)
    end.

Definition exp_neu_trans_prop (x:var) (l l' : list sexp) (vs vs' : vars) :=
       vs' x = inter_neu_l l' (inter_neu_l_anti l vs x) x x.

Lemma shift_fun_twice_same : forall f size, shift_fun (shift_fun f (size-1) size) 1 size = f.
Proof.
  intros. unfold shift_fun.
  apply functional_extensionality. intros.
  bdestruct (x <? size).
  assert (0 < size) by lia.
  bdestruct ((x + 1) mod size <? size).
  assert (x+1 <= size) by lia.
  bdestruct (x + 1 =? size).
  rewrite H3.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_l.
  rewrite Nat.mod_small by lia.
  assert (x = size-1) by lia.
  rewrite H4. easy.
  assert (x + 1 < size) by lia.
  rewrite Nat.mod_small with (a := (x + 1)) by lia.
  assert (((x + 1 + (size - 1)) = x + size)) by lia.
  rewrite H5.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia. rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  assert ((x + 1) mod size < size).
  apply Nat.mod_upper_bound. lia.
  lia. easy.
Qed.

Lemma shift_fun_twice_same_1 : forall f size, shift_fun (shift_fun f 1 size) (size-1) size = f.
Proof.
  intros. unfold shift_fun.
  apply functional_extensionality. intros.
  bdestruct (x <? size).
  assert (0 < size) by lia.
  bdestruct ((x + (size - 1)) mod size <? size).
  rewrite Nat.add_mod by lia.
  bdestruct (size =? 1). subst.
  rewrite Nat.mod_same by lia. rewrite plus_0_r.
  assert ((x + (1 - 1)) = x) by lia. rewrite H2.
  repeat rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  rewrite Nat.mod_mod by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((x + (size - 1) + 1) = x + size) by lia.
  rewrite H3.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia. rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  assert ((x + (size - 1)) mod size < size).
  apply Nat.mod_upper_bound ; lia. lia. easy.
Qed.

Lemma ashift_fun_twice_same : forall f size,
    (forall i, i < size -> f i < size) ->
    ashift_fun (ashift_fun f 1 size) (size-1) size = f.
Proof.
  intros. unfold ashift_fun.
  apply functional_extensionality. intros.
  bdestruct (x <? size).
  assert (0 < size) by lia.
  assert (f x < size). apply H. easy.
  bdestruct (f x + 1 =? size).
  rewrite H3.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_l.
  rewrite Nat.mod_small by lia.
  rewrite <- H3. lia.
  assert (f x + 1 < size) by lia.
  rewrite Nat.mod_small with (a := (f x + 1)) by lia.
  assert (((f x + 1 + (size - 1)) = f x + size)) by lia.
  rewrite H5.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia. rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  easy.
Qed.

Lemma ashift_fun_twice_same_1 : forall f size,
    (forall i, i < size -> f i < size) ->
    ashift_fun (ashift_fun f (size-1) size) 1 size = f.
Proof.
  intros. unfold ashift_fun.
  apply functional_extensionality. intros.
  bdestruct (x <? size).
  assert (0 < size) by lia.
  assert (f x < size). apply H. easy.
  rewrite Nat.add_mod by lia.
  bdestruct (size =? 1). subst.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_mod by lia.
  assert (1-1 = 0) by lia. rewrite H3.
  rewrite plus_0_r.
  rewrite Nat.mod_small by lia. easy. 
  rewrite Nat.mod_small with (a := ((f x + (size - 1)) mod size)).
  rewrite <- Nat.add_mod by lia.
  assert ((f x + (size - 1) + 1) = f x + size) by lia.
  rewrite H4.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_small with (a := f x) by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_small by lia. easy.
  apply Nat.mod_upper_bound. lia. easy.
Qed.

Lemma inter_neu_l_vars_anti_same : 
   forall l vs x, vars_anti_same vs -> vars_anti_same (inter_neu_l l vs x).
Proof.
  induction l;intros;simpl in *. easy.
  destruct a. simpl.
  specialize (vars_anti_vs_same (Lshift x) 0 (inter_neu_l l vs x) (snd
       (fst
          (trans_exp (inter_neu_l l vs x) 0 
             (Lshift x) (fun _ : nat => (0, 0))))) (fun _ => (0,0))) as eq1.
  apply eq1. easy. apply IHl. easy.
  simpl.
  specialize (vars_anti_vs_same (Rshift x) 0 (inter_neu_l l vs x) (snd
       (fst
          (trans_exp (inter_neu_l l vs x) 0 
             (Rshift x) (fun _ : nat => (0, 0))))) (fun _ => (0,0))) as eq1.
  apply eq1. easy. apply IHl. easy.
  simpl.
  specialize (vars_anti_vs_same (Rev x) 0 (inter_neu_l l vs x) (snd
       (fst
          (trans_exp (inter_neu_l l vs x) 0 
             (Rev x) (fun _ : nat => (0, 0))))) (fun _ => (0,0))) as eq1.
  apply eq1. easy. apply IHl. easy.
Qed.

Lemma afbrev_twice_same: forall size f,
      (forall i, i < size -> f i < size) ->
       afbrev (afbrev f size) size = f.
Proof.
  intros.
  unfold afbrev.
  apply functional_extensionality.
  intros.
  bdestruct (x <? size).
  assert (f x < size). apply H. easy.
  assert (0 < size) by lia.
  assert (f x <= size - 1) by lia.
  assert (size - 1 - (size - 1 - f x) = f x) by lia.
  rewrite H4. easy. easy.
Qed.

Lemma inter_neu_l_rev_same : forall (l: list sexp) vs vs1 x, inter_neu_l l vs x x = vs1 x ->
       vars_anti_same vs -> inter_neu_l_anti l vs1 x x = vs x.
Proof.
  induction l;intros;simpl in *. easy.
  assert (vars_anti_same (inter_neu_l l vs x)) as eq1. apply inter_neu_l_vars_anti_same. easy.
  destruct a. simpl in *.
  specialize (IHl vs (trans_rshift vs1 x) x).
  rewrite <- IHl. easy.
  unfold trans_rshift in *. rewrite <- H.
  unfold trans_lshift.
  destruct (inter_neu_l l vs x x) eqn:eq2. destruct p. destruct p.
  bdestruct (x =? x).
  bdestruct (x =? x).
  rewrite shift_fun_twice_same.
  rewrite ashift_fun_twice_same. easy.
  unfold vars_anti_same in H0.
  destruct (eq1 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  intros. specialize (X3 i).
  unfold vsize,avmap in X3. rewrite eq2 in *. simpl in X3. apply X3. easy.
  lia. lia. easy.
  simpl in *.
  specialize (IHl vs (trans_lshift vs1 x) x).
  rewrite <- IHl. easy.
  unfold trans_lshift in *. rewrite <- H.
  unfold trans_rshift.
  destruct (inter_neu_l l vs x x) eqn:eq2. destruct p. destruct p.
  bdestruct (x =? x).
  bdestruct (x =? x).
  rewrite shift_fun_twice_same_1.
  rewrite ashift_fun_twice_same_1. easy.
  unfold vars_anti_same in H0.
  destruct (eq1 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  intros. specialize (X3 i).
  unfold vsize,avmap in X3. rewrite eq2 in *. simpl in X3. apply X3. easy.
  lia. lia. easy.
  simpl in *.
  specialize (IHl vs (trans_rev vs1 x) x).
  rewrite <- IHl. easy.
  unfold trans_rev in *. rewrite <- H.
  destruct (inter_neu_l l vs x x) eqn:eq2. destruct p. destruct p.
  bdestruct (x =? x).
  bdestruct (x =? x).
  rewrite fbrev_twice_same.
  rewrite afbrev_twice_same. easy.
  unfold vars_anti_same in H0.
  destruct (eq1 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  intros. specialize (X3 i).
  unfold vsize,avmap in X3. rewrite eq2 in *. simpl in X3. apply X3. easy.
  lia. lia. easy.
Qed.

Lemma inter_neu_l_out : forall l vs x x0, x <> x0 -> inter_neu_l l vs x x0 = vs x0.
Proof.
  induction l; intros;simpl. easy.
  unfold inter_neu_elem.
  destruct a.
  unfold trans_lshift.
  destruct (inter_neu_l l vs x x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  rewrite IHl; try easy.
  unfold trans_rshift.
  destruct (inter_neu_l l vs x x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  rewrite IHl; try easy.
  unfold trans_rev.
  destruct (inter_neu_l l vs x x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  rewrite IHl; try easy.
Qed.

Lemma inter_neu_l_anti_out : forall l vs x x0, x <> x0 -> inter_neu_l_anti l vs x x0 = vs x0.
Proof.
  induction l; intros;simpl. easy.
  rewrite IHl; try easy.
  unfold inter_neu_elem_anti.
  destruct a.
  unfold trans_rshift.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia. easy.
  unfold trans_lshift.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia. easy.
  unfold trans_rev.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia. easy.
Qed.

Lemma inter_neu_anti_vars_anti_same : 
   forall l vs x, vars_anti_same vs -> vars_anti_same (inter_neu_l_anti l vs x).
Proof.
  induction l;intros;simpl in *. easy.
  destruct a. simpl.
  apply IHl.
  specialize (vars_anti_vs_same (Rshift x) 0 vs (snd
       (fst
          (trans_exp vs 0 
             (Rshift x) (fun _ : nat => (0, 0))))) (fun _ => (0,0))) as eq1.
  apply eq1. easy. easy.
  simpl.
  apply IHl.
  specialize (vars_anti_vs_same (Lshift x) 0 vs (snd
       (fst
          (trans_exp vs 0 
             (Lshift x) (fun _ : nat => (0, 0))))) (fun _ => (0,0))) as eq1.
  apply eq1. easy. easy.
  simpl. apply IHl.
  specialize (vars_anti_vs_same (Rev x) 0 vs (snd
       (fst
          (trans_exp vs 0 
             (Rev x) (fun _ : nat => (0, 0))))) (fun _ => (0,0))) as eq1.
  apply eq1. easy. easy.
Qed.

Lemma inter_neu_l_rev_same_1 : forall (l: list sexp) vs vs1 x, inter_neu_l_anti l vs x x = vs1 x ->
       vars_anti_same vs -> inter_neu_l l vs1 x x = vs x.
Proof.
  induction l;intros. easy.
  destruct a. simpl in *.
  specialize (vars_anti_vs_same (Rshift x) 0 vs (snd
       (fst
          (trans_exp vs 0 
             (Rshift x) (fun _ : nat => (0, 0))))) (fun _ => (0,0))) as eq1.
  simpl in eq1. apply eq1 in H0 as eq2. clear eq1.
  specialize (IHl (trans_rshift vs x) vs1 x).
  unfold trans_lshift in *. rewrite IHl; try easy.
  unfold trans_rshift. destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x).
  bdestruct (x =? x).
  rewrite shift_fun_twice_same_1.
  rewrite ashift_fun_twice_same_1. easy.
  unfold vars_anti_same in H0.
  destruct (H0 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  intros. specialize (X3 i).
  unfold vsize,avmap in X3. rewrite eq1 in *. simpl in *. apply X3. easy.
  lia. lia. easy.
  simpl in *.
  specialize (vars_anti_vs_same (Lshift x) 0 vs (snd
       (fst
          (trans_exp vs 0 
             (Lshift x) (fun _ : nat => (0, 0))))) (fun _ => (0,0))) as eq1.
  simpl in eq1. apply eq1 in H0 as eq2. clear eq1.
  specialize (IHl (trans_lshift vs x) vs1 x).
  unfold trans_rshift in *. rewrite IHl; try easy.
  unfold trans_lshift. destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x).
  bdestruct (x =? x).
  rewrite shift_fun_twice_same.
  rewrite ashift_fun_twice_same. easy.
  unfold vars_anti_same in H0.
  destruct (H0 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  intros. specialize (X3 i).
  unfold vsize,avmap in X3. rewrite eq1 in *. simpl in *. apply X3. easy.
  lia. lia. easy.
  simpl in *.
  specialize (vars_anti_vs_same (Rev x) 0 vs (snd
       (fst
          (trans_exp vs 0 
             (Rev x) (fun _ : nat => (0, 0))))) (fun _ => (0,0))) as eq1.
  simpl in eq1. apply eq1 in H0 as eq2. clear eq1.
  specialize (IHl (trans_rev vs x) vs1 x).
  unfold trans_rev in *. rewrite IHl; try easy.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x).
  bdestruct (x =? x).
  rewrite fbrev_twice_same.
  rewrite afbrev_twice_same. easy.
  unfold vars_anti_same in H0.
  destruct (H0 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  intros. specialize (X3 i).
  unfold vsize,avmap in X3. rewrite eq1 in *. simpl in *. apply X3. easy.
  lia. lia. easy.
Qed.

Lemma inter_neu_l_rev_same_1_gen : forall (l: list sexp) vs x,
   vars_anti_same vs ->
    inter_neu_l l (inter_neu_l_anti l vs x) x x = vs x.
Proof.
  intros.
  remember (inter_neu_l_anti l vs x) as vs1.
  rewrite inter_neu_l_rev_same_1 with (vs := vs). easy.
  rewrite Heqvs1. easy. easy.
Qed.

Lemma inter_neu_l_var_same: forall l x vs vs1, vs x = vs1 x -> inter_neu_l l vs x x = inter_neu_l l vs1 x x.
Proof.
  induction l;intros;simpl in *. easy.
  destruct a.
  simpl.
  unfold trans_lshift.
  rewrite IHl with (vs1 := vs1);try easy.
  destruct (inter_neu_l l vs1 x x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x). easy. lia.
  simpl.
  unfold trans_rshift.
  rewrite IHl with (vs1 := vs1);try easy.
  destruct (inter_neu_l l vs1 x x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x). easy. lia.
  simpl.
  unfold trans_rev.
  rewrite IHl with (vs1 := vs1);try easy.
  destruct (inter_neu_l l vs1 x x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x). easy. lia.
Qed.

Lemma inter_neu_l_vs_same: forall l vs vs' x, vs x = vs' x -> inter_neu_l l vs x x = inter_neu_l l vs' x x.
Proof.
  induction l; intros; simpl in *. easy.
  destruct a. simpl.
  unfold trans_lshift.
  rewrite IHl with (vs' := vs'); try easy. 
  destruct (inter_neu_l l vs' x x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x). easy. lia.
  simpl.
  unfold trans_rshift.
  rewrite IHl with (vs' := vs'); try easy. 
  destruct (inter_neu_l l vs' x x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x). easy. lia.
  simpl.
  unfold trans_rev.
  rewrite IHl with (vs' := vs'); try easy. 
  destruct (inter_neu_l l vs' x x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x). easy. lia.
Qed.

Lemma neu_l_trans_state : forall e l l' x (vs:vars) (dim:nat) (avs : nat -> posi),
      exp_neu_l x l e l' -> vars_anti_same vs ->
      exp_neu_trans_prop x l l' vs (snd (fst (trans_exp vs dim e avs))).
Proof.
  induction e; intros; simpl in *.
  inv H. unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  inv H. unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  inv H. unfold exp_neu_trans_prop in *.
  destruct (trans_exp vs dim e avs) eqn:eq1. destruct p0.
  simpl.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  inv H. unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  inv H. unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  inv H. unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  inv H. unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  inv H. unfold exp_neu_trans_prop in *.
  simpl.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  Check vars_anti_vs_same.
  specialize (vars_anti_vs_same (Lshift x) dim vs (trans_lshift vs x) avs) as eq1.
  simpl in eq1.
  apply eq1; try easy.
  unfold exp_neu_trans_prop in *.
  simpl.
  unfold trans_lshift.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  destruct (vs x) eqn:eq2. destruct p. destruct p.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  unfold trans_lshift.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia. easy.
  inv H. unfold exp_neu_trans_prop in *.
  simpl.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  Check vars_anti_vs_same.
  specialize (vars_anti_vs_same (Rshift x) dim vs (trans_rshift vs x) avs) as eq1.
  simpl in eq1.
  apply eq1; try easy.
  unfold exp_neu_trans_prop in *.
  simpl.
  unfold trans_rshift.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  destruct (vs x) eqn:eq2. destruct p. destruct p.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  unfold trans_rshift.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia. easy.
  inv H. unfold exp_neu_trans_prop in *.
  simpl.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  Check vars_anti_vs_same.
  specialize (vars_anti_vs_same (Rev x) dim vs (trans_rev vs x) avs) as eq1.
  simpl in eq1.
  apply eq1; try easy.
  unfold exp_neu_trans_prop in *.
  simpl.
  unfold trans_rev.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  destruct (vs x) eqn:eq2. destruct p. destruct p.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  unfold trans_rev.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia. easy.
  inv H. unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  inv H. unfold exp_neu_trans_prop in *.
  rewrite inter_neu_l_rev_same_1_gen; try easy.
  inv H.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
  simpl.
  specialize (IHe1 l l'0 x vs dim avs H4 H0).
  rewrite eq1 in IHe1.
  simpl in IHe1.
  assert (vars_anti_same v).
  Check (vars_anti_vs_same).
  specialize (vars_anti_vs_same e1 dim vs v avs) as eq3.
  rewrite eq1 in eq3.
  apply eq3; try easy.
  specialize (IHe2 l'0 l' x v dim p0 H6 H).
  rewrite eq2 in IHe2. simpl in *.
  unfold exp_neu_trans_prop in *.
  remember ((inter_neu_l_anti l vs x)) as vs1.
  symmetry.
  apply inter_neu_l_rev_same_1.
  rewrite Heqvs1.
  symmetry in IHe2.
  apply inter_neu_l_rev_same in IHe2.
  rewrite IHe2.
  apply inter_neu_l_rev_same.
  rewrite IHe1.
  subst. easy.
  apply inter_neu_anti_vars_anti_same. easy.
  apply inter_neu_anti_vars_anti_same. easy.
  specialize (vars_anti_vs_same e2 dim v v0 p0) as eq3.
  apply eq3;try easy.
  rewrite eq2. easy.
Qed.

Lemma trans_finnite_no_in : forall e vs avars dim avs,
      (forall u, In u (get_vars e) -> In u avars) ->
     (forall x, ~ In x avars -> snd (fst (trans_exp vs dim e avs)) x = vs x).
Proof.
  induction e; intros; simpl in *; try easy.
  destruct (trans_exp vs dim e avs). destruct p0.
  simpl in *. easy.
  unfold trans_lshift.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). subst.
  specialize (H x). 
  assert (x = x \/ False). left. easy. apply H in H1. contradiction. easy.
  unfold trans_rshift.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). subst.
  specialize (H x). 
  assert (x = x \/ False). left. easy. apply H in H1. contradiction. easy.
  unfold trans_rev.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). subst.
  specialize (H x). 
  assert (x = x \/ False). left. easy. apply H in H1. contradiction. easy.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0 ) eqn:eq2. destruct p.
  simpl in *.
  assert ((forall u : var, In u (get_vars e1) -> In u avars0)).
  intros. apply H. apply in_or_app. left. easy.
  specialize (IHe1 vs avars0 dim avs H1 x H0).
  rewrite eq1 in IHe1. simpl in IHe1.
  assert ((forall u : var, In u (get_vars e2) -> In u avars0)).
  intros. apply H. apply in_or_app. right. easy.
  specialize (IHe2 v avars0 dim p0 H2 x).
  apply IHe2 in H0.
  rewrite eq2 in H0. simpl in H0. rewrite IHe1 in H0. easy.
Qed.


Lemma neu_trans_state : forall e vs dim avs, exp_neu (get_vars e) e
    -> vars_anti_same vs -> (snd (fst (trans_exp vs dim e avs))) = vs.
Proof.
  intros.
  apply functional_extensionality; intro.
  assert (In x (get_vars e) \/ ~ In x (get_vars e)).
  destruct (@in_dec var Nat.eq_dec x (get_vars e)). left. easy. right. easy.
  destruct H1.
  unfold exp_neu in *. specialize (H x). apply H in H1.
  specialize (neu_l_trans_state e ([]) ([]) x vs dim avs H1 H0) as eq1.
  unfold exp_neu_trans_prop in *. simpl in *. easy.
  rewrite trans_finnite_no_in with (avars := get_vars e); try easy.
Qed.

Lemma avs_out_1 : forall e vs dim avs,
      (forall i, dim <= i -> snd (trans_exp vs dim e avs) i = avs i).
Proof.
  induction e; intros; try easy.
  simpl in *.
  destruct (trans_exp vs dim e avs) eqn:eq1. destruct p0.  simpl. easy.
  simpl in *.
  unfold lshift_avs.
  bdestruct (i <? dim). lia.
  simpl. easy.
  simpl in *.
  unfold rshift_avs.
  bdestruct (i <? dim). lia.
  simpl. easy.
  simpl in *.
  unfold rev_avs.
  bdestruct (i <? dim). lia.
  simpl. easy.
  simpl in *.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
  simpl in *.
  specialize (IHe1 vs dim avs i).
  apply IHe1 in H as X1.
  rewrite eq1 in *. simpl in *. rewrite <- X1.
  specialize (IHe2 v dim p0 i).
  apply IHe2 in H as X2.
  rewrite eq2 in *. simpl in *. easy.
Qed.

Lemma avs_prop_trans_fst_same : forall e vs dim avs, avs_prop vs avs dim ->
        vars_anti_same vs -> vars_sparse vs ->
         (forall i, i < dim -> fst ((snd  (trans_exp vs dim e avs)) i) = fst (avs i)).
Proof.
  induction e; intros; try easy.
  simpl in *. destruct (trans_exp vs dim e avs) eqn:eq1. destruct p0.
  simpl in *. easy.
  simpl.
  unfold lshift_avs.
  bdestruct (i <? dim).
  bdestruct ((start vs x <=? i)).
  bdestruct ((i - start vs x <? vsize vs x)).
  simpl.
  bdestruct (fst (avs i) =? x). easy.
  Check var_not_over_lap_1.
  specialize (var_not_over_lap_1 x (avs i) vs H1 H0) as eq1.
  apply eq1 in H6.
  destruct H6.
  rewrite vs_avs_bij_r with (dim := dim) in H6; try easy. lia.
  rewrite vs_avs_bij_r with (dim := dim) in H6; try easy. lia.
  apply vs_avs_size with (dim := dim) ; try easy.
  1-3:simpl; easy.
  simpl.
  unfold rshift_avs.
  bdestruct (i <? dim).
  bdestruct ((start vs x <=? i)).
  bdestruct ((i - start vs x <? vsize vs x)).
  simpl.
  bdestruct (fst (avs i) =? x). easy.
  Check var_not_over_lap_1.
  specialize (var_not_over_lap_1 x (avs i) vs H1 H0) as eq1.
  apply eq1 in H6.
  destruct H6.
  rewrite vs_avs_bij_r with (dim := dim) in H6; try easy. lia.
  rewrite vs_avs_bij_r with (dim := dim) in H6; try easy. lia.
  apply vs_avs_size with (dim := dim) ; try easy.
  1-3:simpl; easy.
  simpl.
  unfold rev_avs.
  bdestruct (i <? dim).
  bdestruct ((start vs x <=? i)).
  bdestruct ((i - start vs x <? vsize vs x)).
  simpl.
  bdestruct (fst (avs i) =? x). easy.
  Check var_not_over_lap_1.
  specialize (var_not_over_lap_1 x (avs i) vs H1 H0) as eq1.
  apply eq1 in H6.
  destruct H6.
  rewrite vs_avs_bij_r with (dim := dim) in H6; try easy. lia.
  rewrite vs_avs_bij_r with (dim := dim) in H6; try easy. lia.
  apply vs_avs_size with (dim := dim) ; try easy.
  1-3:simpl; easy.
  simpl in *.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
  simpl in *.
  specialize (IHe1 vs dim avs H H0 H1 i H2).
  rewrite eq1 in IHe1. simpl in *.
  rewrite <- IHe1.
  Check avs_prop_vs_same.
  specialize (avs_prop_vs_same e1 dim vs v avs p0) as X1.
  rewrite eq1 in *. simpl in *.
  apply X1 in H0 as X2 ; try easy.
  Check vars_sparse_vs_same.
  specialize (vars_sparse_vs_same e1 dim vs v avs) as X3.
  rewrite eq1 in *. simpl in X3.
  assert (v = v) by easy. apply X3 in H3. clear X3.
  specialize (vars_anti_vs_same e1 dim vs v avs) as X3.
  rewrite eq1 in *.
  assert (v = v) by easy. apply X3 in H4. clear X3.
  specialize (IHe2 v dim p0 X2 H4 H3 i H2).
  rewrite eq2 in IHe2. simpl in *. easy.
  easy. easy.
Qed.

Lemma neu_trans_state_avs : forall e vs dim avs, avs_prop vs avs dim 
         -> vars_anti_same vs -> vars_sparse vs -> exp_com_WF vs dim ->
           exp_neu (get_vars e) e -> snd  (trans_exp vs dim e avs) = avs.
Proof.
  intros.
  specialize (neu_trans_state e vs dim avs H3 H0) as eq1.
  apply functional_extensionality; intro.
  bdestruct (x <? dim).
  remember (snd (fst (trans_exp vs dim e avs))) as vs'.
  remember (snd (trans_exp vs dim e avs)) as avs'.
  Check avs_prop_vs_same.
  specialize (avs_prop_vs_same e dim vs vs' avs avs' Heqvs' Heqavs' H0 H1 H) as eq2.
  rewrite eq1 in *.
  assert (exists i, x = find_pos vs i).
  exists (avs x).
  rewrite vs_avs_bij_r with (dim := dim); try easy.
  destruct H5. rewrite H5.
  Check avs_prop_trans_fst_same.
  assert (fst (avs' x) = fst (avs x)).
  rewrite Heqavs'.
  apply avs_prop_trans_fst_same; try easy.
  unfold avs_prop in *.
  specialize (H x H4). specialize (eq2 x H4).
  destruct H as [X1 [X2 X3]].
  destruct eq2 as [V1 [V2 V3]].
  rewrite H6 in *.
  rewrite X3 in V3. rewrite <- H5 in *.
  destruct (avs' x). destruct (avs x). simpl in *. subst. easy.
  rewrite avs_out_1. easy. lia.
Qed.


Local Transparent SQIR.ID SQIR.CNOT SQIR.X SQIR.Rz. 

Lemma vkron_fun_gt : forall i m (f : nat -> Vector 2) v, i <= m -> vkron i (update f m v) = vkron i f.
Proof.
  intros. induction i.
  simpl. easy.
  simpl.
  rewrite IHi by lia.
  rewrite update_index_neq. easy. lia.
Qed.

Lemma vkron_shift_gt : forall i m j (f : nat -> Vector 2) v, j < m ->
                vkron i (shift (update f j v) m) = vkron i (shift f m).
Proof.
  intros. induction i.
  simpl. easy.
  simpl.
  rewrite IHi by lia.
  assert (shift (update f j v) m i = shift f m i).
  unfold shift.
  rewrite update_index_neq. easy. lia.
  rewrite H0. easy.
Qed.


Lemma vkron_split_up : forall n i (f : nat -> Vector 2) v,
  (forall j, WF_Matrix (f j)) -> WF_Matrix v ->
(*  (forall j, j < n -> WF_Matrix (f j)) -> Maybe necessary? *)
  i < n ->
  vkron n (update f i v) = (vkron i f) ⊗ v ⊗ (vkron (n - (i + 1)) (shift f (i + 1))).
Proof.
  intros.
  rewrite (vkron_split n i).
  rewrite vkron_fun_gt by lia.
  assert ((n - 1 - i) = n - (i + 1)) by lia. rewrite H2.
  rewrite vkron_shift_gt.
  rewrite update_index_eq. easy. lia.
  intros.
  bdestruct (i =? j). subst.
  rewrite update_index_eq. assumption.
  rewrite update_index_neq.
  apply H. lia. lia.
Qed.

Lemma vkron_split_eup : forall dim p v (f : posi -> val) (vs:vars) avs rmax,
  find_pos vs p < dim ->
      (snd p < vsize vs (fst p)) ->
     (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
     (forall i, i < dim -> find_pos vs (avs i) = i) ->
  vkron dim (trans_state avs rmax (f [p |-> v]))
          = (vkron (find_pos vs p) (trans_state avs rmax f)) ⊗
            (compile_val v rmax) ⊗ (vkron (dim - ((find_pos vs p) + 1)) 
                      (shift (trans_state avs rmax f) ((find_pos vs p) + 1))).
Proof.
  intros.
  assert (vkron dim (trans_state avs rmax (f [p |-> v]))
      = vkron dim (update (trans_state avs rmax f) (find_pos vs p) (compile_val v rmax))).
  erewrite vkron_eq. reflexivity. intros.
  rewrite trans_state_update with (dim := dim) (vs := vs); try easy.
  rewrite H3.
  apply vkron_split_up; try easy.
  intros. auto with wf_db.
  auto with wf_db.
Qed.


Lemma denote_ID_1 : forall dim n, n < dim -> uc_eval (ID n) = I (2 ^ dim).
Proof.
  intros.
  rewrite denote_ID. unfold pad.
  bdestruct (n+1<=? dim).
  gridify. easy. lia.
Qed.

Lemma vkron_X : forall (n i : nat) (f : nat -> Vector 2),
  i < n ->
  (forall j, WF_Matrix (f j))  ->
  (uc_eval (SQIR.X i)) × (vkron n f) 
      = vkron i f ⊗ (σx × (f i)) ⊗ vkron (n - (i + 1)) (shift f (i + 1)).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (vkron_split n i f H0 H). 
  simpl; replace (n - 1 - i) with (n - (i + 1)) by lia.
  repad. 
  Msimpl. easy.
Qed.

Lemma vkron_Rz : forall (n i : nat) q (f : nat -> Vector 2),
  i < n ->
  (forall j, WF_Matrix (f j))  ->
  (uc_eval (SQIR.Rz q i)) × (vkron n f) 
      = vkron i f ⊗ (phase_shift q × f i) ⊗ vkron (n - (i + 1)) (shift f (i + 1)).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (vkron_split n i f H0 H). 
  simpl; replace (n - 1 - i) with (n - (i + 1)) by lia.
  repad. 
  Msimpl. easy.
Qed.

Lemma vkron_H : forall (n i : nat) (f : nat -> Vector 2),
  i < n ->
  (forall j, WF_Matrix (f j))  ->
  (uc_eval (SQIR.H i)) × (vkron n f) 
      = vkron i f ⊗ (hadamard × f i) ⊗ vkron (n - (i + 1)) (shift f (i + 1)).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (vkron_split n i f H0 H). 
  simpl; replace (n - 1 - i) with (n - (i + 1)) by lia.
  repad. 
  Msimpl. easy.
Qed.

Lemma is_fresh_sr_gates : forall m n size x dim vs, 0 < n -> m <= n -> m <= size
       -> n < vsize vs x -> vars_finite_bij vs
       -> is_fresh (find_pos vs (x,n)) (gen_sr_gate' vs dim x m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  specialize (finite_bij_inj vs x H3 0 n) as eq1.
  assert (0 < vsize vs x) by lia.
  specialize (eq1 H4 H2). lia.
  constructor.
  apply IHm; try lia. easy.
  apply fresh_app1.  
  specialize (finite_bij_inj vs x H3 m n) as eq1.
  assert (m < vsize vs x) by lia.
  specialize (eq1 H4 H2). lia.
Qed.


Lemma is_fresh_sr_gate_start : forall m n size x y dim vs, m <= size -> x <> y
       -> n < vsize vs x -> m <= vsize vs y -> 0 < vsize vs y -> vars_finite_bij vs -> vars_sparse vs
       -> is_fresh (find_pos vs (x,n)) (gen_sr_gate' vs dim y m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H4 x n H1) as eq1.
  specialize (finite_bij_lt vs H4 y 0 H3) as eq2.
  apply H5; try lia.
  constructor.
  apply IHm; try lia. easy. easy.
  apply fresh_app1.  
  specialize (finite_bij_lt vs H4 x n H1) as eq1.
  assert (m < vsize vs y) by lia.
  specialize (finite_bij_lt vs H4 y m H6) as eq2.
  apply H5; try lia.
Qed.

Lemma is_fresh_srr_gates : forall m n size x dim vs, 0 < n -> m <= n -> m <= size
       -> n < vsize vs x -> vars_finite_bij vs
       -> is_fresh (find_pos vs (x,n)) (gen_srr_gate' vs dim x m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  specialize (finite_bij_inj vs x H3 0 n) as eq1.
  assert (0 < vsize vs x) by lia.
  specialize (eq1 H4 H2). lia.
  constructor.
  apply IHm; try lia. easy.
  apply fresh_app1.  
  specialize (finite_bij_inj vs x H3 m n) as eq1.
  assert (m < vsize vs x) by lia.
  specialize (eq1 H4 H2). lia.
Qed.

Lemma is_fresh_srr_gate_start : forall m n size x y dim vs, m <= size -> x <> y
       -> n < vsize vs x -> m <= vsize vs y -> 0 < vsize vs y -> vars_finite_bij vs -> vars_sparse vs
       -> is_fresh (find_pos vs (x,n)) (gen_srr_gate' vs dim y m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H4 x n H1) as eq1.
  specialize (finite_bij_lt vs H4 y 0 H3) as eq2.
  apply H5; try lia.
  constructor.
  apply IHm; try lia. easy. easy.
  apply fresh_app1.  
  specialize (finite_bij_lt vs H4 x n H1) as eq1.
  assert (m < vsize vs y) by lia.
  specialize (finite_bij_lt vs H4 y m H6) as eq2.
  apply H5; try lia.
Qed.

Lemma is_fresh_rot_gate_start : forall m i n x y dim vs, m + i <= vsize vs y -> i < vsize vs y -> x <> y
       -> n < vsize vs x -> vars_finite_bij vs -> vars_sparse vs
       -> is_fresh (find_pos vs (x,n)) (controlled_rotations_gen vs dim y m i).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H3 x n H2) as eq1.
  specialize (finite_bij_lt vs H3 y i H0) as eq2.
  apply H4; try lia.
  destruct m.
  apply fresh_app1.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H3 x n H2) as eq1.
  specialize (finite_bij_lt vs H3 y i H0) as eq2.
  apply H4; try lia.
  constructor.
  apply IHm; try lia. easy. easy.
  apply fresh_CU.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H3 x n H2) as eq1.
  assert ((S m) + i < vsize vs y) by lia.
  specialize (finite_bij_lt vs H3 y (S m + i) H5) as eq2.
  apply H4; try lia.
  specialize (finite_bij_lt vs H3 x n H2) as eq1.
  specialize (finite_bij_lt vs H3 y i H0) as eq2.
  apply H4; try lia.
Qed.

Lemma is_fresh_qft_gate_start : forall m n b x y dim vs, m <= b <= (vsize vs y) -> 0 < vsize vs y -> x <> y
       -> n < vsize vs x -> vars_finite_bij vs -> vars_sparse vs
       -> is_fresh (find_pos vs (x,n)) (QFT_gen vs dim y m b).
Proof.
  induction m; intros; simpl. 
  specialize (finite_bij_lt vs H3 x n H2) as eq1.
  specialize (finite_bij_lt vs H3 y 0 H0) as eq2.
  apply fresh_app1. apply H4; try easy.
  destruct m. simpl.
  specialize (finite_bij_lt vs H3 x n H2) as eq1.
  specialize (finite_bij_lt vs H3 y 0 H0) as eq2.
  constructor.
  apply fresh_app1. apply H4; try easy.
  constructor.
  Local Transparent SQIR.H.
  apply fresh_app1.
  Local Opaque SQIR.H.  
  apply H4; try easy.
  apply is_fresh_rot_gate_start; try easy. lia.
  constructor.
  apply IHm; try lia. easy. easy.
  constructor.
  Local Transparent SQIR.H.
  apply fresh_app1.
  Local Opaque SQIR.H.
  assert (S m < vsize vs y) by lia.  
  specialize (finite_bij_lt vs H3 x n H2) as eq1.
  specialize (finite_bij_lt vs H3 y (S m) H5) as eq2.
  apply H4; try lia.
  apply is_fresh_rot_gate_start; try easy. lia. lia.
Qed.

Lemma is_fresh_h_gate_start : forall m n b x y dim vs, b + m <= (vsize vs y) -> 0 < vsize vs y -> x <> y
       -> n < vsize vs x -> vars_finite_bij vs -> vars_sparse vs
       -> is_fresh (find_pos vs (x,n)) (nH vs dim y m b).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H3 x n H2) as eq1.
  specialize (finite_bij_lt vs H3 y 0 H0) as eq2.
  apply H4; try lia.
  constructor.
  apply IHm; try easy. lia.
  Local Transparent SQIR.H.
  apply fresh_app1.
  Local Opaque SQIR.H.  
  specialize (finite_bij_lt vs H3 x n H2) as eq1.
  specialize (finite_bij_lt vs H3 y (b+m)) as eq2.
  apply H4; try easy.
  apply eq2. lia.
Qed.

Lemma fresh_is_fresh :
  forall e p vs (dim:nat) avs,
    exp_fresh (size_env vs) p e -> exp_WF (size_env vs) e ->
    snd p < vsize vs (fst p) ->
    vars_start_diff vs -> vars_finite_bij vs ->
    vars_sparse vs ->
      @is_fresh _ dim (find_pos vs p) (fst (fst (trans_exp vs dim e avs))).
Proof.
  intros.
  remember (find_pos vs p) as q.
  generalize dependent vs.
  generalize dependent avs.
  induction e; intros.
  subst.
  apply fresh_app1.
  inv H. inv H0.
  apply find_pos_prop; try assumption.
  subst.
  apply fresh_app1.
  inv H. inv H0.
  apply find_pos_prop; try assumption.
  simpl in *.
  destruct (trans_exp vs dim e avs) eqn:eq1. destruct p1.
  simpl in *.
  inv H. inv H0.
  assert (find_pos vs p = find_pos vs p) by easy.
  specialize (IHe avs vs H9 H7 H1 H2 H3 H4 H).
  rewrite eq1 in IHe. simpl in IHe.
  apply fresh_control.
  split.
  apply find_pos_prop; try easy. easy.
  simpl. subst. inv H. inv H0.
  apply fresh_app1.
  apply find_pos_prop; try assumption.
  subst. inv H. inv H0.
  simpl.
  apply fresh_app1.
  apply find_pos_prop; try assumption.
  subst. inv H. inv H0.
  simpl. unfold gen_sr_gate.
  unfold or_not_r in *.
  bdestruct (x =? fst p). subst. destruct H7. lia.
  specialize (is_fresh_sr_gates (S q0) (snd p) (S q0) (fst p) dim vs) as eq1.
  destruct p.
  simpl in *. unfold find_pos. apply eq1; try lia. easy.
  destruct p.
  specialize (is_fresh_sr_gate_start (S q0) n (S q0) v x dim vs) as eq1.
  apply eq1; try lia. iner_p. iner_p. simpl in *. iner_p. unfold size_env in *. lia.
   easy. easy.
  subst. inv H. inv H0.
  simpl. unfold gen_sr_gate.
  unfold or_not_r in *.
  bdestruct (x =? fst p). subst. destruct H7. lia.
  specialize (is_fresh_srr_gates (S q0) (snd p) (S q0) (fst p) dim vs) as eq1.
  destruct p.
  simpl in *. unfold find_pos. apply eq1; try lia. easy.
  destruct p.
  specialize (is_fresh_srr_gate_start (S q0) n (S q0) v x dim vs) as eq1.
  apply eq1; try lia. iner_p. iner_p. easy. unfold size_env in *. lia. easy. easy.
  inv H. simpl. inv H0.
  apply fresh_app1.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)).
  unfold find_pos. easy. rewrite H.
  unfold or_not_eq in H7.
  destruct H7.
  apply find_pos_prop; try assumption.
  destruct p. iner_p.
  unfold size_env in H0. destruct p. simpl in H1. simpl in H0.
  bdestruct (x =? v). subst.
  apply find_pos_prop; try assumption. iner_p.
  apply find_pos_prop; try assumption. iner_p.
  inv H. simpl. inv H0.
  apply fresh_app1.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)).
  unfold find_pos. easy. rewrite H.
  unfold or_not_eq in H7.
  destruct H7.
  apply find_pos_prop; try assumption.
  destruct p. iner_p.
  unfold size_env in H0. destruct p. simpl in H1. simpl in H0.
  bdestruct (x =? v). subst.
  apply find_pos_prop; try assumption. iner_p.
  apply find_pos_prop; try assumption. iner_p.
  inv H. simpl. inv H0.
  apply fresh_app1.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)).
  unfold find_pos. easy. rewrite H.
  unfold or_not_eq in H7.
  destruct H7.
  apply find_pos_prop; try assumption.
  destruct p. iner_p.
  unfold size_env in H0. destruct p. simpl in H1. simpl in H0.
  bdestruct (x =? v). subst.
  apply find_pos_prop; try assumption. iner_p.
  apply find_pos_prop; try assumption. iner_p.
  subst. inv H. inv H0. unfold or_not_eq in H7.
  simpl. unfold trans_qft.
  destruct H7.
  destruct p.
  constructor.
  apply is_fresh_qft_gate_start; try easy. 
  apply is_fresh_h_gate_start; try easy. unfold size_env in *. lia.
  destruct p. bdestruct (x =? v).  subst.
  unfold size_env in H. simpl in *. lia.
  constructor.
  apply is_fresh_qft_gate_start; try easy. lia.
  apply is_fresh_h_gate_start; try easy. unfold size_env in *. lia. lia.
  simpl in *. unfold trans_rqft.
  rewrite <- invert_fresh.
  subst. inv H. inv H0. unfold or_not_eq in H7.
  destruct H7. destruct p.
  constructor.
  apply is_fresh_qft_gate_start; try easy.
  apply is_fresh_h_gate_start; try easy. unfold size_env in *. lia.
  destruct p. bdestruct (x =? v).  subst.
  unfold size_env in H. simpl in *. lia.
  constructor.
  apply is_fresh_qft_gate_start; try easy. lia.
  apply is_fresh_h_gate_start; try easy. unfold size_env in *. lia. lia.
  simpl. subst. inv H. inv H0.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p0.
  destruct (trans_exp v dim e2 p1) eqn:eq2. destruct p0. simpl.
  apply fresh_seq; try assumption.
  assert (b = (fst (fst (trans_exp vs dim e1 avs)))). rewrite eq1. easy.
  rewrite H.
  apply IHe1; try assumption. easy.
  assert (b0 = (fst (fst (trans_exp v dim e2 p1)))). rewrite eq2. easy. subst.
  apply IHe2; try assumption.
  erewrite size_env_vs_same. apply H9. rewrite eq1. easy.
  apply (wf_vs_same e2 e1 avs dim vs v). easy. rewrite eq1. easy.
  rewrite (vsize_vs_same e1 dim vs v avs); try easy. rewrite eq1. easy.
  eapply vars_start_diff_vs_same. rewrite eq1. easy. easy.
  eapply vars_finite_bij_vs_same. rewrite eq1. easy. easy.
  eapply vars_sparse_vs_same. rewrite eq1. easy. easy.
  rewrite (efresh_trans_same e1 dim vs v avs p); try easy.
  rewrite eq1. easy.
Qed.

Lemma gen_sr_gate_uc_well_typed : forall n size x dim vs, n <= size <= vsize vs x ->
     0 < vsize vs x -> exp_com_WF vs dim -> uc_well_typed (gen_sr_gate' vs dim x n size).
Proof.
  induction n; intros; simpl.
  constructor. unfold exp_com_WF in H1.
  specialize (H1 (x,0)). apply H1. simpl. easy.
  constructor. apply IHn; try lia. easy.
  constructor.
  specialize (H1 (x,n)). apply H1. simpl. lia.
Qed.

Lemma rot_gate_uc_well_typed : forall n i x dim vs, n+i <= vsize vs x -> 
            i < vsize vs x -> exp_com_WF vs dim ->
            vars_start_diff vs -> vars_finite_bij vs -> vars_sparse vs
       -> uc_well_typed (controlled_rotations_gen vs dim x n i).
Proof.
  induction n; intros; simpl.
  constructor.
  specialize (H1 (x,i)). apply H1. simpl. easy.
  destruct n.
  constructor.
  specialize (H1 (x,i)). apply H1. simpl. easy.
  constructor.
  apply IHn; try easy. lia.
  repeat constructor.
  specialize (H1 (x,(S n + i))). apply H1. easy.
  specialize (H1 (x,i)). apply H1. easy.
  specialize (H1 (x,(S n + i))). apply H1. easy.
  specialize (H1 (x,i)). apply H1. easy.
  assert (start vs x + vmap vs x (S n + i)= find_pos vs (x,S n + i)).
  easy. rewrite H5.
  assert (start vs x + vmap vs x i = find_pos vs (x,i)).
  easy. rewrite H6.
  apply find_pos_prop; try easy. iner_p.
  specialize (H1 (x,i)). apply H1. easy.
  specialize (H1 (x,(S n + i))). apply H1. easy.
  specialize (H1 (x,i)). apply H1. easy.
  assert (start vs x + vmap vs x (S n + i)= find_pos vs (x,S n + i)).
  easy. rewrite H5.
  assert (start vs x + vmap vs x i = find_pos vs (x,i)).
  easy. rewrite H6.
  apply find_pos_prop; try easy. iner_p.
  specialize (H1 (x,i)). apply H1. easy.
Qed.

Lemma gen_qft_gate_uc_well_typed : forall n x b dim vs, n <= b <= (vsize vs x) ->
             0 < vsize vs x -> exp_com_WF vs dim -> 
                vars_start_diff vs -> vars_finite_bij vs -> vars_sparse vs ->
               uc_well_typed ((QFT_gen vs dim x n b)).
Proof.
  induction n; intros; simpl.
  constructor. unfold exp_com_WF in H1.  apply (H1 (x,0)).
  iner_p.
  constructor.
  apply IHn; try easy. lia.
  constructor.
  apply uc_well_typed_H.
   unfold exp_com_WF in H1.
  apply (H1 (x,n)). simpl. lia.
  apply rot_gate_uc_well_typed; try easy. lia.
  lia.
Qed.

Lemma h_gate_uc_well_typed : forall n x b vs dim, b + n <= (vsize vs x) -> 0 < vsize vs x
       -> exp_com_WF vs dim -> uc_well_typed (nH vs dim x n b).
Proof.
  induction n; intros; simpl.
  constructor. apply (H1 (x,0)). simpl. lia.
  constructor.
  apply IHn; try lia. easy.
  apply uc_well_typed_H.
  apply (H1 (x,b+n)). simpl in *. lia.
Qed.

Lemma gen_srr_gate_uc_well_typed : forall n size x dim vs, n <= size <= vsize vs x ->
     0 < vsize vs x -> exp_com_WF vs dim -> uc_well_typed (gen_srr_gate' vs dim x n size).
Proof.
  induction n; intros; simpl.
  constructor. unfold exp_com_WF in H1.
  specialize (H1 (x,0)). apply H1. iner_p.
  constructor. apply IHn; try lia. easy.
  constructor.
  specialize (H1 (x,n)). apply H1. simpl. lia.
Qed.

(* Type soundness Compilatoin Preservation. *)
Lemma trans_exp_uc_well_typed : forall e dim vs avs tenv tenv',
     vars_start_diff vs -> vars_finite_bij vs ->
       vars_sparse vs -> well_typed_oexp (size_env vs) tenv e tenv' -> exp_WF (size_env vs) e ->
            exp_com_WF vs dim ->  @uc_well_typed _ dim (fst (fst (trans_exp vs dim e avs))).
Proof.
  induction e; intros.
  constructor. apply H4. inv H3. unfold size_env in H6. easy.
  constructor. apply H4. inv H3. unfold size_env in H6. easy.
  simpl in *.
  destruct (trans_exp vs dim e avs) eqn:eq1. destruct p0. simpl.
  apply uc_well_typed_control.
  split. apply H4. inv H3. unfold size_env in *. easy.
  split. 
  assert (b = (fst (fst (trans_exp vs dim e avs)))).
  rewrite eq1. easy.
  rewrite H5.
  apply fresh_is_fresh; try assumption. inv H2. inv H6. easy.
  inv H3. easy. inv H3. unfold size_env in H8. easy.
  assert (b = (fst (fst (trans_exp vs dim e avs)))).
  rewrite eq1. easy.
  rewrite H5.
  apply IHe with (tenv:=tenv) (tenv':=tenv'); try easy.
  inv H2. inv H6. easy. inv H3. easy.
  constructor. apply H4. inv H3. unfold size_env in H6. easy.
  constructor. apply H4. inv H3. unfold size_env in H6. easy.
  simpl. unfold gen_sr_gate.
  apply gen_sr_gate_uc_well_typed; try easy.
  inv H3. easy. inv H3. unfold size_env in *. lia.
  simpl. unfold gen_srr_gate.
  apply gen_srr_gate_uc_well_typed; try easy.
  inv H3. easy. inv H3. unfold size_env in *. lia.
  simpl. constructor.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)). easy.
  rewrite H5. apply H4. inv H3. unfold size_env in H7. easy.
  simpl. constructor.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)). easy.
  rewrite H5. apply H4. inv H3. unfold size_env in H7. easy.
  simpl. constructor.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)). easy.
  rewrite H5. apply H4. inv H3. unfold size_env in H7. easy.
  simpl. unfold trans_qft. inv H3. inv H2. inv H3.
  constructor.
  apply gen_qft_gate_uc_well_typed; try easy.
  apply h_gate_uc_well_typed; try easy.
  unfold size_env in *. lia.
  simpl. unfold trans_rqft. inv H3. inv H2. inv H3.
  rewrite <- uc_well_typed_invert.
  constructor.
  apply gen_qft_gate_uc_well_typed; try easy.
  apply h_gate_uc_well_typed; try easy.
  unfold size_env in *. lia.
  simpl.
  inv H2. inv H5. inv H3.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
  constructor.
  assert ((fst (fst (trans_exp vs dim e1 avs))) = b). rewrite eq1. easy.
  rewrite <- H2.
  apply IHe1 with (tenv := tenv) (tenv' := env'); try easy.
  assert ((fst (fst (trans_exp v dim e2 p0))) = b0). rewrite eq2. easy.
  rewrite <- H2.
  apply IHe2 with  (tenv := env') (tenv' := tenv'); try easy.
  eapply vars_start_diff_vs_same. rewrite eq1. easy. easy.
  eapply vars_finite_bij_vs_same. rewrite eq1. easy. easy.
  eapply vars_sparse_vs_same. rewrite eq1. easy. easy.
  erewrite size_env_vs_same. apply H10. rewrite eq1. easy.
  eapply wf_vs_same. apply H7. rewrite eq1. easy.
  eapply exp_com_WF_vs_same. rewrite eq1. easy. easy.
Qed.


Check trans_qft. 

Lemma Mmult_adj_add : forall {n} (A: Matrix n n) (C D:Vector n), 
        WF_Unitary A -> WF_Matrix C ->  WF_Matrix D ->
        A † × A × C = A † × D -> A × C = D.
Proof.
  intros. unfold WF_Unitary in *. destruct H.
  rewrite H3 in H2. rewrite Mmult_1_l in H2; try easy.
  rewrite <- (@adjoint_involutive n n A).
  rewrite H2.
  rewrite <- Mmult_assoc.
  assert (WF_Unitary ((A) †)).
  apply transpose_unitary. unfold WF_Unitary. split. easy. easy.
  unfold WF_Unitary in H4. destruct H4.
  rewrite H5.
  rewrite Mmult_1_l; easy.
Qed.

Lemma two_n_kron_n: forall {m p} n i (A : Matrix m p),
  WF_Matrix A -> (i + n) ⨂ A = (n ⨂ A) ⊗ (i ⨂ A).
Proof.
  intros.
  induction n.
  simpl.
  Msimpl. rewrite plus_0_r.
  reflexivity.
  rewrite kron_n_assoc by assumption.
  restore_dims.
  rewrite kron_assoc.
  rewrite <- IHn.
  assert ((m ^ n * m ^ i) = m ^ (i + n)).
  rewrite Nat.pow_add_r. lia.
  rewrite H0. clear H0.
  assert ((p ^ n * p ^ i) = p ^ (i + n)).
  rewrite Nat.pow_add_r. lia.
  rewrite H0. clear H0.
  rewrite <- kron_n_assoc by assumption.
  assert ((i + S n) =  S (i + n)) by lia.
  rewrite H0. easy.
  assumption.
  auto with wf_db.
  auto with wf_db.
Qed.

Lemma uc_cnot_control : forall (n i j : nat),
  i < n -> j < n -> i <> j ->
  (@uc_eval n (SQIR.CNOT i j)) = (uc_eval (control i (SQIR.X j))).
Proof.
  intros.
  rewrite control_correct.
  autorewrite with eval_db.
  bdestruct ( i <? j).
  assert ((i + (1 + (j - i - 1) + 1)) = j + 1) by lia.
  rewrite H3. 
  bdestruct (j + 1 <=? n).
  unfold proj,pad.
  bdestruct (i + 1 <=? n).
  simpl.
  autorewrite with ket_db.
  rewrite Mplus_comm.
  restore_dims.
  rewrite kron_plus_distr_l.
  rewrite kron_plus_distr_r.
  rewrite kron_assoc.
  rewrite kron_assoc.
  assert ((I 2 ⊗ I (2 ^ (n - (j + 1)))) = I (2^ S (n - (j + 1)))).
  rewrite <- kron_n_I.
  rewrite <- kron_n_assoc.
  rewrite kron_n_I. easy.
  auto with wf_db.
  rewrite H6.
  rewrite kron_assoc.
  assert ((I (2 ^ (j - i - 1)) ⊗ I (2 ^ S (n - (j + 1)))) = I (2 ^ (n - (i + 1)))).
  Check @kron_n_I.
  Check two_n_kron_n.
  rewrite <- kron_n_I.
  rewrite <- kron_n_I.
  rewrite <- two_n_kron_n.
  rewrite kron_n_I.
  assert ((S (n - (j + 1)) + (j - i - 1)) = (n - (i + 1))) by lia.
  rewrite H7. easy. 
  auto with wf_db.
  restore_dims.
  rewrite H7.
  gridify. easy.
  1-9:auto with wf_db.
  lia. lia.
  bdestruct (j <? i).
  assert (j + (1 + (i - j - 1) + 1) = i + 1) by lia.
  rewrite H4. 
  unfold proj,pad.
  bdestruct (i + 1 <=? n).
  bdestruct (j + 1 <=? n).
  simpl.
  autorewrite with ket_db.
  rewrite Mplus_comm.
  restore_dims.
  rewrite kron_plus_distr_l.
  gridify. easy. lia. lia. lia.
  constructor. easy.
  constructor. easy.
Qed.

Lemma vkron_proj_eq : forall f q n r b,
  (forall j : nat, WF_Matrix (f j)) ->
  q < n -> f q = r .* ket (Nat.b2n b) -> 
  proj q n b × (vkron n f) = vkron n f.
Proof.
  intros f q n r b ? ? ?.
  rewrite (vkron_split n q) by (try assumption; try lia). 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad.
  gridify. 
  do 2 (apply f_equal2; try reflexivity). 
  rewrite H1. destruct b; solve_matrix.
Qed.

Lemma vkron_proj_neq : forall f q n r b b',
  (forall j : nat, WF_Matrix (f j)) ->
  q < n -> f q = r .* ket (Nat.b2n b) -> b <> b' ->
  proj q n b' × (vkron n f) = Zero.
Proof.
  intros f q n r b b' ? ? H ?.
  rewrite (vkron_split n q) by (try assumption; try lia). 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad.
  gridify. rewrite H.
  destruct b. destruct b'. contradiction. lma.
  destruct b'.  lma. contradiction.
Qed.



Local Opaque SQIR.ID SQIR.CNOT SQIR.X SQIR.Rz. 

Lemma trans_exp_cu_eval : forall vs avs dim p e, 
                 (uc_eval (fst (fst (trans_exp vs dim (CU p e) avs)))) = 
                    (uc_eval (control (find_pos vs p) (fst (fst (trans_exp vs dim e avs))))).
Proof.
  intros.
  simpl. destruct (trans_exp vs dim e avs) eqn:eq1. destruct p0.
  simpl. easy.
Qed.

Lemma rotate_sn_eq : forall n r, rotate r 1 (S n) = r (S n).
Proof.
  intros.
  unfold rotate,addto.
  bdestruct (S n <? 1). lia. easy.
Qed.

Lemma turn_angle_r_cut_n : forall n m size r, n <= m <= size -> turn_angle_r (cut_n r m) n size = turn_angle_r r n size.
Proof.
  induction n;intros;simpl. easy.
  rewrite IHn by lia.
  assert (cut_n r m n = r n).
  unfold cut_n. bdestruct (n <? m). easy. lia. rewrite H0. easy.
Qed.

Lemma turn_angle_r_low_bit_same :
       forall i q n r, i <= n - q < n -> (forall i, n <= i -> r i = false) -> 
       turn_angle_r (fbrev n r) i n = turn_angle_r (fbrev n (rotate r q)) i n.
Proof.
  induction i ; intros; simpl.
  easy.
  assert (fbrev n r i = fbrev n (rotate r q) i).
  unfold rotate.
  rewrite add_to_sem with (n := n); try lia.
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  specialize (f_num_0 (fbrev n r) n) as eq1.
  destruct eq1.
  assert (cut_n (fbrev n r) n = fbrev n r).
  unfold cut_n,fbrev.
  apply functional_extensionality; intro.
  bdestruct (x0 <? n). easy.
  rewrite H0. easy. lia.
  rewrite H2 in H1. rewrite H1.
  rewrite sumfb_correct_carry0.
  unfold cut_n.
  bdestruct (i <? n).
  rewrite low_bit_same. easy. lia. lia. lia.
  intros. rewrite H0. easy. lia.
  rewrite H1.
  rewrite IHi with (q := q); try easy. lia.
Qed.

Lemma turn_angle_r_false_0 : forall n size r, n <= size -> (forall i, i < n -> r i = false)
               -> turn_angle_r r n size = 0%R.
Proof.
  induction n; intros; simpl. easy.
  rewrite H0 by lia. rewrite IHn; try lia. lra.
  intros. rewrite H0 by lia. easy.
Qed.

Lemma turn_angle_r_split :
       forall n i r size, i <= n <= size ->
       turn_angle_r r n size = (turn_angle_r r i size + turn_angle_r (fb_push_n i (shift r i)) n size)%R.
Proof.
  induction n; intros; simpl.
  assert (i = 0) by lia. subst. simpl. lra.
  bdestruct (i =? S n). subst.
  simpl.
  assert (fb_push false (fb_push_n n (shift r (S n))) = fb_push_n (S n) (shift r (S n))) by easy.
  rewrite H0.
  rewrite fb_push_n_false by lia.
  rewrite turn_angle_r_false_0 with (r := (fb_push_n (S n) (shift r (S n)))); try lia.
  rewrite Rplus_0_r.
  rewrite Rplus_0_r.
  easy.
  intros.
  rewrite fb_push_n_false. easy. lia.
  rewrite IHn with (i := i); try lia.
  assert (fb_push_n i (shift r i) n = r n).
  assert (fb_push_n i (shift r i) n = fb_push_n i (shift r i) (i + (n-i))).
  assert (i + (n-i) = n) by lia. rewrite H1. easy.
  rewrite H1.
  rewrite fb_push_nsame.
  unfold shift.
  assert ((n - i + i) = n) by lia.
  rewrite H2. easy.
  rewrite H1. lra.
Qed.

Lemma turn_angle_fb_push: forall n size r, n <= size
       -> (turn_angle_r (fb_push false r) n size) = (2 * turn_angle_r r (n-1) size)%R.
Proof.
  induction n; intros; simpl. 
  rewrite Rmult_0_r. easy.
  rewrite IHn by lia.
  assert ((n - 0) = n) by lia. rewrite H0.
  destruct (n). simpl. lra.
  assert ((S n0 - 1)  = n0) by lia. rewrite H1. simpl.
  destruct (r n0) eqn:eq1.
  assert ((size - n0) = S (size- S n0)) by lia.
  rewrite H2.
  remember (size - S n0) as q.
  simpl. rewrite Rmult_plus_distr_l. autorewrite with R_db trig_db.
  rewrite Rinv_mult_distr. lra. lra.
  apply pow_nonzero. lra.
  rewrite Rplus_0_l.
  rewrite Rplus_0_l. easy.
Qed.

Lemma turn_angle_fb_push_n: forall m n size r, m <= n <= size
       -> (turn_angle_r (fb_push_n m r) n size) = (2^m * turn_angle_r r (n-m) size)%R.
Proof.
  induction m; intros; simpl. 
  replace (n - 0) with n by lia. rewrite Rmult_1_l. easy.
  rewrite turn_angle_fb_push by lia.
  rewrite IHm by lia.
  assert ((n - 1 - m) = n - S m) by lia.
  rewrite H0. lra.
Qed.

Lemma turn_angle_r_fun_same : forall n size f g, n <= size -> (forall i, i < n -> f i = g i) ->
         turn_angle_r f n size = turn_angle_r g n size.
Proof.
  induction n; intros; simpl. easy.
  rewrite H0. rewrite IHn with (g := g) ; try lia. easy.
  intros. rewrite H0. easy. lia. lia.
Qed.

Lemma fb_push_shift_anti : forall n f, shift (fb_push_n n f) n = f.
Proof.
  induction n; intros; simpl.
  rewrite shift_0. easy.
  remember (fb_push false (fb_push_n n f)) as g.
  assert (shift g (S n) = shift (shift g 1) n).
  unfold shift.
  apply functional_extensionality; intro.
  assert (x + S n = x + n + 1) by lia. rewrite H. easy.
  rewrite H. subst.
  remember (fb_push_n n f) as g.
  assert ((shift (fb_push false g) 1) = g).
  apply functional_extensionality; intro.
  unfold shift,fb_push.
  destruct (x + 1) eqn:eq1. lia.
  assert (x = n0) by lia. rewrite H0. easy.
  rewrite H0. subst. rewrite IHn. easy.
Qed.

Lemma nat2fb_pow_shift_n : forall n x, nat2fb (x) = (shift (nat2fb (2^n * x)) n).
Proof.
  induction n;intros. simpl. 
  rewrite plus_0_r.
  rewrite shift_0. easy.
  assert ((2 ^ S n * x) = 2 * (2^n * x)) by (simpl;lia).
  rewrite H.
  rewrite <- times_two_correct.
  rewrite IHn.
  remember (times_two_spec (nat2fb (2 ^ n * x))) as g.
  assert (shift g (S n) = shift (shift g 1) n).
  unfold shift.
  apply functional_extensionality; intro.
  assert (x0 + S n = x0 + n + 1) by lia. rewrite H0. easy.
  rewrite H0. subst.
  assert ((shift (times_two_spec (nat2fb (2 ^ n * x))) 1) = (nat2fb (2 ^ n * x))).
  unfold shift,times_two_spec.
  apply functional_extensionality; intro.
  bdestruct (x0 + 1 =? 0). lia.
  assert ((x0 + 1 - 1) = x0) by lia. rewrite H2. easy.
  rewrite H1. easy.
Qed.

Lemma turn_angle_r_bin : forall n size x, n <= size -> 
      turn_angle_r (nat2fb x) n size = (1 / 2^size * INR (bindecomp n x))%R.
Proof.
  induction n;intros;simpl.
  lra.
  rewrite bindecomp_seq.
  destruct (nat2fb x n) eqn:eq1. simpl.
  rewrite plus_0_r.
  rewrite IHn.
  rewrite plus_INR.
  rewrite Rmult_plus_distr_l.
  rewrite pow_INR.
  assert ((IZR (Zpos (xO xH))) = (INR (S (S O)))).
  rewrite INR_IZR_INZ.
  rewrite <- positive_nat_Z.
  assert ((Pos.to_nat 2) = 2) by lia.
  rewrite H0. easy.
  rewrite <- H0.
  autorewrite with R_db.
  assert (size = (size - n) + n)%nat by lia.
  assert (/ 2 ^ size * 2 ^ n  = / 2 ^ ((size - n) + n) * 2 ^ n)%R.
  rewrite <- H1. easy. rewrite H2.
  rewrite pow_add.
  rewrite Rinv_mult_distr.
  rewrite Rmult_assoc.
  rewrite <- Rinv_l_sym. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra. lia.
  simpl. rewrite plus_0_r. rewrite IHn. lra. lia.
Qed.

Lemma turn_angle_r_add_1_lt : forall n size x, 0 < n <= size -> x < 2^ n - 1 ->
    (turn_angle_r (nat2fb x) n size + 1/(2^size))%R = turn_angle_r (nat2fb (x+1)) n size.
Proof.
  intros.
  rewrite turn_angle_r_bin by lia.
  rewrite turn_angle_r_bin by lia.
  rewrite bindecomp_spec. rewrite bindecomp_spec.
  rewrite Nat.mod_small by lia.
  rewrite Nat.mod_small by lia.
  rewrite plus_INR.
  rewrite Rmult_plus_distr_l. simpl. lra.
Qed.

Lemma turn_angle_add_same : forall n r q, q <= n ->
       Cexp (2 * PI * turn_angle r n + rz_ang q)
            = Cexp (2 * PI *  turn_angle (rotate r q) n).
Proof.
  intros.
  bdestruct (q =? 0). subst. unfold rotate,rz_ang. simpl. rewrite addto_0.
  rewrite Cexp_add.
  assert ((2 * PI / 1) = 2 * PI)%R by lra.
  rewrite H0. rewrite Cexp_2PI. lca.
  unfold turn_angle. 
  rewrite <- turn_angle_r_cut_n with (m := n) by lia.
  rewrite <- turn_angle_r_cut_n with (r := (fbrev n (rotate r q))) (m := n) by lia.
  rewrite turn_angle_r_split with (i := n - q) ; try lia.
  rewrite turn_angle_r_split with (r := (cut_n (fbrev n (rotate r q)) n)) (i := n - q) ; try lia.
  assert (turn_angle_r (cut_n (fbrev n (rotate r q)) n) (n - q) n
             = turn_angle_r (cut_n (fbrev n r) n) (n - q) n).
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_fbrev_flip.
  assert ((cut_n (rotate r q) n) = rotate (cut_n r n) q).
  rewrite addto_cut_n by lia. easy.
  rewrite H1.
  rewrite <- turn_angle_r_low_bit_same; try lia. easy.
  intros. unfold cut_n. bdestruct (i <? n). lia. easy.
  rewrite H1.
  unfold rz_ang.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_l.
  rewrite turn_angle_fb_push_n.
  rewrite turn_angle_fb_push_n.
  assert ((n - (n - q)) = q) by lia. rewrite H2.
  assert (forall i, i < q -> (shift (cut_n (fbrev n (rotate r q)) n) (n - q)) i
           = (cut_n (sumfb false (shift (cut_n (fbrev n r) n) (n-q)) (nat2fb 1)) n) i).
  intros. unfold rotate.
  rewrite cut_n_fbrev_flip.
  rewrite <- addto_cut_n by lia.
  rewrite add_to_sem with (n := n); try lia.
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite <- cut_n_fbrev_flip.
  rewrite <- f_twoton_eq.
  unfold shift,cut_n.
  bdestruct (i + (n - q) <? n). bdestruct (i <? n).
  unfold sumfb.
  assert (twoton_fun (n - q) (i + (n - q))  = nat2fb 1 i).
  assert (1 = 2^0) by (simpl; easy).
  rewrite H6.
  rewrite <- f_twoton_eq.
  unfold twoton_fun.
  bdestruct (i + (n-q) <? n-q). bdestruct (i <? 0). easy. lia.
  bdestruct (i <? 0). lia.
  bdestruct (i + (n-q) =? n-q). bdestruct (i =? 0). easy. lia.
  bdestruct (i =? 0). lia. easy.
  rewrite H6.
  assert (forall i, i + (n-q) = (n-q) + i) by lia. rewrite H7.
  rewrite carry_add_index with (s := (fun i0 : nat =>
    if i0 + (n - q) <? n
         then fbrev n r (i0 + (n - q)) else allfalse (i0 + (n - q)))) (t := nat2fb 1); try easy.
  rewrite carry_twoton_less. easy. lia.
  intros. rewrite H7. easy.
  intros.
  assert (1 = 2^0) by (simpl; easy).
  rewrite H9.
  rewrite <- f_twoton_eq.
  unfold twoton_fun.
  bdestruct (n - q + i0 <? n-q). bdestruct (i0 <? 0). easy. lia.
  bdestruct (i0 <? 0). lia.
  bdestruct (n - q + i0  =? n-q). bdestruct (i0 =? 0). easy. lia.
  bdestruct (i0 =? 0). lia. easy. lia. lia.
  intros. unfold cut_n.
  bdestruct (i0 <? n). lia. easy.
  rewrite turn_angle_r_fun_same with (f := (shift (cut_n (fbrev n (rotate r q)) n) (n - q)))
    (g := cut_n (sumfb false (shift (cut_n (fbrev n r) n) (n - q)) (nat2fb 1)) n); try easy.
  remember ((shift (cut_n (fbrev n r) n) (n - q)) ) as g.
  rewrite turn_angle_r_cut_n with (r := (sumfb false g (nat2fb 1))) by lia.
  assert (g = cut_n g q).
  subst.
  unfold shift,cut_n.
  apply functional_extensionality; intro.
  bdestruct (x + (n-q) <? n). bdestruct (x <? q). easy. lia.
  bdestruct (x <? q). lia. easy.
  rewrite H4.
  specialize (f_num_0 g q) as eq1.
  destruct eq1. rewrite H5.
  rewrite sumfb_correct_carry0.
  bdestruct (x <? 2^ q - 1).
  rewrite <- turn_angle_r_add_1_lt ; try lia.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_l.
  autorewrite with R_db.
  assert ((2 ^ (n - q) * / 2 ^ n)= / 2 ^ q)%R.
  assert (n = (n-q) + q) by lia.
  assert (2 ^ n = 2^((n-q)+q))%R. rewrite <- H7. easy.
  rewrite H8.
  rewrite pow_add.
  rewrite Rinv_mult_distr.
  rewrite <- Rmult_assoc.
  rewrite Rinv_r. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  rewrite H7.
  rewrite Rplus_assoc. easy.
  apply f_num_small in H5.
  assert (x = 2^q - 1) by lia. subst.
  assert ( (2 ^ q - 1 + 1)  = 2^q) by lia.
  rewrite H7.
  rewrite turn_angle_r_bin by lia.
  rewrite turn_angle_r_bin by lia.
  rewrite bindecomp_spec.
  rewrite bindecomp_spec.
  rewrite Nat.mod_same.
  simpl.
  repeat rewrite Rmult_0_r.
  rewrite Rplus_0_r.
  rewrite Nat.mod_small by lia.
  rewrite minus_INR.
  assert ((2 ^ (n - q) * (1 / 2 ^ n * (INR (2 ^ q) - INR 1))) = / 2^q * (INR (2 ^ q) - INR 1))%R.
  rewrite <- Rmult_assoc.
  assert (n = n-q + q) by lia.
  assert ((1 / 2 ^ n) = 1 / 2^(n-q+q))%R. rewrite <- H8. easy.
  rewrite H9.
  autorewrite with R_db.
  rewrite pow_add.
  rewrite Rinv_mult_distr.
  rewrite <- Rmult_assoc.
  rewrite Rinv_r. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  rewrite H8.
  autorewrite with R_db.
  rewrite Rplus_assoc.
  rewrite Cexp_add.
  rewrite <- Rmult_plus_distr_l.
  assert ((/ 2 ^ q * (INR (2 ^ q) + - INR 1) + / 2 ^ q) =
          (/ 2 ^ q * (INR (2 ^ q) + - INR 1) + / 2 ^ q * INR 1))%R.
  simpl. lra. rewrite H9.
  rewrite <- Rmult_plus_distr_l. simpl.
  assert ((INR (2 ^ q) + - (1) + 1) = INR (2^q))%R by lra.
  rewrite H10.
  rewrite pow_INR.
  assert ((IZR (Zpos (xO xH))) = (INR (S (S O)))).
  rewrite INR_IZR_INZ.
  rewrite <- positive_nat_Z.
  assert ((Pos.to_nat 2) = 2) by lia.
  rewrite H11. easy.
  rewrite <- H11.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  rewrite Cexp_2PI. lca.
  apply pow_nonzero. lra.
  assert (2 ^ q <> 0)%R.
  apply pow_nonzero. lra. lia.
  apply Nat.pow_nonzero. lia. lia. lia.
Qed.

Lemma turn_angle_r_low_bit_same_r :
       forall i q n r, i <= n - q < n -> (forall i, n <= i -> r i = false) -> 
       turn_angle_r (fbrev n r) i n = turn_angle_r (fbrev n (r_rotate r q)) i n.
Proof.
  induction i ; intros; simpl.
  easy.
  assert (fbrev n r i = fbrev n (r_rotate r q) i).
  unfold r_rotate.
  rewrite add_to_n_sem with (n := n); try lia.
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  specialize (f_num_0 (fbrev n r) n) as eq1.
  destruct eq1.
  assert (cut_n (fbrev n r) n = fbrev n r).
  unfold cut_n,fbrev.
  apply functional_extensionality; intro.
  bdestruct (x0 <? n). easy.
  rewrite H0. easy. lia.
  rewrite H2 in H1. rewrite H1.
  rewrite sumfb_correct_carry0.
  unfold cut_n.
  bdestruct (i <? n).
  rewrite low_bit_same_minus. easy. lia. lia. lia.
  intros. rewrite H0. easy. lia.
  rewrite H1.
  rewrite IHi with (q := q); try easy. lia.
Qed.

Lemma turn_angle_add_r_same : forall n r q, q < n -> 
          Cexp (2 * PI * turn_angle r n + rrz_ang q) = Cexp (2 * PI *  turn_angle (r_rotate r q) n).
Proof.
  intros.
  bdestruct (q =? 0). subst. unfold r_rotate,rrz_ang. simpl. rewrite addto_n_0.
  rewrite Cexp_add.
  assert ((2 * PI - 2 * PI / 1) = 0)%R by lra.
  rewrite H0. rewrite Cexp_0. lca.
  unfold turn_angle. 
  rewrite <- turn_angle_r_cut_n with (m := n) by lia.
  rewrite <- turn_angle_r_cut_n with (r := (fbrev n (r_rotate r q))) (m := n) by lia.
  rewrite turn_angle_r_split with (i := n - q) ; try lia.
  rewrite turn_angle_r_split with (r := (cut_n (fbrev n (r_rotate r q)) n)) (i := n - q) ; try lia.
  assert (turn_angle_r (cut_n (fbrev n (r_rotate r q)) n) (n - q) n
             = turn_angle_r (cut_n (fbrev n r) n) (n - q) n).
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_fbrev_flip.
  assert ((cut_n (r_rotate r q) n) = r_rotate (cut_n r n) q).
  rewrite addto_r_cut_n by lia. easy.
  rewrite H1.
  rewrite <- turn_angle_r_low_bit_same_r; try lia. easy.
  intros. unfold cut_n. bdestruct (i <? n). lia. easy.
  rewrite H1.
  unfold rrz_ang.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_l.
  rewrite turn_angle_fb_push_n.
  rewrite turn_angle_fb_push_n.
  assert ((n - (n - q)) = q) by lia. rewrite H2.
  assert (forall i, i < q -> (shift (cut_n (fbrev n (r_rotate r q)) n) (n - q)) i
           = (cut_n (sumfb false (shift (cut_n (fbrev n r) n) (n-q)) (nat2fb (2^q - 1))) n) i).
  intros. unfold r_rotate.
  rewrite cut_n_fbrev_flip.
  rewrite <- addto_r_cut_n by lia.
  rewrite add_to_n_sem with (n := n); try lia.
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite <- cut_n_fbrev_flip.
  assert ((2 ^ n - 2 ^ (n - q)) = 2^(n-q) * (2^q - 1)).
  assert (2^n = 2^(n-q + q)).
  assert (n=n-q+q) by lia. rewrite <- H4. easy.
  rewrite H4.
  rewrite Nat.pow_add_r.
  rewrite mult_minus_distr_l. lia.
  rewrite H4.
  rewrite nat2fb_pow_n.
  remember (cut_n (fbrev n r) n) as g.
  unfold shift,cut_n.
  bdestruct (i + (n - q) <? n). bdestruct (i <? n).
  unfold sumfb.
  replace (i + (n - q)) with ((n-q) + i) by lia.
  rewrite fb_push_nsame.
  rewrite carry_add_index with (s := 
    (fun i0 : nat => g (i0 + (n - q)))) (t := (nat2fb (2 ^ q - 1))); try easy.
  rewrite carry_false_lt; try easy.
  intros.
  rewrite fb_push_n_false. easy. lia.
  intros.
  assert ((i0 + (n - q))  = n-q+i0) by lia. rewrite H8. easy.
  intros. rewrite fb_push_nsame. easy.
  lia. lia.
  intros.
  unfold cut_n. bdestruct (i0 <? n). lia. easy.
  rewrite turn_angle_r_fun_same with (f := (shift (cut_n (fbrev n (r_rotate r q)) n) (n - q)))
    (g := cut_n (sumfb false (shift (cut_n (fbrev n r) n) (n - q)) (nat2fb (2 ^ q - 1))) n); try easy.
  remember ((shift (cut_n (fbrev n r) n) (n - q)) ) as g.
  rewrite turn_angle_r_cut_n with (r := (sumfb false g (nat2fb (2 ^ q - 1)))) by lia.
  assert (g = cut_n g q).
  subst.
  unfold shift,cut_n.
  apply functional_extensionality; intro.
  bdestruct (x + (n-q) <? n). bdestruct (x <? q). easy. lia.
  bdestruct (x <? q). lia. easy.
  rewrite H4.
  specialize (f_num_0 g q) as eq1.
  destruct eq1. rewrite H5.
  rewrite sumfb_correct_carry0.
  bdestruct (x =? 0). rewrite H6 in *.
  rewrite nat2fb_0.
  rewrite turn_angle_r_false_0 with (r := allfalse); try lia.
  rewrite plus_0_l. rewrite Rmult_0_r. rewrite Rmult_0_r.
  rewrite Rplus_0_r.
  rewrite turn_angle_r_bin by lia.
  rewrite bindecomp_spec.
  assert (2^q <> 0).
  apply Nat.pow_nonzero. lia.
  rewrite Nat.mod_small by lia.
  rewrite minus_INR. simpl.
  rewrite Rmult_minus_distr_l.
  rewrite Rmult_minus_distr_l.
  rewrite Rmult_minus_distr_l.
  rewrite Rmult_1_r.
  rewrite pow_INR.
  assert ((IZR (Zpos (xO xH))) = (INR (S (S O)))).
  rewrite INR_IZR_INZ.
  rewrite <- positive_nat_Z.
  assert ((Pos.to_nat 2) = 2) by lia.
  rewrite H8. easy.
  rewrite <- H8.
  rewrite <- (Rmult_assoc (2 ^ (n - q))).
  assert (2 ^ (n - q) * (1 / 2 ^ n) = / 2^ q)%R.
  assert (n = (n-q) + q) by lia.
  assert (2 ^ n = 2^((n-q)+q))%R. rewrite <- H9. easy.
  rewrite H10.
  rewrite pow_add.
  autorewrite with R_db.
  rewrite Rinv_mult_distr.
  rewrite <- Rmult_assoc.
  rewrite Rinv_r. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  rewrite H9.
  rewrite Rinv_l.
  autorewrite with R_db. easy.
  apply pow_nonzero. lra. lia.
  intros. easy.
  assert (2^q <> 0).
  apply Nat.pow_nonzero. lia.
  assert ((x + (2 ^ q - 1)) = x-1+2^q) by lia.
  rewrite H8.
  rewrite turn_angle_r_fun_same with
      (f := (nat2fb (x - 1 + 2 ^ q))) (g := (nat2fb (x - 1))); try lia.
  assert (nat2fb x = nat2fb (x - 1 + 1)).
  assert (x = x-1+1) by lia. rewrite <- H9. easy.
  rewrite H9.
  rewrite <- turn_angle_r_add_1_lt ; try lia.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_l.
  autorewrite with R_db.
  assert ((2 ^ (n - q) * / 2 ^ n)= / 2 ^ q)%R.
  assert (n = (n-q) + q) by lia.
  assert (2 ^ n = 2^((n-q)+q))%R. rewrite <- H10. easy.
  rewrite H11.
  rewrite pow_add.
  rewrite Rinv_mult_distr.
  rewrite <- Rmult_assoc.
  rewrite Rinv_r. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  rewrite H10.
  rewrite Rplus_assoc.
  rewrite Rplus_assoc.
  rewrite (Rplus_comm (2 * PI * / 2 ^ q)).
  rewrite (Rplus_assoc (2 * PI)).
  assert ((- (2 * PI * / 2 ^ q) + 2 * PI * / 2 ^ q) = 0)%R by lra.
  rewrite H11. rewrite Rplus_0_r.
  rewrite <- Rplus_assoc.
  rewrite Cexp_add. rewrite Cexp_2PI. lca.
  apply f_num_small in H5. lia.
  apply low_bit_same. 1-4:lia.
Qed.

Lemma Z_0_bit : σz × ∣0⟩ = ∣0⟩.
Proof.
  solve_matrix.
Qed.

Lemma Z_1_bit : σz × ∣1⟩ = (-1)%R .* ∣1⟩.
Proof.
  solve_matrix.
Qed.

Lemma rz_ang_trans_sem : forall vs dim avs tenv q rmax f p size, 
    exp_com_WF vs dim -> snd p < vsize vs (fst p) -> q < rmax ->
    right_mode_env (size_env vs) tenv f -> Env.MapsTo (fst p) (Phi size) tenv ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
           (phase_shift (rz_ang q) × trans_state avs rmax f (find_pos vs p))
                = compile_val (times_rotate (f p) q) rmax.
Proof.
      intros.
      unfold trans_state.
      rewrite H4 by assumption.
      apply (H2 (Phi size)) in H0; try easy. inv H0. 
      unfold times_rotate.
      unfold compile_val.
      distribute_scale.
      rewrite Mmult_plus_distr_l.
      distribute_scale.
      assert (∣0⟩ = ket (Nat.b2n false)).
      autorewrite with ket_db. easy. rewrite H0.
      rewrite phase_shift_on_basis_state.
      simpl. rewrite Rmult_0_l. simpl. rewrite Cexp_0. Msimpl.
      assert (∣1⟩ = ket (Nat.b2n true)).
      autorewrite with ket_db. easy. rewrite H5.
      rewrite phase_shift_on_basis_state. simpl.
      distribute_scale.
      rewrite <- Cexp_add. rewrite Rmult_1_l.
      rewrite turn_angle_add_same. easy. lia.
Qed.

Lemma rrz_ang_trans_sem : forall vs dim avs tenv q rmax f p size, 
    exp_com_WF vs dim -> snd p < vsize vs (fst p) -> q < rmax ->
    right_mode_env (size_env vs) tenv f -> Env.MapsTo (fst p) (Phi size) tenv ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
           (phase_shift (rrz_ang q) × trans_state avs rmax f (find_pos vs p))
                = compile_val (times_r_rotate (f p) q) rmax.
Proof.
      intros.
      unfold trans_state.
      rewrite H4 by assumption.
      apply (H2 (Phi size)) in H0; try easy. inv H0. 
      unfold times_rotate.
      unfold compile_val.
      distribute_scale.
      rewrite Mmult_plus_distr_l.
      distribute_scale.
      assert (∣0⟩ = ket (Nat.b2n false)).
      autorewrite with ket_db. easy. rewrite H0.
      rewrite phase_shift_on_basis_state.
      simpl. rewrite Rmult_0_l. simpl. rewrite Cexp_0. Msimpl.
      assert (∣1⟩ = ket (Nat.b2n true)).
      autorewrite with ket_db. easy. rewrite H5.
      rewrite phase_shift_on_basis_state. simpl.
      distribute_scale.
      rewrite <- Cexp_add. rewrite Rmult_1_l.
      rewrite turn_angle_add_r_same. easy. easy.
Qed.


Lemma gen_sr_gate_eval : forall n size asize tenv f vs avs dim rmax x, n <= size <= asize -> asize <= vsize vs x ->
    exp_com_WF vs dim -> 0 < vsize vs x -> size < rmax -> Env.MapsTo x (Phi asize) tenv ->
    right_mode_env (size_env vs) tenv f ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
    (forall i, i < dim -> find_pos vs (avs i) = i) ->
    uc_eval (gen_sr_gate' vs dim x n size) × vkron dim (trans_state avs rmax f)
    = vkron dim (trans_state avs rmax (sr_rotate' f x n size)).
Proof.
  induction n; intros; simpl.
  rewrite denote_ID.
  assert (find_pos vs (x,0) < dim).
  apply H1. easy. unfold find_pos in H6.
  unfold pad.
  bdestruct (start vs x + vmap vs x 0 + 1 <=? dim).
  repeat rewrite id_kron.
  assert (2 ^ (start vs x + vmap vs x 0) * 2 = 2 ^ (start vs x + vmap vs x 0) * (2^1)).
  rewrite Nat.pow_1_r. easy. rewrite H10.
  repeat rewrite <- Nat.pow_add_r. Msimpl. easy.
  unfold find_pos in H8. lia.
  rewrite Mmult_assoc.
  rewrite IHn with (asize := asize) (tenv := tenv); (try lia; try easy).
  rewrite vkron_Rz. 
  assert (vkron dim (trans_state avs rmax ((sr_rotate' f x n size) [(x, n)
                      |-> times_rotate (f (x, n)) (size - n)])) = 
          vkron dim (update (trans_state avs rmax (sr_rotate' f x n size))
                        (find_pos vs (x, n)) (compile_val (times_rotate (f (x, n)) (size - n)) rmax))).
  erewrite vkron_eq. reflexivity. intros.
  apply (trans_state_update dim). simpl. lia. easy. assumption. assumption.
  rewrite H8.
  rewrite vkron_split_up.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  rewrite (rz_ang_trans_sem vs dim avs tenv (size - n) rmax 
      (sr_rotate' f x n size) (x,n) asize); (try lia; try easy).
  rewrite sr_rotate'_ge; try easy.
  simpl. lia.
  unfold right_mode_env in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (n0 <? n). 
  rewrite sr_rotate'_lt_1; try lia.
  simpl in H10.
  apply mapsto_always_same with (v1:=(Phi asize)) in H10; try easy.
  specialize (H5 (Phi asize) (v,n0) H9). simpl in H5. apply H5 in H4.
  inv H4. unfold times_rotate. constructor.
  rewrite sr_rotate'_ge ; try lia. apply H5; try easy. simpl. lia.
  rewrite sr_rotate'_irrelevant; try easy.
  apply H5; try easy. simpl. lia.
  auto with wf_db. auto with wf_db.
  apply H1. simpl. lia.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  apply H1. simpl. lia.
  auto with wf_db. 
Qed.

Lemma gen_srr_gate_eval : forall n size asize tenv f vs avs dim rmax x, n <= size <= asize -> asize <= vsize vs x ->
    exp_com_WF vs dim -> 0 < vsize vs x -> size < rmax -> Env.MapsTo x (Phi asize) tenv ->
    right_mode_env (size_env vs) tenv f ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
    (forall i, i < dim -> find_pos vs (avs i) = i) ->
    uc_eval (gen_srr_gate' vs dim x n size) × vkron dim (trans_state avs rmax f)
    = vkron dim (trans_state avs rmax (srr_rotate' f x n size)).
Proof.
  induction n; intros; simpl.
  rewrite denote_ID.
  assert (find_pos vs (x,0) < dim).
  apply H1. easy. unfold find_pos in H6.
  unfold pad.
  bdestruct (start vs x + vmap vs x 0 + 1 <=? dim).
  repeat rewrite id_kron.
  assert (2 ^ (start vs x + vmap vs x 0) * 2 = 2 ^ (start vs x + vmap vs x 0) * (2^1)).
  rewrite Nat.pow_1_r. easy. rewrite H10.
  repeat rewrite <- Nat.pow_add_r. Msimpl. easy.
  unfold find_pos in H8. lia.
  rewrite Mmult_assoc.
  rewrite IHn with (asize := asize) (tenv := tenv); (try lia; try easy).
  rewrite vkron_Rz. 
  assert (vkron dim (trans_state avs rmax ((srr_rotate' f x n size) [(x, n)
                      |-> times_r_rotate (f (x, n)) (size - n)])) = 
          vkron dim (update (trans_state avs rmax (srr_rotate' f x n size))
                        (find_pos vs (x, n)) (compile_val (times_r_rotate (f (x, n)) (size - n)) rmax))).
  erewrite vkron_eq. reflexivity. intros.
  apply (trans_state_update dim). simpl. lia. easy. assumption. assumption.
  rewrite H8.
  rewrite vkron_split_up.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  rewrite (rrz_ang_trans_sem vs dim avs tenv (size - n) rmax 
      (srr_rotate' f x n size) (x,n) asize); (try lia; try easy).
  rewrite srr_rotate'_ge; try easy.
  simpl. lia.
  unfold right_mode_env in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (n0 <? n). 
  rewrite srr_rotate'_lt_1; try lia.
  simpl in H10.
  apply mapsto_always_same with (v1:=(Phi asize)) in H10; try easy.
  specialize (H5 (Phi asize) (v,n0) H9). simpl in H5. apply H5 in H4.
  inv H4. unfold times_r_rotate. constructor.
  rewrite srr_rotate'_ge ; try lia. apply H5; try easy. simpl. lia.
  rewrite srr_rotate'_irrelevant; try easy.
  apply H5; try easy. simpl. lia.
  auto with wf_db. auto with wf_db.
  apply H1. simpl. lia.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  apply H1. simpl. lia.
  auto with wf_db. 
Qed.


Fixpoint lshift_fun_gen (g : nat -> bool) (i n:nat) := 
   match n with 0 => allfalse
           | S m => update (lshift_fun_gen g i m) m (g (i+m))
   end.

Lemma turn_angle_0 : forall rmax, turn_angle allfalse rmax = 0%R.
Proof.
  intros. unfold turn_angle.
  assert (forall n, rmax <= n -> turn_angle_r (fbrev n allfalse) rmax n = 0%R).
  induction rmax;intros;simpl. easy.
  rewrite IHrmax by lia.
  unfold fbrev. bdestruct (rmax <? n). simpl. lra. simpl. lra.
  rewrite H. easy. lia.
Qed.

Lemma turn_angle_1 : forall rmax, 0 < rmax -> turn_angle (update allfalse 0 true) rmax = (1/ 2)%R.
Proof.
  intros. unfold turn_angle.
  rewrite turn_angle_r_fun_same with (g := update allfalse (rmax - 1) true) ; try lia.
  assert (forall n, rmax <= n -> turn_angle_r (update allfalse (n - 1) true) rmax n = (if rmax <? n then 0%R else (1/2)%R)).
  induction rmax;intros;simpl. lia. 
  bdestruct (rmax =? 0). subst. simpl.
  bdestruct (1 <? n). rewrite update_index_neq by lia. simpl. lra.
  assert (n = 1) by lia. rewrite H2.
  simpl. rewrite Rmult_1_r. lra.
  rewrite IHrmax.
  bdestruct (rmax =? n-1). subst. rewrite update_index_eq.
  bdestruct (n-1<?n).
  assert ((n - (n - 1)) = 1) by lia. rewrite H3. simpl.
  rewrite Rmult_1_r.
  bdestruct (S (n-1) <? n). lia. lra. lia.
  bdestruct (rmax <? n).
  rewrite update_index_neq by lia. simpl.
  bdestruct (S rmax <? n). lra. 1-4:lia.
  rewrite H0. bdestruct (rmax <? rmax). lia. easy. lia.
  intros. unfold fbrev. bdestruct (i <? rmax). 
  bdestruct (i =? rmax-1). subst.
  replace ((rmax - 1 - (rmax - 1))) with 0 by lia.
  repeat rewrite update_index_eq. easy.
  repeat rewrite update_index_neq by lia. easy. lia.
Qed.

Lemma turn_angle_update_0 : forall rmax (g:nat->bool) i b,
      0 < rmax -> g i = b -> turn_angle (update allfalse 0 (g i)) rmax = (if b then (1/2)%R else 0%R).
Proof.
  intros.
  unfold turn_angle. subst.
  destruct (g i).
  rewrite <- turn_angle_1 with (rmax := rmax). unfold turn_angle. easy. lia.
  rewrite turn_angle_r_fun_same with (g := (fbrev rmax allfalse)) ; try lia.
  rewrite <- turn_angle_0 with (rmax := rmax); try easy.
  intros. unfold fbrev. bdestruct (i0 <? rmax).
  bdestruct (rmax - 1 -i0 =? 0). rewrite H2.
  rewrite update_index_eq. easy.
  rewrite update_index_neq by lia. easy. lia.
Qed.

Lemma turn_angle_ge: forall n m f, n <= m -> turn_angle (update f m true) n = turn_angle f n.
Proof.
  intros. unfold turn_angle.
  rewrite turn_angle_r_fun_same with (g := fbrev n f) ; try lia. easy.
  intros. unfold fbrev.
  bdestruct (i <? n). rewrite update_index_neq by lia. easy. lia.
Qed.


Lemma turn_angle_out: forall n f i j, i <= j -> S j < n -> 
     (forall t, i <= t -> f t = false) ->
    (turn_angle f n + / 2^(S j))%R = turn_angle (update f j true) n.
Proof.
  intros. unfold turn_angle.
  rewrite (turn_angle_r_split n (n-i)) by lia.
  rewrite (turn_angle_r_split n (n-i) (fbrev n (update f j true))) by lia.
  rewrite turn_angle_r_false_0.
  rewrite turn_angle_r_fun_same with (f := (fb_push_n (n - i) (shift (fbrev n f) (n - i))))
             (g := (fb_push_n (n - i) (shift (fbrev n (update f j true)) (n - i)))) ; try lia.
  rewrite turn_angle_r_fun_same with (f := (fbrev n (update f j true))) (g := twoton_fun (n-1-j)) ; try lia.
  rewrite f_twoton_eq. rewrite turn_angle_r_bin by lia.
  rewrite bindecomp_spec.
  rewrite Nat.mod_small.
  assert ((1 / 2 ^ n * INR (2 ^ (n - 1 - j)) = /2^ S j)%R).
  autorewrite with R_db.
  assert (n = (n - 1 - j) + S j)%nat by lia.
  assert (/ 2 ^ n = / 2 ^ (n - 1 - j + S j))%R.
  rewrite <- H2. easy. rewrite H3.
  rewrite pow_add.
  rewrite pow_INR.
  assert ((IZR (Zpos (xO xH))) = (INR (S (S O)))).
  rewrite INR_IZR_INZ.
  rewrite <- positive_nat_Z.
  assert ((Pos.to_nat 2) = 2) by lia.
  rewrite H4. easy. rewrite <- H4.
  rewrite Rinv_mult_distr.
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc.
  rewrite Rinv_r. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  apply pow_nonzero. lra.
  rewrite H2. lra.
  apply Nat.pow_lt_mono_r; try lia.
  intros.
  unfold fbrev,twoton_fun.
  bdestruct (i0 <? n).
  bdestruct (i0 <? n- 1 - j).
  rewrite update_index_neq by lia. rewrite H1. easy. lia.
  bdestruct (i0 =? n - 1 - j).
  subst. assert ((n - 1 - (n - 1 - j)) = j) by lia.
  rewrite H5. rewrite update_index_eq. easy.
  rewrite update_index_neq by lia.
  rewrite H1. easy. lia.
  lia.
  intros.
  bdestruct (i0 <? n-i).
  repeat rewrite fb_push_n_false by lia. easy.
  assert (i0 = (n-i) + (i0 - (n-i))) by lia.
  rewrite H4.
  repeat rewrite fb_push_nsame.
  unfold shift.
  assert ((i0 - (n - i) + (n - i)) = i0) by lia.
  rewrite H5.
  unfold fbrev.
  bdestruct (i0 <? n).
  rewrite update_index_neq by lia. easy. lia. lia.
  intros. unfold fbrev.
  bdestruct (i0 <? n).
  rewrite H1. easy. lia. lia.
Qed.

Lemma lshift_fun_gen_lt : forall n m i g, i < n -> lshift_fun_gen g m n i = g (m + i).
Proof.
  induction n; intros; simpl. lia.
  bdestruct (i =? n).
  subst. rewrite update_index_eq. easy.
  rewrite update_index_neq by lia.
  rewrite IHn. easy. lia.
Qed.

Lemma lshift_fun_gen_ge : forall n m i g,  n <= i -> lshift_fun_gen g m n i = false.
Proof.
  induction n; intros; simpl. easy.
  bdestruct (i =? n). subst. lia.
  rewrite update_index_neq by lia.
  rewrite IHn. easy. lia.
Qed.


Lemma gen_cr_gate_eval : forall n i b f g vs avs dim rmax x, 
    n + i <= b <= (size_env vs x) -> 0 < n -> b < rmax
     -> (forall m, i <= m < (size_env vs x) -> nor_mode f (x,m)) ->
    exp_com_WF vs dim ->
    (forall m, i <= m < b -> get_cua (f (x,m)) = g m) ->
    avs_prop vs avs dim -> 
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    uc_eval
  (controlled_rotations_gen vs dim x n i)
   × vkron dim (trans_state avs rmax (f[(x, i) |-> up_h (f (x, i))])) =
   vkron dim
  (update (trans_state avs rmax f)
     (find_pos vs (x, i))
     (compile_val (qval (get_r (f (x,i))) (lshift_fun_gen g i n)) rmax)).
Proof.
  induction n; intros; simpl. lia.
  destruct n.
  rewrite denote_ID_1. Msimpl.
  specialize (H2 i) as eq1.
  assert (i <= i < size_env vs x) by lia.
  apply eq1 in H10.
  unfold nor_mode in H10.
  destruct (f (x,i)) eqn:eq2.
  rewrite vkron_split_eup with (vs := vs); try easy.
  unfold up_h.
  destruct b0 eqn:eq3.
  unfold compile_val.
  rewrite <- turn_angle_add_same by lia.
  rewrite vkron_split_up.
  unfold get_r,z_phase,rz_ang.
  rewrite Cexp_add. rewrite turn_angle_0.
  assert ((2 * PI / 2 ^ 1) = PI)%R.
  rewrite pow_1. lra.
  rewrite H11. rewrite Cexp_PI.
  unfold lshift_fun_gen.
  replace (i + 0) with i by lia.
  specialize (H4 i) as eq4.
  assert (i <= i < b) by lia.
  apply eq4 in H12.
  rewrite eq2 in H12. unfold get_cua in H12.
  rewrite turn_angle_update_0 with (b := true);try lia.
  assert ((2 * PI * (1 / 2)) = PI)%R.
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc. unfold Rdiv.
  rewrite Rmult_1_l.
  rewrite <- Rinv_l_sym. lra. lra.
  rewrite H13. rewrite Cexp_PI.
  assert ((2 * PI * 0) = 0)%R by lra.
  rewrite H14. rewrite Cexp_0.
  simpl. autorewrite with C_db. easy. symmetry. easy.
  auto with wf_db.
  auto with wf_db.
  replace (start vs x + vmap vs x i) with (find_pos vs (x,i)) by easy.
  apply H3. simpl. unfold size_env in *. lia.
  unfold compile_val.
  rewrite vkron_split_up.
  unfold get_r,z_phase,rz_ang.
  rewrite turn_angle_0.
  unfold lshift_fun_gen.
  replace (i + 0) with i by lia.
  specialize (H4 i) as eq4.
  assert (i <= i < b) by lia.
  apply eq4 in H11.
  rewrite eq2 in H11. unfold get_cua in H11.
  rewrite turn_angle_update_0 with (b := false);try lia.
  assert ((2 * PI * 0) = 0)%R by lra.
  rewrite H12. rewrite Cexp_0. simpl. easy.
  symmetry. easy.
  auto with wf_db.
  auto with wf_db.
  replace (start vs x + vmap vs x i) with (find_pos vs (x,i)) by easy.
  apply H3. simpl. unfold size_env in *. lia.
  apply H3. simpl. unfold size_env in *. lia.
  simpl. unfold size_env in *. lia.
  apply vs_avs_bij_l with (dim := dim); try easy.
  apply vs_avs_bij_r; try easy. lia.
  replace (start vs x + vmap vs x i) with (find_pos vs (x,i)) by easy.
  apply H3. simpl. unfold size_env in *. lia.
  remember (S n) as m.
  simpl.
  rewrite Mmult_assoc.
  rewrite IHn with (g := g) (b := b); try easy.
  rewrite control_correct.
  distribute_plus.
  Locate proj.
  specialize (H2 (m+i)).
  assert (i <= m + i < size_env vs x). lia.
  specialize (H4 (m+i)).
  apply H2 in H10 as eq1.
  assert (i <= m + i < b). lia.
  apply H4 in H11.
  unfold nor_mode in *.
  destruct (f (x,m+i)) eqn:eq2. clear eq1. unfold get_cua.
  assert ((update (trans_state avs rmax f) (find_pos vs (x, i))
       (compile_val (qval (get_r (f (x, i))) (lshift_fun_gen g i m))
          rmax)) (find_pos vs (x,m+i)) = compile_val (nval b0 r) rmax).
  rewrite update_index_neq.
  unfold trans_state.
  rewrite vs_avs_bij_l with (dim := dim); try easy.
  rewrite eq2. easy.
  apply find_pos_prop; try easy. simpl. unfold size_env in *. lia. iner_p.
  unfold compile_val in H12.
  destruct b0 eqn:eq1.
  rewrite vkron_proj_neq with (b := true) (r := Cexp (2 * PI * turn_angle r rmax)); try easy.
  rewrite Mmult_assoc.
  replace ((start vs x + vmap vs x i)) with (find_pos vs (x,i)) by easy.
  assert (vkron dim (update (update (trans_state avs rmax f) (find_pos vs (x, i))
             (compile_val
                (qval (get_r (f (x, i))) (lshift_fun_gen g i m)) rmax))
               (find_pos vs (x, i))
              (compile_val
                (qval (get_r (f (x, i))) (update (lshift_fun_gen g i m) m (g (i + m)))) rmax))
        = (uc_eval (Rz (rz_ang (S m)) (find_pos vs (x, i)))
           × vkron dim
             (update (trans_state avs rmax f) (find_pos vs (x, i))
             (compile_val
                (qval (get_r (f (x, i))) (lshift_fun_gen g i m)) rmax)))).
  rewrite vkron_Rz.
  rewrite vkron_split_up.
  assert ((phase_shift (rz_ang (S m))
   × update (trans_state avs rmax f) (find_pos vs (x, i))
       (compile_val (qval (get_r (f (x, i))) (lshift_fun_gen g i m))
          rmax) (find_pos vs (x, i)))
    = compile_val
    (qval (get_r (f (x, i)))
       (update (lshift_fun_gen g i m) m (g (i + m)))) rmax).
  rewrite update_index_eq.
  unfold compile_val.
  distribute_scale.
  unfold rz_ang.
  Locate phase_shift.
  autorewrite with R_db C_db ket_db eval_db.
  rewrite <- Cmult_assoc.
  rewrite <- Cexp_add.
  rewrite <- Rmult_plus_distr_l.
  assert ((turn_angle (lshift_fun_gen g i m) rmax + / 2 ^ S m)%R
    = turn_angle (update (lshift_fun_gen g i m) m (g (i + m))) rmax).
  unfold get_cua in H11.
  rewrite plus_comm in H11.
  rewrite <- H11.
  rewrite turn_angle_out with (i := m); try lia. easy.
  intros. rewrite lshift_fun_gen_ge; try lia; try easy.
  rewrite H13. easy.
  rewrite H13. easy.
  intros.
  auto with wf_db.
  auto with wf_db.
  apply H3. simpl. unfold size_env in *. lia.
  apply H3. simpl. unfold size_env in *. lia.
  auto with wf_db.
  rewrite <- H13. clear H13.
  rewrite update_twice_eq.
  replace ((start vs x + vmap vs x (m + i))) with (find_pos vs (x,m+i)) by easy.
  Check vkron_proj_eq.
  rewrite vkron_proj_eq with (b := true) (r := Cexp (2 * PI * turn_angle r rmax)); try easy.
  unfold compile_val.
  Msimpl. easy.
  auto with wf_db.
  apply H3. simpl. unfold size_env in *. lia.
  rewrite update_index_neq.
  rewrite update_index_neq in H12. easy.
  apply find_pos_prop; try easy. simpl. unfold size_env in *. lia. iner_p.
  apply find_pos_prop; try easy. simpl. unfold size_env in *. lia. iner_p.
  auto with wf_db.
  replace ((start vs x + vmap vs x (m + i))) with (find_pos vs (x,m+i)) by easy.
  apply H3. simpl. unfold size_env in *. lia.
  replace ((start vs x + vmap vs x (m + i))) with (find_pos vs (x,m+i)) by easy.
  rewrite vkron_proj_eq with (b := false) (r := Cexp (2 * PI * turn_angle r rmax)); try easy.
  rewrite Mmult_assoc.
  replace ((start vs x + vmap vs x i)) with (find_pos vs (x,i)) by easy.
  assert (vkron dim (update (update (trans_state avs rmax f) (find_pos vs (x, i))
             (compile_val
                (qval (get_r (f (x, i))) (lshift_fun_gen g i m)) rmax))
               (find_pos vs (x, i))
              (compile_val
                (qval (get_r (f (x, i))) (update (lshift_fun_gen g i m) m true)) rmax))
        = (uc_eval (Rz (rz_ang (S m)) (find_pos vs (x, i)))
           × vkron dim
             (update (trans_state avs rmax f) (find_pos vs (x, i))
             (compile_val
                (qval (get_r (f (x, i))) (lshift_fun_gen g i m)) rmax)))).
  rewrite vkron_Rz.
  rewrite vkron_split_up.
  assert ((phase_shift (rz_ang (S m))
   × update (trans_state avs rmax f) (find_pos vs (x, i))
       (compile_val (qval (get_r (f (x, i))) (lshift_fun_gen g i m))
          rmax) (find_pos vs (x, i)))
    = compile_val
    (qval (get_r (f (x, i)))
       (update (lshift_fun_gen g i m) m true)) rmax).
  rewrite update_index_eq.
  unfold compile_val.
  distribute_scale.
  unfold rz_ang.
  Locate phase_shift.
  autorewrite with R_db C_db ket_db eval_db.
  rewrite <- Cmult_assoc.
  rewrite <- Cexp_add.
  rewrite <- Rmult_plus_distr_l.
  assert ((turn_angle (lshift_fun_gen g i m) rmax + / 2 ^ S m)%R
    = turn_angle (update (lshift_fun_gen g i m) m true) rmax).
  rewrite turn_angle_out with (i := m); try lia. easy.
  intros. rewrite lshift_fun_gen_ge; try lia; try easy.
  rewrite H13. easy.
  rewrite H13. easy.
  intros.
  auto with wf_db.
  auto with wf_db.
  apply H3. simpl. unfold size_env in *. lia.
  apply H3. simpl. unfold size_env in *. lia.
  auto with wf_db.
  rewrite <- H13.
  rewrite vkron_proj_neq with (b := false) (r := Cexp (2 * PI * turn_angle r rmax)); try easy.
  unfold get_cua in H11.
  rewrite plus_comm in H11. rewrite <- H11.
  rewrite update_same with (b1 := false).
  unfold compile_val. Msimpl. easy.
  rewrite lshift_fun_gen_ge by lia. easy.
  intros. rewrite update_twice_eq.
  auto with wf_db.
  apply H3. simpl. unfold size_env in *. lia.
  rewrite update_twice_eq.
  rewrite update_index_neq.
  rewrite update_index_neq in H12. easy.
  apply find_pos_prop; try easy. simpl. unfold size_env in *. lia. iner_p.
  apply find_pos_prop; try easy. simpl. unfold size_env in *. lia. iner_p.
  auto with wf_db.
  apply H3. simpl. unfold size_env in *. lia. lia.
  replace ((start vs x + vmap vs x (m + i))) with (find_pos vs (x,m+i)) by easy.
  replace ((start vs x + vmap vs x i)) with (find_pos vs (x,i)) by easy.
  Check fresh_is_fresh.
  replace ((Rz (rz_ang (S m)) (find_pos vs (x, i)))) with ((fst (fst (trans_exp vs dim (RZ (S m) (x, i)) avs)))) by easy.
  apply fresh_is_fresh; try easy.
  constructor. iner_p.
  constructor.
  simpl. lia. unfold size_env in *. simpl. lia.
  apply uc_well_typed_Rz.
  replace (start vs x + vmap vs x i) with (find_pos vs (x,i)) by easy.
  apply H3. simpl. unfold size_env in *. lia. lia. lia.
Qed.

Definition rshift_fun (f:nat -> bool) (n:nat) := fun i => f (i-n).

Lemma lshift_fun_gen_s : forall n i g,
   forall m, 0 < m < n -> lshift_fun_gen g i n m = rshift_fun (lshift_fun_gen g (S i) n) 1 m.
Proof.
  induction n; intros;simpl.
  unfold rshift_fun. easy.
  unfold rshift_fun.
  bdestruct (m =? n). subst.
  rewrite update_index_eq.
  rewrite update_index_neq by lia.
  rewrite lshift_fun_gen_lt.
  assert ((S i + (n - 1)) = i + n) by lia. rewrite H0. easy. lia.
  rewrite update_index_neq by lia.
  rewrite IHn by lia.
  unfold rshift_fun.
  bdestruct (n =? m-1). lia.
  rewrite update_index_neq by lia. easy.
Qed.

Lemma lshift_fun_gen_eq : forall n size g, n <= size -> (forall i, size <= i -> g i = false) ->
   lshift_fun_gen g (size - n) n = lshift_fun g (size - n).
Proof.
  induction n; intros;simpl.
  unfold lshift_fun.
  apply functional_extensionality; intro.
  assert (size <= (x + (size - 0))) by lia.
  apply H0 in H1. rewrite H1. easy.
  unfold lshift_fun.
  apply functional_extensionality; intro.
  bdestruct (x =? n). subst. rewrite update_index_eq.
  assert ((size - S n + n) = (n + (size - S n))) by lia. rewrite H1. easy.
  rewrite update_index_neq by lia.
  bdestruct (n =? 0). subst.
  simpl. assert (0 < x) by lia.
  assert (size <= (x + (size - 1))) by lia. apply H0 in H3. rewrite H3. easy.
  bdestruct (n <=? x).
  rewrite lshift_fun_gen_ge by lia.
  assert (size <= (x + (size - S n))) by lia. apply H0 in H4. rewrite H4. easy.
  rewrite lshift_fun_gen_lt by lia.
  assert ((size - S n + x) = (x + (size - S n))) by lia. rewrite H4. easy.
Qed.

Lemma gen_qft_gate_eval : forall n b f g vs avs dim rmax x, 
    n <= b <= (size_env vs x) -> 0 < (size_env vs x) ->
    exp_com_WF vs dim -> nor_modes f x (size_env vs x) ->
    (get_cus b f x) = g ->
    avs_prop vs avs dim -> 
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    b < rmax ->
    uc_eval (QFT_gen vs dim x n b) × vkron dim (trans_state avs rmax f)
    = vkron dim (trans_state avs rmax (assign_r f x g n)).
Proof.
  induction n; intros; simpl.
  rewrite denote_ID_1. Msimpl. easy.
  assert (find_pos vs (x,0) < dim). apply H1. easy.
  unfold find_pos in *. easy.
  rewrite Mmult_assoc.
  rewrite IHn with (g:=g); try easy.
  assert (vkron dim (trans_state avs rmax
                ((assign_r f x g n) [(x, n) |-> up_qft (f (x, n)) (lshift_fun g n)])) = 
          vkron dim (update (trans_state avs rmax (assign_r f x g n))
                        (find_pos vs (x, n)) (compile_val (up_qft (f (x, n)) (lshift_fun g n)) rmax))).
  erewrite vkron_eq. reflexivity. intros.
  apply (trans_state_update dim). simpl. unfold size_env in *. lia.
  apply vs_avs_bij_l with (dim := dim); try easy.
  apply vs_avs_bij_r with (dim := dim); try easy. easy.
  rewrite H10.
  unfold up_qft.
  rewrite Mmult_assoc.
  rewrite vkron_H.
  unfold nor_modes in *.
  specialize (H2 n) as X1.
  assert (n < vsize vs x). unfold size_env in *. lia. apply X1 in H11.
  unfold nor_mode in H11. destruct (f (x,n)) eqn:eq1.
  replace (start vs x + vmap vs x n) with (find_pos vs (x,n)) by easy.
  assert ((vkron (find_pos vs (x, n)) (trans_state avs rmax (assign_r f x g n))
   ⊗ (hadamard
      × trans_state avs rmax (assign_r f x g n) (find_pos vs (x, n)))
   ⊗ vkron (dim - (find_pos vs (x, n) + 1))
       (shift (trans_state avs rmax (assign_r f x g n))
          (find_pos vs (x, n) + 1)))
    = vkron dim
           (trans_state avs rmax ((assign_r f x g n) [(x, n) |-> up_h ((assign_r f x g n) (x, n))]))).
  rewrite vkron_split_eup with (vs := vs); try easy.
  assert ((hadamard × trans_state avs rmax (assign_r f x g n) (find_pos vs (x, n)))
            = compile_val (up_h (assign_r f x g n (x, n))) rmax).
  unfold trans_state.
  rewrite vs_avs_bij_l with (dim := dim); try easy.
  rewrite assign_r_ge by lia.
  rewrite eq1.
  unfold compile_val,up_h.
  destruct b0 eqn:eq2.
  assert (rotate allfalse 1 = update allfalse 0 true).
  {   apply functional_extensionality; intro.
      destruct x0. rewrite rotate_1_0. rewrite update_index_eq. easy.
      easy.
      rewrite update_index_neq by lia.
      unfold rotate, addto.
      bdestruct (S x0 <? 1). lia. easy.
  }
  rewrite H12. clear H12. rewrite turn_angle_1.
  distribute_scale.
  rewrite H_spec.
  unfold z_phase. 
  simpl.
  assert ((2 * PI * (1 / 2)) = PI)%R by lra.
  rewrite H12. rewrite Cexp_PI.
  assert (((-1)%R * C1)%C = ((-1)%R)%C) by lca.
  rewrite H13. clear H13.
  rewrite Cmult_comm.
  autorewrite with R_db C_db ket_db RtoC_db. easy. lia.
  rewrite turn_angle_0.
  distribute_scale.
  rewrite H_spec.
  unfold z_phase. 
  simpl.
  assert ((2 * PI * 0) = 0)%R by lra.
  rewrite H12. rewrite Cexp_0.
  rewrite Cmult_comm.
  autorewrite with R_db C_db ket_db RtoC_db. easy.
  unfold size_env in *. simpl. lia.
  rewrite H12. easy.
  apply H1. simpl. unfold size_env in *. lia. unfold size_env in *. simpl. lia.
  apply vs_avs_bij_l with (dim := dim); try easy.
  apply vs_avs_bij_r with (dim := dim); try easy.
  rewrite H12.
  rewrite gen_cr_gate_eval with (g := g) (b := b); try (easy); try lia.
  rewrite assign_r_ge by lia.
  rewrite eq1. unfold get_r.
  remember (b - n) as q.
  assert ((lshift_fun_gen g n q)
          = lshift_fun_gen g (b - q) q).
  subst.
  assert ((b - (b - n)) = n) by lia.
  rewrite H3. easy.
  rewrite H13.
  rewrite lshift_fun_gen_eq; try easy. subst.
  assert ((b - (b - n)) = n) by lia.
  rewrite H3. easy.
  subst. lia.
  intros. rewrite <- H3.
  unfold get_cus. bdestruct (i <? b). unfold size_env in *. lia.
  easy.
  intros.
  unfold nor_mode.
  rewrite assign_r_ge by lia. apply H2. lia.
  intros.
  rewrite assign_r_ge by lia.
  rewrite <- get_cus_cua with (n := (vsize vs x)). rewrite <- H3.
  rewrite get_cus_cua. rewrite get_cus_cua. easy. lia.
  unfold size_env in *. lia.
  unfold size_env in *. lia. easy.
  replace (start vs x + vmap vs x n) with (find_pos vs (x,n)) by easy.
  apply H1. simpl. unfold size_env in *. lia.
  intros. 
  auto with wf_db. lia.
Qed.

Lemma gen_h_gate_eval : forall n b f vs avs dim rmax x, 
    b+n <= (size_env vs x) -> 0 < (size_env vs x) ->
    exp_com_WF vs dim ->
    avs_prop vs avs dim -> 
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    (forall i, b <= i < b + n -> nor_mode f (x,i)) ->
    0 < rmax ->
    uc_eval (nH vs dim x n b) × vkron dim (trans_state avs rmax f) =
    vkron dim (trans_state avs rmax (assign_h f x b n)).
Proof.
  induction n; intros; simpl.
  rewrite denote_ID_1. Msimpl. easy.
  replace (start vs x + vmap vs x 0) with (find_pos vs (x,0)) by easy.
  apply H1.  simpl. easy.
  rewrite Mmult_assoc.
  rewrite IHn; try easy.
  replace (start vs x + vmap vs x (b+n)) with (find_pos vs (x,b+n)) by easy.
  rewrite vkron_H.
  rewrite vkron_split_eup with (vs := vs); try easy.
  assert ((hadamard × trans_state avs rmax (assign_h f x b n) (find_pos vs (x, b+n)))
            = compile_val (up_h (f (x, b+n))) rmax).
  unfold trans_state.
  rewrite vs_avs_bij_l with (dim := dim); try easy.
  rewrite assign_h_ge by lia.
  specialize (H7 (b+n)).
  assert (b <= b+n < b+ S n) by lia. apply H7 in H9.
  unfold nor_mode in *.
  destruct (f (x,b+n)) eqn:eq1.
  unfold compile_val,up_h.
  destruct b0 eqn:eq2.
  assert (rotate allfalse 1 = update allfalse 0 true).
  {   apply functional_extensionality; intro.
      destruct x0. rewrite rotate_1_0. rewrite update_index_eq. easy.
      easy.
      rewrite update_index_neq by lia.
      unfold rotate, addto.
      bdestruct (S x0 <? 1). lia. easy.
  }
  rewrite H10. clear H10. rewrite turn_angle_1.
  distribute_scale.
  rewrite H_spec.
  unfold z_phase. 
  simpl.
  assert ((2 * PI * (1 / 2)) = PI)%R by lra.
  rewrite H10. rewrite Cexp_PI.
  autorewrite with C_db.
  rewrite Cmult_comm.
  autorewrite with R_db C_db ket_db RtoC_db. easy. 
  easy.
  rewrite turn_angle_0.
  distribute_scale.
  rewrite H_spec.
  unfold z_phase. 
  simpl.
  assert ((2 * PI * 0) = 0)%R by lra.
  rewrite H10. rewrite Cexp_0.
  rewrite Cmult_comm.
  autorewrite with R_db C_db ket_db RtoC_db. easy.
  easy.
  simpl. unfold size_env in *. lia.
  rewrite H9. easy.
  apply H1. simpl. unfold size_env in *. lia.
  simpl. unfold size_env in *. lia.
  apply vs_avs_bij_l with (dim := dim); try easy.
  apply vs_avs_bij_r with (dim := dim); try easy.
  apply H1. unfold size_env in *. simpl. lia.
  intros. auto with wf_db. lia.
  intros. apply H7. lia.
Qed.

Lemma assign_r_cover_full : forall n f x g aenv tenv,
            0 < aenv x -> n <= aenv x ->
            Env.MapsTo x (Phi n) tenv -> qft_uniform aenv tenv f 
           -> qft_gt aenv tenv f -> right_mode_env aenv tenv f ->
            assign_r (assign_seq f x g n) x (get_r_qft f x) n = f.
Proof.
  intros. 
  assert (phi_modes f x (aenv x)).
  apply type_phi_modes with (b := n) (env := tenv); try easy.
  apply functional_extensionality. intros.
  destruct x0.
  bdestruct (v =? x). subst.
  bdestruct (n0 <? n).
  rewrite assign_r_covers; try easy.
  apply phi_modes_trans with (size := aenv x); try easy.
  unfold qft_uniform in *.
  rewrite H2 with (b := n); try easy.
  rewrite assign_r_ge by lia.
  rewrite assign_seq_ge by lia. easy.
  rewrite assign_r_out by iner_p.
  rewrite assign_seq_out by iner_p. easy.
Qed.

Lemma get_cus_assign_hr_same :
    forall i n b f x, b <= n -> get_cus b (assign_h_r f x n i) x = get_cus b f x.
Proof.
  induction i;intros;simpl.
  apply functional_extensionality; intro.
  unfold get_cus.
  bdestruct (x0 <? b); try easy.
  apply functional_extensionality; intro.
  unfold get_cus.
  bdestruct (x0 <? b); try easy.
  rewrite eupdate_index_neq by iner_p.
  specialize (IHi n b f x H).
  assert (get_cus b (assign_h_r f x n i) x x0 = get_cus b f x x0).
  rewrite IHi. easy.
  unfold get_cus in *.
  bdestruct (x0 <? b).
  easy. lia.
Qed.

(* The Compilation Correctness Theorem. *)
Lemma trans_exp_sem :
  forall dim e f tenv tenv' rmax vs (avs : nat -> posi),
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    exp_WF (size_env vs) e ->
    at_match (size_env vs) tenv ->
    exp_com_WF vs dim ->
    exp_com_gt vs avs dim ->
    well_typed_oexp (size_env vs) tenv e tenv' ->
    right_mode_env (size_env vs) tenv f ->
    avs_prop vs avs dim -> 
    exp_rmax (size_env vs) rmax e ->
    qft_uniform (size_env vs) tenv f ->
    qft_gt (size_env vs) tenv f ->
    dim > 0 ->
    (uc_eval (fst (fst (trans_exp vs dim e avs)))) × (vkron dim (trans_state avs rmax f)) 
                =  vkron dim (trans_state (snd (trans_exp vs dim e avs)) rmax (exp_sem (size_env vs) e f)).
Proof.
  intros dim e. induction e; intros.
  - simpl. rewrite denote_ID_1. Msimpl. easy.
    apply H5. inv H3. unfold size_env in *. easy.
  - simpl.
    rewrite vkron_X. 
    assert (vkron dim (trans_state avs rmax (f [p |-> exchange (f p)])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (exchange (f p)) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H3. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy. easy.
    rewrite H14.  rewrite vkron_split_up.
    assert ((σx × trans_state avs rmax f (find_pos vs p))
                 = compile_val (exchange (f p)) rmax).
    { unfold trans_state.
      inv H3. rewrite vs_avs_bij_l with (dim := dim); try easy.
      inv H7. inv H3. unfold right_mode_env in H8.
      apply (H8 Nor) in H16. inv H16.
      unfold exchange. 
      unfold compile_val.
      distribute_scale.
      destruct b. simpl.
      autorewrite with ket_db. easy.
      simpl.
      autorewrite with ket_db. easy. easy.
      }
    rewrite H15. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H5. inv H3. assumption.
    apply H5. inv H3. assumption.
    auto with wf_db.
  - rewrite trans_exp_cu_eval by assumption.
    assert ((snd (trans_exp vs dim (CU p e) avs)) = avs).
    simpl. destruct (trans_exp vs dim e avs) eqn:eq1. destruct p0. simpl. easy.
    rewrite H14. clear H14.
    rewrite control_correct.
    simpl. 
    assert (exists r', (trans_state avs rmax f) (find_pos vs p) = r' .* (ket (Nat.b2n (get_cua (f p))))).
    inv H3.
    unfold trans_state. 
    rewrite vs_avs_bij_l with (dim := dim); try easy.
    inv H7. inv H3. apply (H8 Nor) in H16; try easy. inv H16.
    unfold compile_val,get_cua.
    exists (Cexp (2 * PI * turn_angle r rmax)). 
    easy.
    destruct H14. inv H7. inv H15.
    inv H10.
    rewrite Mmult_plus_distr_r.
    rewrite Mmult_assoc.
    inv H3. 
    specialize (IHe f tenv' tenv' rmax vs avs H H0 H1 H2 H19 H4 H5 H6 H22 H8 H9 H16 H11 H12 H13).
    rewrite IHe.
    destruct (get_cua (f p)) eqn:eq2.
    erewrite vkron_proj_neq.
    rewrite vkron_proj_eq with (r := x).
    rewrite neu_trans_state_avs; try easy.
    Msimpl. easy. auto with wf_db. apply H5. easy.
    rewrite neu_trans_state_avs; try easy.
    unfold trans_state in *. rewrite efresh_exp_sem_irrelevant. easy. easy.
    rewrite vs_avs_bij_l with (dim := dim); try easy.
    auto with wf_db.
    apply H5; easy. rewrite H14. reflexivity. easy.
    rewrite vkron_proj_eq with (r := x).
    rewrite vkron_proj_neq with (r := x) (b := false). Msimpl. easy.
    auto with wf_db.
    apply H5. easy.
    rewrite neu_trans_state_avs; try easy.
    unfold trans_state in *. rewrite efresh_exp_sem_irrelevant. easy. easy.
    rewrite vs_avs_bij_l with (dim := dim); try easy. easy.
    auto with wf_db.
    apply H5; easy. rewrite H14. reflexivity. 
    apply fresh_is_fresh; try easy.
    inv H7. inv H14. easy. inv H3. easy. inv H3. unfold size_env in H16. easy.
    inv H7. inv H14.
    apply trans_exp_uc_well_typed with (tenv:=tenv') (tenv':=tenv'); try easy. inv H3. easy.
  - simpl.
    rewrite vkron_Rz. 
    assert (vkron dim (trans_state avs rmax (f [p |-> times_rotate (f p) q])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (times_rotate (f p) q) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H3. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy. easy.
    rewrite H14.  rewrite vkron_split_up.
    assert ((phase_shift (rz_ang q) × trans_state avs rmax f (find_pos vs p))
                 = compile_val (times_rotate (f p) q) rmax).
    { unfold trans_state.
      inv H3.
      rewrite vs_avs_bij_l with (dim := dim); try easy.
      inv H7. inv H3. apply (H8 Nor) in H17; try easy. inv H17. 
      unfold times_rotate. destruct b.
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale.
      rewrite <- Cexp_add. simpl. rewrite Rmult_1_l.
      inv H10. rewrite turn_angle_add_same. easy. lia.
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale. simpl. 
      rewrite <- Cexp_add. simpl.
      autorewrite with R_db. easy.
      }
    rewrite H15. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H5. inv H3. assumption.
    apply H5. inv H3. assumption.
    auto with wf_db.
  - simpl.
    rewrite vkron_Rz. 
    assert (vkron dim (trans_state avs rmax (f [p |-> times_r_rotate (f p) q])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (times_r_rotate (f p) q) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H3. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy. easy.
    rewrite H14.  rewrite vkron_split_up.
    assert ((phase_shift (rrz_ang q) × trans_state avs rmax f (find_pos vs p))
                 = compile_val (times_r_rotate (f p) q) rmax).
    { unfold trans_state.
      inv H3.
      rewrite vs_avs_bij_l with (dim := dim); try easy.
      inv H7. inv H3. apply (H8 Nor) in H17.
      inv H17.
      unfold times_r_rotate. destruct b. 
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale.
      rewrite <- Cexp_add. simpl. rewrite Rmult_1_l.
      inv H10. rewrite turn_angle_add_r_same. easy. easy.
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale. simpl. 
      rewrite <- Cexp_add. simpl.
      autorewrite with R_db. easy. easy.
      }
    rewrite H15. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H5. inv H3. assumption.
    apply H5. inv H3. assumption.
    auto with wf_db.
  - Local Opaque gen_sr_gate. simpl.
    Local Transparent gen_sr_gate. unfold gen_sr_gate,sr_rotate.
    unfold at_match in H4.
    inv H7. inv H14. inv H3. inv H10. apply H4 in H17 as X1.
    rewrite gen_sr_gate_eval with (asize := b) (tenv := tenv'); try easy.
    unfold size_env in *. lia.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
  - Local Opaque gen_srr_gate. simpl.
    Local Transparent gen_srr_gate. unfold gen_srr_gate,srr_rotate.
    unfold at_match in H4.
    inv H7. inv H14. inv H3. inv H10. apply H4 in H17 as X1.
    rewrite gen_srr_gate_eval with (asize := b) (tenv := tenv'); try easy.
    unfold size_env in *. lia.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
(*
  - simpl. inv H3.
    rewrite uc_cnot_control; try easy.
    rewrite control_correct. inv H7. inv H3.
    apply (H8 Had) in H19 as eq1.
    apply (H8 Had) in H20 as eq2. inv eq1. inv eq2.
    unfold hexchange.
    rewrite Mmult_plus_distr_r.
    rewrite Mmult_assoc.
    assert ((uc_eval (SQIR.X (find_pos vs p2))
      × vkron dim (trans_state avs rmax f))
      = (vkron dim (trans_state avs rmax (f[p2 |-> exchange (f p2)])))).
    rewrite vkron_X. 
    assert (vkron dim (trans_state avs rmax (f [p2 |-> exchange (f p2)])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p2) (compile_val (exchange (f p2)) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy. easy.
    rewrite H21.  rewrite vkron_split_up.
    assert ((σx × trans_state avs rmax f (find_pos vs p2))
                 = compile_val (exchange (f p2)) rmax).
    { unfold trans_state.
      rewrite vs_avs_bij_l with (dim := dim); try easy.
      unfold exchange.
      rewrite <- H14. 
      unfold compile_val.
      distribute_scale.
      autorewrite with ket_db. rewrite Mplus_comm. easy.
      }
    rewrite H22. easy.
    auto with wf_db.
    auto with wf_db.
    apply H5. assumption.
    apply H5. assumption.
    auto with wf_db.
    rewrite H21. clear H21.
    destruct (eqb b0 b3) eqn:eq1.
    apply Bool.eqb_prop in eq1.
    rewrite <- H14. unfold exchange. subst.
    rewrite eupdate_same by easy.
    rewrite eupdate_same by easy.
    rewrite <- Mmult_plus_distr_r.
    rewrite Mplus_comm.
    rewrite proj_sum.
    Msimpl. easy.
    apply H5. easy.
    apply eqb_false_iff in eq1.
    unfold exchange. rewrite <- H14.
    rewrite (vkron_split dim (find_pos vs p1)).
    assert (trans_state avs rmax f (find_pos vs p1) = (/ √ 2)%R * Cexp (2 * PI * (turn_angle r rmax)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩)).
    unfold trans_state,compile_val.
    rewrite vs_avs_bij_l with (dim := dim); try easy.
    rewrite <- H3. easy.
    rewrite H21.
    distribute_scale.
    distribute_plus.
    distribute_scale.
    assert (@Mmult (2 ^ dim) (2 ^ dim) 1 
            (proj (find_pos vs p1) dim false)
            (vkron (find_pos vs p1) (trans_state avs rmax f) ⊗ ∣1⟩
              ⊗ vkron (dim - 1 - find_pos vs p1)
                  (shift (trans_state avs rmax f) (find_pos vs p1 + 1))) = Zero).
    replace ((dim - 1 - find_pos vs p1)) with (dim - (1 + find_pos vs p1)) by lia.
    unfold proj,pad.
    assert (∣1⟩ = ket (Nat.b2n true)). autorewrite with ket_db. simpl. easy. rewrite H22.
    gridify.
    assert ((find_pos vs p1 + 1 + d - S (find_pos vs p1)) = d) by lia. rewrite H16.
    autorewrite with ket_db. easy.
    rewrite H22. clear H22. Msimpl.
    rewrite (vkron_split dim (find_pos vs p1) (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]))).
    assert (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]) (find_pos vs p1) = (/ √ 2)%R * Cexp (2 * PI * (turn_angle r rmax)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩)).
    unfold trans_state,compile_val.
    rewrite vs_avs_bij_l with (dim := dim); try easy.
    rewrite eupdate_index_neq by iner_p. rewrite <- H3. easy.
    rewrite H22. clear H22.
    distribute_scale.
    distribute_plus.
    distribute_scale.
    assert (@Mmult (2 ^ dim) (2 ^ dim) 1 
            (proj (find_pos vs p1) dim true)
            (vkron (find_pos vs p1)
                (trans_state avs rmax (f [p2 |-> hval b3 b0 r0])) ⊗ ∣0⟩
              ⊗ vkron (dim - 1 - find_pos vs p1)
                  (shift
                     (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]))
                     (find_pos vs p1 + 1))) = Zero).
    replace ((dim - 1 - find_pos vs p1)) with (dim - (1 + find_pos vs p1)) by lia.
    unfold proj,pad.
    assert (∣0⟩ = ket (Nat.b2n false)). autorewrite with ket_db. simpl. easy. rewrite H22.
    gridify.
    assert ((find_pos vs p1 + 1 + d - S (find_pos vs p1)) = d) by lia. rewrite H16.
    autorewrite with ket_db. easy.
    rewrite H22. clear H22. Msimpl.
    assert ((@Mmult (Nat.pow (S (S O)) dim) (Nat.pow (S (S O)) dim)
          (Init.Nat.mul (Init.Nat.mul (S O) (S O)) (S O))
          (proj (find_pos vs p1) dim false)
      (vkron (find_pos vs p1) (trans_state avs rmax f) ⊗ ∣0⟩
       ⊗ vkron (dim - 1 - find_pos vs p1)
           (shift (trans_state avs rmax f) (find_pos vs p1 + 1))))
      = (vkron (find_pos vs p1) (trans_state avs rmax f) ⊗ ∣0⟩
       ⊗ vkron (dim - 1 - find_pos vs p1)
           (shift (trans_state avs rmax f) (find_pos vs p1 + 1)))).
    replace ∣0⟩ with (compile_val (nval false allfalse) rmax).
    replace ((dim - 1 - find_pos vs p1)) with (dim - ((find_pos vs p1) + 1)) by lia.
    rewrite <- vkron_split_eup.
    rewrite vkron_proj_eq with (r := Cexp 0). easy.
    intros. auto with wf_db.
    apply H5. easy.
    unfold trans_state.
    rewrite vs_avs_bij_l with (dim := dim); try easy.
    rewrite eupdate_index_eq.
    unfold compile_val.
    rewrite turn_angle_0.
    rewrite Rmult_0_r. easy.
    apply H5. easy. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
    unfold compile_val.
    rewrite turn_angle_0.
    rewrite Rmult_0_r.
    simpl. rewrite Cexp_0. rewrite Mscale_1_l.
    autorewrite with ket_db. easy.
    rewrite H22. clear H22.
    assert ((@Mmult (Nat.pow (S (S O)) dim) (Nat.pow (S (S O)) dim)
          (Init.Nat.mul (Init.Nat.mul (S O) (S O)) (S O))
           (proj (find_pos vs p1) dim true)
            (vkron (find_pos vs p1)
                (trans_state avs rmax (f [p2 |-> hval b3 b0 r0])) ⊗ ∣1⟩
              ⊗ vkron (dim - 1 - find_pos vs p1)
                  (shift
                     (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]))
                     (find_pos vs p1 + 1))))
        = (vkron dim
                (trans_state avs rmax ((f [p2 |-> hval b3 b0 r0])[p1 |-> nval true allfalse])))).
    replace ∣1⟩ with (compile_val (nval true allfalse) rmax).
    replace ((dim - 1 - find_pos vs p1)) with (dim - ((find_pos vs p1) + 1)) by lia.
    rewrite <- vkron_split_eup.
    rewrite vkron_proj_eq with (r := Cexp 0). easy.
    intros. auto with wf_db.
    apply H5. easy.
    unfold trans_state.
    rewrite vs_avs_bij_l with (dim := dim); try easy.
    rewrite eupdate_index_eq.
    unfold compile_val.
    rewrite turn_angle_0.
    rewrite Rmult_0_r. easy.
    apply H5. easy. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
    unfold compile_val.
    rewrite turn_angle_0.
    rewrite Rmult_0_r.
    simpl. rewrite Cexp_0. rewrite Mscale_1_l.
    autorewrite with ket_db. easy.
    rewrite H22. clear H22.
    rewrite eupdate_twice_neq by iner_p.
    rewrite vkron_split_eup with (vs := vs).
    assert (compile_val (hval b3 b0 r0) rmax
      = (RtoC (-1)%R) .* compile_val (hval b0 b3 r0) rmax).
    unfold compile_val.
    destruct b0 eqn:eq2. destruct b3 eqn:eq3. easy.
    unfold z_phase.
    rewrite Mscale_assoc.
    rewrite Cmult_comm with (x := RtoC (-1)%R).
    rewrite <- Mscale_assoc with (y := RtoC (-1)%R).
    rewrite Mscale_plus_distr_r with (x := RtoC (-1)%R).
    rewrite Mscale_assoc.
    rewrite Mscale_assoc.
    assert (((-1)%R * 1%R)%C = RtoC (-1)%R) by lca.
    rewrite H22.
    assert (((-1)%R * (-1)%R)%C = RtoC 1%R) by lca.
    rewrite H23. easy.
    destruct b3.
    unfold z_phase.
    rewrite Mscale_assoc.
    rewrite Cmult_comm with (x := RtoC (-1)%R).
    rewrite <- Mscale_assoc with (y := RtoC (-1)%R).
    rewrite Mscale_plus_distr_r with (x := RtoC (-1)%R).
    rewrite Mscale_assoc.
    rewrite Mscale_assoc.
    assert (((-1)%R * 1%R)%C = RtoC (-1)%R) by lca.
    rewrite H22.
    assert (((-1)%R * (-1)%R)%C = RtoC 1%R) by lca.
    rewrite H23. easy. easy.
    rewrite H22. clear H22.
    distribute_scale.
    rewrite <- vkron_split_eup.
    assert (((f [p1 |-> nval true allfalse]) [p2
                    |-> hval b0 b3 r0]) = (f [p1 |-> nval true allfalse])).
    rewrite eupdate_same. easy.
    rewrite eupdate_index_neq by iner_p. rewrite <- H14. easy.
    rewrite H22. clear H22.
    rewrite vkron_split_eup with (vs := vs).
    replace (compile_val (nval true allfalse) rmax) with ∣1⟩.
    rewrite vkron_split_eup with (vs := vs).
    unfold compile_val.
    assert (z_phase (¬ b2) = ((-1)%R * z_phase (b2))%R).
    unfold z_phase. destruct b2. simpl. lra. simpl. lra.
    rewrite H22. clear H22.
    autorewrite with RtoC_db eval_db C_db ket_db.
    assert (RtoC (-1 * z_phase b2)%R = ((RtoC (z_phase b2)%R) * (RtoC (-1)%R))%C) by lca.
    rewrite H22.
    rewrite Cmult_assoc.
    rewrite <- Mscale_assoc with (y := RtoC (-1)%R).
    replace ((dim - 1 - find_pos vs p1)) with (dim - (find_pos vs p1 + 1)) by lia.
    easy.
    apply H5. easy. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
    unfold compile_val. rewrite turn_angle_0. rewrite Rmult_0_r. rewrite Cexp_0.
    Msimpl. simpl. autorewrite with ket_db. easy.
    apply H5. easy. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
    apply H5. easy. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
    apply H5. easy. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
    auto with wf_db.
    apply H5. easy.
    auto with wf_db.
    apply H5. easy.
    1-2:easy.
    assert (SQIR.X (find_pos vs p2) = fst (fst (trans_exp vs dim (X p2) avs))) by easy.
    rewrite H3.
    apply fresh_is_fresh; try easy. constructor. inv H7. inv H14. easy. constructor. easy.
    assert (SQIR.X (find_pos vs p2) = fst (fst (trans_exp vs dim (X p2) avs))) by easy.
    rewrite H3. inv H7. inv H14.
    apply trans_exp_uc_well_typed with (tenv:=tenv') (tenv':=tenv'); try easy. constructor.
    apply x_had. easy. constructor. easy. 
    apply H5. easy. apply H5. easy.
    apply find_pos_prop; try easy. inv H7. inv H3. easy.
*)
  - simpl. rewrite denote_ID_1. Msimpl. unfold size_env. 
    rewrite <- lshift_avs_lshift_same; try easy.
    inv H3. easy. unfold exp_com_WF,find_pos in H5.
    specialize (H5 (x,0)). simpl in H5. apply H5. inv H3. easy.
  - simpl. rewrite denote_ID_1. Msimpl. unfold size_env. rewrite <- rshift_avs_rshift_same; try easy.
    inv H3. easy. unfold exp_com_WF,find_pos in H5.
    specialize (H5 (x,0)). simpl in H5. apply H5. inv H3. easy.
  - simpl. rewrite denote_ID_1. Msimpl. unfold size_env. rewrite <- rev_avs_rev_same; try easy.
    inv H3. easy. unfold exp_com_WF,find_pos in H3.
    specialize (H5 (x,0)). simpl in H5. apply H5. inv H3. easy.
  - unfold trans_qft,turn_qft.
    inv H7. inv H14.
    assert (nor_modes f x (size_env vs x)).
    unfold right_mode_env,nor_modes,nor_mode in *. intros.
    specialize (H8 Nor (x,i)). simpl in H8. apply (H8 H7) in H18.
    inv H18. easy.
    inv H3. simpl.
    inv H10.
    rewrite Mmult_assoc.
    rewrite gen_qft_gate_eval with (g := (get_cus b f x)); try easy.
    rewrite gen_h_gate_eval; try easy.
    unfold size_env in *. simpl. lia.
    intros. 
    unfold nor_mode. rewrite assign_r_ge by lia.
    apply H7. unfold size_env in *. lia. lia.
  - specialize (trans_exp_uc_well_typed (RQFT x b)
               dim vs avs tenv tenv' H H0 H1 H7 H3 H5) as X1.
    Local Opaque trans_rqft. simpl in *.
    Local Transparent trans_rqft. 
    unfold trans_rqft, turn_rqft in *.
    rewrite <- invert_correct.
    apply Mmult_adj_add.
    rewrite invert_correct.
    apply uc_eval_unitary_iff. easy.
    auto with wf_db.
    auto with wf_db.
    apply uc_eval_unitary_iff in X1.
    rewrite <- invert_correct in X1.
    unfold WF_Unitary in X1.
    destruct X1.
    rewrite H15.
    rewrite Mmult_1_l.
    rewrite adjoint_involutive.
    assert (phi_modes f x (size_env vs x)) as X1.
    apply type_phi_modes with (env := tenv) (b := b); try easy.
    inv H7. inv H16. easy.
    simpl.
    rewrite Mmult_assoc.
    inv H3. unfold at_match in *.
    inv H7. inv H3.
    apply H12 in H21 as X2. destruct X2.
    specialize (H11 x b H21) as X3.
    bdestruct (b =? 0). subst.
    simpl. rewrite denote_ID_1.
    Msimpl. unfold size_env in *.
    replace (vsize vs x - 0) with (vsize vs x) by lia.
    rewrite gen_h_gate_eval; try easy.
    rewrite assign_rh_cancel. easy.
    intros. apply X1; try lia.
    intros. apply H7; try lia.
    intros.
    assert (right_mode_val Nor (assign_h_r f x 0 (vsize vs x) (x, i))).
    apply assign_h_r_right_mode with (size := vsize vs x) (b := 0); try lia.
    intros. unfold phi_modes in X1.
    destruct H20.
    apply (X1 i0) in H22. unfold phi_mode in *. 
    destruct (f (x, i0)) eqn:eq1. easy.
    constructor.
    inv H20. unfold nor_mode. rewrite <- H22. easy. inv H10. easy.
    specialize (H5 (x,0)). simpl in H5. apply H5. easy.
    rewrite gen_qft_gate_eval with (g := (get_r_qft f x)); try easy.
    rewrite gen_h_gate_eval; try easy.
    rewrite assign_h_r_flip by lia.
    rewrite assign_rh_cancel.
    rewrite assign_r_cover_full with (aenv := size_env vs) (tenv := tenv); try easy.
    intros.
    unfold phi_mode.
    rewrite assign_seq_ge by lia.
    apply X1. unfold size_env in *. lia.
    intros. 
    unfold get_snd_r in *.
    rewrite assign_seq_ge by lia.
    apply H7; try easy.
    unfold size_env. lia.
    unfold size_env in *. lia.
    intros.
    specialize (phi_to_nor_modes x b ((size_env vs) x) (size_env vs) f) as X4.
    apply X4 in X1; try lia.
    simpl in X1. unfold turn_rqft in X1.
    unfold nor_modes,nor_mode in *.
    rewrite assign_r_ge by lia.
    apply X1. unfold size_env in *. lia. inv H10. lia.
    specialize (phi_to_nor_modes x b ((size_env vs) x) (size_env vs) f) as X4.
    apply X4 in X1; try lia.
    simpl in X1. unfold turn_rqft in X1. easy.
    unfold nor_modes,nor_mode in *.
    rewrite get_cus_assign_hr_same.
    rewrite get_cus_assign_seq.
    rewrite cut_n_eq. easy.
    intros.
    specialize (X3 0).
    assert (0 < b) by lia.
    apply X3 in H22.
    rewrite lshift_fun_0 in H22.
    specialize (H3 i). rewrite H3. easy. lia. easy. inv H10. lia.
    auto with wf_db.
(*
  - simpl.
    inv H7. inv H14.
    apply gen_h_gate_eval with (tenv := tenv); try easy.
    inv H3. easy. left. easy. inv H10. lia.
    apply gen_h_gate_eval with (tenv := tenv); try easy.
    inv H3. easy. right. easy. inv H10. lia.
*)
  - simpl.
    destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
    destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl. inv H3. inv H7. inv H3.
    inv H10.
    rewrite Mmult_assoc.
    assert (b = fst (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
    rewrite H3.
    rewrite (IHe1 f tenv) with (tenv':=env'); try easy.
    assert (b0 = fst (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
    rewrite H7. rewrite eq1. simpl.
    rewrite (IHe2 (exp_sem (size_env vs) e1 f) env' tenv'); try easy.
    rewrite eq2. simpl.
    rewrite (size_env_vs_same vs v e1 dim avs). easy.
    rewrite eq1. easy.
    apply (vars_start_diff_vs_same vs v e1 dim avs).
    rewrite eq1. easy. easy.
    apply (vars_finite_bij_vs_same e1 dim vs v avs).
    rewrite eq1. easy. easy.
    apply (vars_sparse_vs_same e1 dim vs v avs).
    rewrite eq1. easy. easy.
    apply (vars_anti_vs_same e1 dim vs v avs).
    rewrite eq1. easy. easy.
    erewrite size_env_vs_same with (vs := vs); try easy.
    rewrite eq1. easy.
    apply at_match_trans with (tenv := tenv) (e := e1); try easy.
    erewrite size_env_vs_same with (vs := vs); try easy.
    rewrite eq1. easy.
    erewrite size_env_vs_same with (vs := vs); try easy.
    rewrite eq1. easy.
    apply (exp_com_WF_vs_same e1 dim avs vs v).
    rewrite eq1. easy. easy.
    apply (exp_com_gt_vs_same e1 dim vs v avs p0).
    rewrite eq1. easy. rewrite eq1. easy. easy.
    rewrite (size_env_vs_same vs v e1 dim avs); try easy.
    rewrite eq1. easy.
    rewrite size_env_vs_same with (vs := vs) (e:=e1) (dim := dim) (avs := avs).
    apply well_typed_right_mode_pexp with (tenv := tenv); try easy.
    rewrite eq1. easy.
    apply (avs_prop_vs_same e1 dim vs v avs p0).
    rewrite eq1. easy. rewrite eq1. easy. easy.
    easy. easy.
    rewrite size_env_vs_same with (vs := vs) (e:=e1) (dim := dim) (avs := avs). easy.
    rewrite eq1. easy.
    rewrite size_env_vs_same with (vs := vs) (e:=e1) (dim := dim) (avs := avs).
    apply qft_uniform_exp_trans with (tenv := tenv) ; try easy.
    rewrite eq1. easy.
    rewrite size_env_vs_same with (vs := vs) (e:=e1) (dim := dim) (avs := avs).
    apply qft_gt_exp_trans with (tenv := tenv) ; try easy.
    rewrite eq1. easy.
Qed.

(* some useful gates. *)
Definition CNOT (x y : posi) := CU x (X y).
Definition SWAP (x y : posi) := if (x ==? y) then (SKIP x) else (CNOT x y; CNOT y x; CNOT x y).
Definition CCX (x y z : posi) := CU x (CNOT y z).

(*
Lemma cnot_fwf : forall x y aenv, x<> y -> exp_fwf aenv (CNOT x y).
Proof.
  intros.
  unfold CNOT. constructor.
  constructor. easy.
  constructor.
Qed.

Lemma swap_fwf : forall x y aenv, exp_fwf aenv (SWAP x y).
Proof.
  intros.
  unfold SWAP.
  bdestruct (x ==? y).
  constructor.
  constructor.
  constructor. apply cnot_fwf. easy.
  apply cnot_fwf. nor_sym.
  constructor. constructor. easy.
  constructor.
Qed.

Lemma ccx_fwf : forall x y z aenv, x <> y -> y <> z -> z <> x -> exp_fwf aenv (CCX x y z).
Proof.
  intros.
  unfold CCX.
  constructor. constructor. easy.
  constructor. nor_sym.
  constructor. constructor.
  easy.
  constructor.
Qed.
*)

(* Proofs of semantics. *)
Lemma cnot_sem : forall f x y aenv, nor_mode f x -> nor_mode f y -> 
              exp_sem aenv (CNOT x y) f = (f[y |-> put_cu (f y) (get_cua (f x) ⊕ get_cua (f y))]).
Proof.
 intros.
 unfold CNOT.
 assert (eq1 := H).
 apply nor_mode_nval in H.
 destruct H. destruct H.
 simpl.
 destruct (get_cua (f x)).
 bt_simpl.
 unfold exchange.
 destruct (f y) eqn:eq2.
 simpl. easy.
 unfold nor_mode in H0.
 rewrite eq2 in H0. inv H0.
 bt_simpl.
 rewrite put_get_cu.
 rewrite eupdate_same. easy. easy. easy.
 simpl.
 assert (get_cua (f x) = false). unfold get_cua. rewrite H. easy.
 rewrite H1.
 destruct (f y) eqn:eq2.
 simpl. destruct b.
 rewrite <- eq2. rewrite eupdate_same. easy. easy.
 rewrite <- eq2. rewrite eupdate_same. easy. easy.
 unfold nor_mode in H0.
 rewrite eq2 in H0. inv H0.
Qed.

Lemma cnot_nor : forall f x y v aenv, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> exp_sem aenv (CNOT x y) f = (f[y |-> v]).
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma cnot_nor_1 : forall f f' x y v aenv, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> f[y|-> v] = f'
           -> exp_sem aenv (CNOT x y) f = f'.
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma ccx_sem : forall f x y z aenv, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                    exp_sem aenv (CCX x y z) f = (f[z |-> put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x)))]).
Proof.
 intros. 
 assert (eq1 := H).
 unfold CCX. apply nor_mode_nval in H.
 destruct H. destruct H.
 simpl. rewrite H. simpl.
 destruct (f z) eqn:eq2.
 unfold exchange.
 simpl.
 destruct (get_cua (f y)) eqn:eq3.
 simpl. easy.
 simpl. rewrite eupdate_same. easy. rewrite eq2.
 bt_simpl. easy.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 unfold nor_mode in H1.
 simpl.
 rewrite H. simpl. bt_simpl.
 rewrite put_get_cu. rewrite eupdate_same. easy. easy. assumption.
Qed.

Lemma ccx_nor : forall f f' x y z v aenv, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                       put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x))) = v ->
                       f = f' ->
                    exp_sem aenv (CCX x y z) f = (f'[z |-> v]).
Proof.
 intros. subst. apply ccx_sem. 1 - 6: assumption. 
Qed.


Definition id_nat := fun i :nat => i.
Definition avs_for_arith (size:nat) := fun x => (x/size, x mod size).
Fixpoint gen_vars' (size:nat) (l : list var) (start:nat) :=
      match l with [] => (fun _ => (0,0,id_nat,id_nat))
             | (x::xl) => (fun y => if x =? y then (start,size,id_nat,id_nat) else 
                                gen_vars' size xl (start+size) y)
      end.
Definition gen_vars (size:nat) (l:list var) := gen_vars' size l 0.




Fixpoint copyto (x y:var) size := match size with 0 => SKIP (x,0) 
                  | S m => copyto x y m;CNOT (x,m) (y,m)
    end.



Lemma cnot_wt_nor : forall aenv env x y, x <> y -> Env.MapsTo (fst x) Nor env -> 
                   Env.MapsTo (fst y) Nor env -> well_typed_oexp aenv env (CNOT x y) env.
Proof.
  intros. unfold CNOT.
  apply pcu_nor. easy. constructor. easy.
  unfold exp_neu. intros. constructor.
  constructor. constructor. easy.
Qed.

(*
Lemma cnot_wt_had : forall aenv env x y, x <> y -> Env.MapsTo (fst x) Nor env -> 
                   Env.MapsTo (fst y) Had env -> well_typed_oexp aenv env (CNOT x y) env.
Proof.
  intros. unfold CNOT.
  apply pcu_nor. easy. constructor. easy.
  unfold exp_neu. intros. constructor.
  constructor. apply x_had. easy.
Qed.
*)

Lemma ccx_wt_nor : forall aenv env x y z, x <> y -> y <> z -> z <> x -> Env.MapsTo (fst x) Nor env -> 
                   Env.MapsTo (fst y) Nor env -> Env.MapsTo (fst z) Nor env
                   -> well_typed_oexp aenv env (CCX x y z) env.
Proof.
  intros. unfold CCX.
  apply pcu_nor. easy. constructor. easy.
  constructor. iner_p.
  unfold exp_neu. intros. constructor.
  constructor.
  apply cnot_wt_nor. easy. easy. easy.
Qed.

Lemma swap_wt_nor : forall aenv env x y, x <> y -> Env.MapsTo (fst x) Nor env -> 
                   Env.MapsTo (fst y) Nor env -> well_typed_oexp aenv env (SWAP x y) env.
Proof.
  intros. unfold SWAP.
  bdestruct (x ==? y). subst. constructor. constructor.
  apply pe_seq with (env' := env).
  apply pe_seq with (env' := env).
  apply cnot_wt_nor. easy. easy. easy.
  apply cnot_wt_nor. iner_p. easy. easy.
  apply cnot_wt_nor. easy. easy. easy.
Qed.


Lemma sr_phi_mode : forall p1 x m f aenv, phi_mode f p1 -> phi_mode (exp_sem aenv (SR m x) f) p1.
Proof.
  intros. unfold phi_mode in *. 
  destruct p1. simpl.
  unfold sr_rotate.
  bdestruct (x =? v). subst.
  bdestruct (n <? S m).
  rewrite sr_rotate'_lt_1 by lia.
  destruct (f (v,n)) eqn:eq1.
  easy. easy.
  unfold times_rotate.
  rewrite sr_rotate'_ge. easy. simpl. lia.
  rewrite sr_rotate'_irrelevant. easy. simpl. lia.
Qed.

Lemma sr_phi_modes : forall x y n m f aenv, phi_modes f x n -> phi_modes (exp_sem aenv (SR m y) f) x n.
Proof.
  intros. unfold phi_modes in *. 
  intros.
  apply H in H0.
  apply sr_phi_mode. easy.
Qed.

Lemma srr_phi_mode : forall p1 x m f aenv, phi_mode f p1 -> phi_mode (exp_sem aenv (SRR m x) f) p1.
Proof.
  intros. unfold phi_mode in *. 
  destruct p1. simpl.
  unfold srr_rotate.
  bdestruct (x =? v). subst.
  bdestruct (n <? S m).
  rewrite srr_rotate'_lt_1 by lia.
  destruct (f (v,n)) eqn:eq1.
  easy. easy.
  unfold times_r_rotate.
  rewrite srr_rotate'_ge. easy. simpl. lia.
  rewrite srr_rotate'_irrelevant. easy. simpl. lia.
Qed.

Lemma srr_phi_modes : forall x y n m f aenv, phi_modes f x n -> phi_modes (exp_sem aenv (SRR m y) f) x n.
Proof.
  intros. unfold phi_modes in *. 
  intros.
  apply H in H0.
  apply srr_phi_mode. easy.
Qed.

Definition get_phi_r (v:val) := match v with qval r1 r2 => r2 | _ => allfalse end.

Lemma sr_rotate_get_r : forall n size f x, 0 < n <= size -> get_r_qft (sr_rotate' f x n size) x
                 = get_phi_r (times_rotate (f (x,0)) size).
Proof.
  induction n;intros; simpl. lia.
  unfold get_r_qft.
  bdestruct (n =? 0). subst. 
  rewrite eupdate_index_eq.
  unfold get_phi_r.
  assert (size - 0=size) by lia. rewrite H0. easy.
  rewrite eupdate_index_neq by iner_p.
  unfold get_r_qft in IHn. rewrite IHn. easy. lia.
Qed.

Lemma sr_rotate'_phi : forall m n size f x, m <= n <= size -> phi_modes f x size
             -> phi_modes ((sr_rotate' f x m n)) x size.
Proof.
  induction m; intros ; simpl; try easy.
  unfold phi_modes in *. intros.
  unfold phi_mode in *. 
  bdestruct (m =? i). subst.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  apply H0 in H1. destruct (f (x,i)) eqn:eq1. lia. lia.
  rewrite eupdate_index_neq by iner_p.
  apply IHm with (size := size). lia. easy. lia.
Qed.

Lemma srr_rotate_get_r : forall n size f x, 0 < n <= size -> get_r_qft (srr_rotate' f x n size) x
                 = get_phi_r (times_r_rotate (f (x,0)) size).
Proof.
  induction n;intros; simpl. lia.
  unfold get_r_qft.
  bdestruct (n =? 0). subst. 
  rewrite eupdate_index_eq.
  unfold get_phi_r.
  assert (size - 0=size) by lia. rewrite H0. easy.
  rewrite eupdate_index_neq by iner_p.
  unfold get_r_qft in IHn. rewrite IHn. easy. lia.
Qed.

Lemma srr_rotate'_phi : forall m n size f x, m <= n <= size -> phi_modes f x size
             -> phi_modes ((srr_rotate' f x m n)) x size.
Proof.
  induction m; intros ; simpl; try easy.
  unfold phi_modes in *. intros.
  unfold phi_mode in *. 
  bdestruct (m =? i). subst.
  rewrite eupdate_index_eq.
  unfold times_r_rotate.
  apply H0 in H1. destruct (f (x,i)) eqn:eq1. lia. lia.
  rewrite eupdate_index_neq by iner_p.
  apply IHm with (size := size). lia. easy. lia.
Qed.

Lemma get_r_qft_out : forall x c v f, fst c <> x -> get_r_qft (f[c |-> v]) x = get_r_qft f x.
Proof.
  intros. unfold get_r_qft.
  destruct c.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma env_eq_well_typed : forall e tenv tenv', Env.Equal tenv tenv' 
                 -> well_typed_exp tenv e -> well_typed_exp tenv' e.
Proof.
 intros.
 induction H0. constructor.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 constructor. eapply mapsto_equal.
 apply H0. easy.
 constructor. eapply mapsto_equal.
 apply H0. easy.
 apply sr_phi with (b := b). 
 eapply mapsto_equal. apply H0. easy. easy.
 apply srr_phi with (b:=b).
 eapply mapsto_equal. apply H0. easy. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
 constructor.
 eapply mapsto_equal. apply H0. easy.
Qed.

Lemma env_eq_right_mode : forall tenv tenv' aenv f, Env.Equal tenv tenv'
          -> right_mode_env aenv tenv f -> right_mode_env aenv tenv' f.
Proof.
  intros.
  unfold right_mode_env in *. intros.
  specialize (H0 t p H1).
  apply mapsto_equal with (s2 := tenv) in H2. apply H0. easy.
  apply EnvFacts.Equal_sym. easy.
Qed.


Lemma exp_fresh_init : forall n x size M aenv, 0 < size <= n
         -> exp_fresh aenv (x, n) (init_v size x M).
Proof.
  induction size;intros;simpl.
  simpl. constructor. iner_p.
  bdestruct (size =? 0). subst.
  destruct (M 0).
  constructor. simpl.
  constructor. iner_p.
  constructor. iner_p.
  constructor. iner_p.
  destruct (M size).
  constructor. apply IHsize. lia.
  constructor. iner_p.
  apply IHsize. lia. 
Qed.

Lemma exp_fresh_init_1 : forall n v x size M aenv, v <> x
         -> exp_fresh aenv (v, n) (init_v size x M).
Proof.
  induction size;intros;simpl.
  simpl. constructor. iner_p.
  destruct (M size).
  constructor. apply IHsize. easy.
  constructor. iner_p.
  apply IHsize. easy.
Qed.


Lemma exp_WF_init: forall n x M aenv, n <= aenv x -> 0 < aenv x -> exp_WF aenv (init_v n x M).
Proof.
 induction n;intros;simpl.
 constructor. simpl. easy.
 destruct (M n). constructor.
  apply IHn. lia. lia.
  constructor. simpl. lia.
 apply IHn. lia. lia.
Qed.


Lemma init_v_sem : forall n size x M f aenv tenv, get_cus size f x = nat2fb 0 -> 
            n <= size -> size = aenv x -> Env.MapsTo x Nor tenv
            -> right_mode_env aenv tenv f ->
            (exp_sem aenv (init_v n x M) f) = put_cus f x (cut_n M n) size.
Proof.
  induction n; intros;simpl.
  unfold put_cus,cut_n.
  apply functional_extensionality; intro.
  destruct x0. simpl in *.
  bdestruct (v =? x). rewrite H4 in *.
  bdestruct (n <? size).
  assert (nor_modes f x (aenv x)).
  apply type_nor_modes with (env := tenv); try easy.
  rewrite <- H1 in H6. 
  unfold nor_modes in H6.
  assert (forall i, i < size -> get_cus size f x i = false).
  intros.
  rewrite H. unfold nat2fb. simpl. easy.
  unfold put_cu.
  specialize (H6 n H5).
  specialize (H7 n H5).
  rewrite get_cus_cua in H7; try easy.
  unfold get_cua,nor_mode in *.
  destruct (f (x,n)) eqn:eq1. 
  rewrite H7. easy. easy. easy. easy.
  unfold put_cus,cut_n.
  apply functional_extensionality; intro.
  destruct x0. simpl in *.
  bdestruct (v =? x). rewrite H4 in *.
  bdestruct (n0 <? size).
  assert (nor_modes f x (aenv x)).
  apply type_nor_modes with (env := tenv); try easy.
  rewrite <- H1 in H6. 
  unfold nor_modes in H6.
  assert (forall i, i < size -> get_cus size f x i = false).
  intros.
  rewrite H. unfold nat2fb. simpl. easy.
  destruct (M n) eqn:eq1.
  simpl.
  bdestruct (n =? n0). rewrite H8 in *. 
  rewrite eupdate_index_eq.
  rewrite IHn with (size := size) (tenv := tenv); try easy.
  specialize (H6 n0 H5). specialize (H7 n0 H5).
  unfold exchange,put_cus,put_cu,nor_mode,get_cus,cut_n in *.
  simpl in *.
  bdestruct (x =? x).
  bdestruct (n0 <? size).
  bdestruct (n0 <? S n0 ).
  bdestruct (n0 <? n0). lia.
  destruct (f (x, n0)) eqn:eq2.
  rewrite eq1. easy. lia. lia. lia. lia. lia.
  rewrite eupdate_index_neq; iner_p.
  rewrite IHn with (size := size) (tenv := tenv); try easy.
  specialize (H6 n0 H5). specialize (H7 n0 H5).
  unfold exchange,put_cus,put_cu,nor_mode,get_cus,cut_n in *.
  simpl in *.
  bdestruct (x =? x).
  bdestruct (n0 <? size).
  bdestruct (n0 <? S n).
  bdestruct (n0 <? n). easy. lia.
  bdestruct (n0 <? n). lia. easy.
  lia. lia. lia.
  rewrite IHn with (size := size) (tenv := tenv); try easy.
  specialize (H6 n0 H5). specialize (H7 n0 H5).
  unfold exchange,put_cus,put_cu,nor_mode,get_cus,cut_n in *.
  simpl in *.
  bdestruct (x =? x).
  bdestruct (n0 <? size).
  bdestruct (n0 <? S n).
  bdestruct (n0 <? n). easy.
  assert ( n = n0) by lia. subst. rewrite eq1. easy.
  bdestruct (n0 <? n). lia. easy.
  bdestruct (n0 <? S n). lia. lia. lia. lia.
  bdestruct (n =? 0). rewrite H6 in *.
  simpl.
  destruct (M 0). simpl. rewrite eupdate_index_neq; iner_p. easy.
  simpl. easy.
  rewrite efresh_exp_sem_irrelevant ; try easy.
  destruct (M n). constructor.
  apply exp_WF_init; try lia. constructor. simpl. lia.
  apply exp_WF_init; try lia.
  destruct (M n). constructor.
  apply exp_fresh_init. lia. constructor. iner_p.
  apply exp_fresh_init. lia.
  rewrite efresh_exp_sem_irrelevant ; try easy.
  destruct (M n). constructor.
  apply exp_WF_init; try lia. constructor. simpl. lia.
  apply exp_WF_init; try lia.
  destruct (M n). constructor.
  apply exp_fresh_init_1. lia. constructor. iner_p.
  apply exp_fresh_init_1. lia.  
Qed.

Lemma well_typed_init_v : forall n x v aenv tenv, Env.MapsTo x Nor tenv -> well_typed_oexp aenv tenv (init_v n x v) tenv.
Proof.
 induction n;intros;simpl.
 constructor. constructor.
 destruct (v n).
 apply pe_seq with (env' := tenv).
 apply IHn. easy.
 constructor. constructor. easy.
 apply IHn. easy.
Qed. 

Lemma right_mode_up_nor : forall aenv tenv f p v, Env.MapsTo (fst p) Nor tenv -> right_mode_env aenv tenv f ->
              right_mode_env aenv tenv (f[p |-> put_cu (f p) v]).
Proof.
  unfold right_mode_env in *.
  intros.
  bdestruct (p ==? p0).
  subst.
  rewrite eupdate_index_eq.
  assert (nor_mode f p0).
  unfold nor_mode.
  specialize (H0 Nor p0).
  apply H0 in H; try easy.
  inv H. easy. 
  unfold put_cu,nor_mode in *.
  destruct (f p0) eqn:eq1.
  apply mapsto_always_same with (v1:=Nor) in H2; try easy.
  subst. constructor. easy.
  rewrite eupdate_index_neq; iner_p.
  apply H0; try easy.
Qed.

Definition bin_xor (f1 f2:nat -> bool) (size:nat) :=
  cut_n (fun x => xorb (f1 x) (f2 x)) size.

Lemma init_v_sem_full : forall n size x M f aenv tenv, 
            n <= size -> size = aenv x -> Env.MapsTo x Nor tenv
            -> right_mode_env aenv tenv f ->
            (exp_sem aenv (init_v n x M) f) = put_cus f x (bin_xor (get_cus n f x) M n) n.
Proof.
  induction n; intros;simpl.
  unfold put_cus,cut_n.
  apply functional_extensionality; intro.
  destruct x0. simpl in *.
  bdestruct (v =? x). easy. easy.
  assert (n <= size) by lia.
  specialize (IHn size x M f aenv tenv H3 H0 H1 H2).
  apply functional_extensionality; intro.
  assert (nor_modes f x (aenv x)).
  apply type_nor_modes with (env := tenv); try easy.
  rewrite <- H0 in H4. 
  unfold nor_modes in H4.
  destruct (M n) eqn:eq1.
  destruct x0. simpl in *.
  bdestruct (v =? x). subst.
  bdestruct ( n =? n0). subst.
  rewrite eupdate_index_eq.
  bdestruct (n0 =? 0). subst.
  simpl.
  rewrite put_cus_eq by lia.
  unfold bin_xor,cut_n,exchange,put_cu. rewrite eq1. bt_simpl.
  rewrite get_cus_cua by lia.
  bdestruct (0 <? 1).
  unfold get_cua.
  assert (0 < aenv x) by lia.
  specialize (H4 0 H5). unfold nor_mode in *.
  destruct (f (x, 0)) eqn:eq2.
  assert ((@pair var nat x 0) = (@pair Env.key nat x 0)) by easy.
  rewrite H6 in *. rewrite eq2 in *. easy.
  assert ((@pair var nat x 0) = (@pair Env.key nat x 0)) by easy.
  rewrite H6 in *. rewrite eq2 in *. easy.
  lia.
  rewrite efresh_exp_sem_irrelevant ; try easy.
  rewrite put_cus_eq by lia.
  unfold bin_xor,cut_n.
  bdestruct (n0 <? S n0).
  rewrite eq1. bt_simpl.
  rewrite get_cus_cua by lia.
  assert (n0 < aenv x) by lia.
  specialize (H4 n0 H6). unfold nor_mode,exchange,put_cu,get_cua in *.
  destruct (f (x,n0)) eqn:eq2.
  assert ((@pair var nat x n0) = (@pair Env.key nat x n0)) by easy.
  rewrite H7 in *. rewrite eq2 in *.
  easy.
  assert ((@pair var nat x n0) = (@pair Env.key nat x n0)) by easy.
  rewrite H7 in *. rewrite eq2 in *. easy.
  lia.
  apply exp_WF_init; try lia. apply exp_fresh_init. lia.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  bdestruct (n0 <? n).
  unfold bin_xor,cut_n in *.
  rewrite put_cus_eq by lia.
  rewrite put_cus_eq by lia.
  bdestruct (n0 <? n). bdestruct (n0 <? S n).
  simpl.
  rewrite get_cus_cua by lia.
  rewrite get_cus_cua by lia. easy.
  lia. lia.
  rewrite put_cus_neq_2 by lia.
  rewrite put_cus_neq_2 by lia.
  easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  rewrite put_cus_neq by lia.
  rewrite put_cus_neq by lia. easy.
  rewrite IHn.
  destruct x0.
  bdestruct (v =? x). subst.
  bdestruct (n0 <? n).
  rewrite put_cus_eq by lia.
  rewrite put_cus_eq by lia.
  unfold bin_xor,cut_n in *.
  bdestruct (n0 <? n). bdestruct (n0 <? S n).
  rewrite get_cus_cua by lia.
  rewrite get_cus_cua by lia. easy. lia. lia.
  simpl.
  bdestruct (n0 =? n). subst.
  rewrite put_cus_neq_2 by lia.
  rewrite put_cus_eq by lia.
  unfold bin_xor,cut_n.
  rewrite eq1. bt_simpl.
  bdestruct (n <? S n).
  rewrite get_cus_cua by lia.
  rewrite put_get_cu; try easy.
  apply H4. easy. lia.
  rewrite put_cus_neq_2 by lia.
  rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by lia.
  rewrite put_cus_neq by lia. easy. 
Qed.


Lemma well_typed_copyto_nor : forall n x v aenv tenv, x <> v -> Env.MapsTo v Nor tenv ->
          Env.MapsTo x Nor tenv -> well_typed_oexp aenv tenv (copyto x v n) tenv.
Proof.
 induction n;intros;simpl.
 constructor. constructor.
 apply pe_seq with (env' := tenv).
 apply IHn;easy.
 apply pcu_nor. easy.
 constructor. iner_p.
 unfold exp_neu. intros. constructor.
 constructor. constructor. easy. 
Qed. 

Lemma exp_WF_copy: forall size x y aenv, 0 < size <= aenv x -> size < aenv y -> exp_WF aenv (copyto x y size).
Proof.
 induction size;intros;simpl.
 constructor. simpl. easy.
 destruct size. simpl. constructor. constructor. simpl. lia.
 constructor. simpl. lia. constructor. simpl. lia.
 constructor. apply IHsize. lia. lia.
 constructor. simpl. lia. constructor. simpl. lia.
Qed.

Lemma exp_fresh_copy : forall n x size y aenv, 0 < size <= n
         -> exp_fresh aenv (x, n) (copyto x y size).
Proof.
  induction size;intros;simpl.
  simpl. constructor. iner_p.
  bdestruct (size =? 0). subst.
  constructor. simpl. constructor. iner_p.
  constructor. iner_p.
  constructor. iner_p.
  constructor. apply IHsize. lia.
  constructor. iner_p.
  constructor. iner_p.
Qed.


Lemma copyto_sem' : forall n size x y f aenv tenv, 
            n <= size -> size = aenv x -> size = aenv y -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv
            -> right_mode_env aenv tenv f ->
            (exp_sem aenv (copyto x y n) f) = put_cus f y (bin_xor (get_cus size f y) (get_cus size f x) n) n.
Proof.
  induction n; intros;simpl in *.
  simpl.
  apply functional_extensionality; intro.
  destruct x0.
  unfold put_cus,bin_xor.
  simpl in *.
  bdestruct (v =? y). easy. easy.
  assert (nor_modes f x size).
  rewrite H0.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes f y size).
  rewrite H1.
  apply type_nor_modes with (env := tenv); try easy.
  bdestruct (n =? 0). subst.
  simpl.
  destruct (get_cua (f (x, 0))) eqn:eq1.
  assert ((@pair var nat x 0) = (@pair Env.key nat x 0)) by easy.
  rewrite H0 in *. rewrite eq1 in *.
  apply functional_extensionality; intro.
  destruct x0.
  bdestruct ((y,0) ==? (v,n)). inv H7.
  rewrite eupdate_index_eq.
  rewrite put_cus_eq by lia.
  unfold bin_xor,cut_n.
  bdestruct (0 <? 1).
  rewrite get_cus_cua by lia.
  rewrite get_cus_cua by lia.
  rewrite H0. rewrite eq1. bt_simpl.
  unfold exchange,put_cu,get_cua,nor_modes in *.
  specialize (H6 0).
  assert (0 < aenv x) by lia.
  apply H6 in H8. unfold nor_mode in *.
  destruct (f (v,0)). easy. easy. easy.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (y =? v). subst. assert (0 <> n).
  intros R. subst. contradiction.
  rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by lia. easy.
  assert ((@pair var nat x 0) = (@pair Env.key nat x 0)) by easy.
  rewrite H0 in *. rewrite eq1 in *.
  apply functional_extensionality; intro.
  destruct x0.
  bdestruct ((v,n) ==? (y,0)). inv H7.
  rewrite put_cus_eq by lia.
  unfold bin_xor,cut_n.
  bdestruct (0 <? 1).
  rewrite get_cus_cua by lia.
  rewrite get_cus_cua by lia.
  rewrite H0. rewrite eq1. bt_simpl.
  rewrite put_get_cu. easy. apply H6. easy. lia.
  bdestruct (y =? v). subst. assert (0 <> n).
  intros R. subst. contradiction.
  rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by lia. easy.
  rewrite efresh_exp_sem_irrelevant.
  destruct (get_cua (f (x, n))) eqn:eq1.
  assert ((@pair var nat x n) = (@pair Env.key nat x n)) by easy.
  rewrite H8 in *. rewrite eq1 in *.
  apply functional_extensionality; intro.
  destruct x0.
  bdestruct (v =? y). subst.
  bdestruct (n0 =? n). subst.
  rewrite eupdate_index_eq.
  rewrite put_cus_eq by lia.
  rewrite IHn with (size := aenv x) (tenv := tenv) ; try easy.
  rewrite put_cus_neq_2 by lia.
  unfold bin_xor,cut_n.
  bdestruct (n <? S n).
  rewrite get_cus_cua by lia.
  rewrite get_cus_cua by lia.
  rewrite H8. rewrite eq1. bt_simpl.
  unfold exchange,put_cu,get_cua,nor_modes in *.
  specialize (H6 n).
  assert (n < aenv x) by lia.
  apply H6 in H9. unfold nor_mode in *.
  destruct (f (y, n)) eqn:eq2.
  assert ((@pair var nat y n) = (@pair Env.key nat y n)) by easy.
  rewrite H10 in *. rewrite eq2 in *. easy. 
  assert ((@pair var nat y n) = (@pair Env.key nat y n)) by easy.
  rewrite H10 in *. rewrite eq2 in *. easy. 
  lia. lia.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn with (size := aenv x) (tenv := tenv) ; try easy.
  bdestruct (n0 <? n). 
  rewrite put_cus_eq by lia.
  rewrite put_cus_eq by lia.
  unfold bin_xor,cut_n.
  bdestruct (n0 <? n). bdestruct (n0 <? S n). easy. lia.  lia.
  rewrite put_cus_neq_2 by lia.
  rewrite put_cus_neq_2 by lia. easy. lia.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn with (size := aenv x) (tenv := tenv) ; try easy.
  rewrite put_cus_neq by lia.
  rewrite put_cus_neq by lia. easy. lia. lia.
  assert ((@pair var nat x n) = (@pair Env.key nat x n)) by easy.
  rewrite H8 in *. rewrite eq1 in *.
  rewrite IHn with (size := aenv x) (tenv := tenv) ; try easy.
  rewrite <- H0.
  apply functional_extensionality; intro.
  destruct x0.
  bdestruct (v =? y). subst.
  bdestruct (n0 =? n). subst.
  rewrite put_cus_neq_2 by lia.
  rewrite put_cus_eq by lia.
  unfold bin_xor,cut_n.
  bdestruct (n <? S n).
  rewrite get_cus_cua by lia.
  rewrite get_cus_cua by lia.
  rewrite H8. rewrite eq1. bt_simpl.
  rewrite put_get_cu. easy. apply H6. lia. lia.
  bdestruct (n0 <? n). 
  rewrite put_cus_eq by lia.
  rewrite put_cus_eq by lia.
  unfold bin_xor,cut_n.
  bdestruct (n0 <? n). bdestruct (n0 <? S n). easy. lia.  lia.
  rewrite put_cus_neq_2 by lia.
  rewrite put_cus_neq_2 by lia. easy.
  rewrite put_cus_neq by lia.
  rewrite put_cus_neq by lia. easy. lia. lia.
  apply exp_WF_copy. lia. lia.
  apply exp_fresh_copy. lia.
Qed.

Lemma copyto_sem : forall n x y f aenv tenv, 
            n = aenv x -> n = aenv y -> Env.MapsTo x Nor tenv -> Env.MapsTo y Nor tenv
            -> right_mode_env aenv tenv f ->
            (exp_sem aenv (copyto x y n) f) = put_cus f y (bin_xor (get_cus n f y) (get_cus n f x) n) n.
Proof.
  intros. apply copyto_sem' with (tenv := tenv); try easy.
Qed.

(* Example Circuits that are definable by OQASM. *)
(* find a number that is great-equal than 2^(n-1), assume that the number is less than 2^n *)
Fixpoint findnum' (size:nat) (x:nat) (y:nat) (i:nat) := 
       match size with 0 => i
              | S n => if y <=? x then i else findnum' n (2 * x) y (i+1)
       end.

Definition findnum (x:nat) (n:nat) := findnum' n x (2^(n-1)) 0.

(* Find the index i of a number 2^i that is x <= 2^i *)
Fixpoint findBig2n' (size:nat) (x:nat) (i:nat) :=
   match i with 0 => size
          | S m => if x <=? 2^(size-(S m)) then (size - (S m)) else findBig2n' size x m
   end.
Definition findBig2n (size:nat) (x:nat) := findBig2n' size x size.

Definition div_two_spec (f:nat->bool) := fun i => f (i+1).