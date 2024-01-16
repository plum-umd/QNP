Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import OQASM.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import QafnySyntax.
Require Import LocusDef.
Require Import LocusKind.
Require Import LocusSem.
Require Import LocusType.
(**********************)
(** Unitary Programs **)
(**********************)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Declare Scope pexp_scope.
Delimit Scope pexp_scope with pexp.
Local Open Scope pexp_scope.
Local Open Scope nat_scope.

Inductive env_state_eq : type_map -> qstate ->  Prop :=
    env_state_eq_empty : env_state_eq nil nil
  | env_state_eq_many : forall s t a l1 l2, env_state_eq l1 l2 -> type_state_elem_same t a -> env_state_eq ((s,t)::l1) ((s,a)::l2).

Definition qstate_wt (S : qstate) : Prop := forall s m bl, In (s,Cval m bl) S -> m > 0.


Lemma find_env_state : forall s s' t T S, env_state_eq T S -> @find_env se_type T s (Some (s++s',t))
       -> (exists a, @find_env state_elem S s (Some (s++s',a)) /\ type_state_elem_same t a).
Proof.
  intros.
  remember (Some (s ++ s', t)) as q.
  generalize dependent S.
  induction H0.
  easy. intros. inv Heqq. inv H0. exists a.
  split. apply find_env_many_1. easy. easy.
  intros. inv H1.
  assert (Some (y ++ s', t) = Some (y ++ s', t)) by auto.
  apply IHfind_env with (S0 := l2) in H1. destruct H1 as [a' [X1 X2]].
  exists a'. split. apply find_env_many_2. auto. auto. auto. auto.
Qed.

Lemma env_state_eq_app: forall S a1 a2, env_state_eq (a1++a2) S
      -> exists b1 b2, env_state_eq (a1++a2) (b1++b2) /\ S = b1 ++ b2 /\ length b1 = length a1.
Proof.
  intros. remember (a1++a2) as S1.
  generalize dependent a1.
  generalize dependent a2.
  induction H. intros. symmetry in HeqS1. apply app_eq_nil in HeqS1. inv HeqS1.
  exists nil,nil. split. simpl. constructor. simpl. easy.
  intros. destruct a1. simpl in *. destruct a2. inv HeqS1.
  inv HeqS1.
  specialize (IHenv_state_eq a2 nil).
  simpl in *. assert (a2 = a2) by easy. apply IHenv_state_eq in H1.
  destruct H1 as [b1 [b2 [X1 [X2 X3]]]].
  exists b1. exists ((s,a)::b2).
  rewrite length_zero_iff_nil in X3 ; subst. simpl in *.
  split. constructor. easy. easy. easy.
  inv HeqS1.
  specialize (IHenv_state_eq a2 a1).
  assert (a1 ++ a2 = a1 ++ a2) by easy. apply IHenv_state_eq in H1.
  destruct H1 as [b1 [b2 [X1 [X2 X3]]]].
  exists ((s, a)::b1). exists b2.
  split. simpl. constructor. easy. easy.
  split. simpl. rewrite X2. easy. simpl. rewrite X3. easy.
Qed.

Lemma env_state_eq_same_length: forall a1 a2 b1 b2, length a1 = length b1
        -> env_state_eq (a1++a2) (b1++b2) -> env_state_eq a1 b1 /\ env_state_eq a2 b2.
Proof.
  induction a1;intros;simpl in *.
  symmetry in H. apply length_zero_iff_nil in H as X1; subst. simpl in *.
  split. constructor. easy. destruct b1. simpl in *. easy.
  simpl in *. inv H.
  inv H0.
  destruct (IHa1 a2 b1 b2 H2 H4) as [X1 X2].
  split. constructor; easy. easy.
Qed.

Lemma env_state_eq_app_join: forall a1 a2 b1 b2, env_state_eq a1 b1 -> env_state_eq a2 b2 -> env_state_eq (a1++a2) (b1 ++ b2).
Proof.
  induction a1; intros; simpl in *.
  inv H. simpl. easy.
  inv H. simpl in *. constructor. apply IHa1; easy. easy.
Qed.

Lemma env_state_eq_app_comm: forall a1 a2 b1 b2, length a1 = length b1 -> env_state_eq (a1 ++ a2) (b1++b2) -> env_state_eq (a2 ++ a1) (b2++b1).
Proof.
  intros. remember (a1 ++ a2) as l1. remember (b1 ++ b2) as l2.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent b1.
  generalize dependent b2.
  induction H0. intros.
  symmetry in Heql1. symmetry in Heql2.
  apply app_eq_nil in Heql1. apply app_eq_nil in Heql2. inv Heql1. inv Heql2.
  simpl. constructor.
  intros.
  destruct a1. simpl in *. symmetry in H1. rewrite length_zero_iff_nil in H1; subst. simpl in *.
  destruct b2. inv Heql2. inv Heql2. repeat rewrite app_nil_r. constructor; easy.
  simpl in *. inv Heql1.
  destruct b1. simpl in *. lia. simpl in *. inv Heql2.
  assert (env_state_eq (((s, t) :: a1) ++ a2) (((s, a) :: b1) ++ b2)). simpl.
  apply env_state_eq_many; try easy.
  apply env_state_eq_same_length in H2 as X1; try easy.
  apply env_state_eq_app_join; try easy.
Qed.

Lemma find_env_ch: forall T s s' t, find_env T s (Some (s',t)) -> (exists T', env_equiv T T' /\ find_env T' s (Some (s',CH))).
Proof.
 intros. remember (Some (s',t)) as a. induction H; subst. inv Heqa.
 inv Heqa.
 exists ((s',CH)::S).
 split. apply env_subtype.
 destruct t; constructor.
 constructor. easy.
 assert (Some (s', t) = Some (s', t)) by easy. apply IHfind_env in H1.
 destruct H1 as [T' [X1 X2]].
 exists ((x,v)::T').
 split.
 constructor. easy.
 apply find_env_many_2. easy. easy.
Qed.

Lemma find_type_ch : forall T1 s s' t, find_type T1 s (Some (s',t)) -> find_type T1 s (Some (s',CH)).
Proof.
  intros. inv H.
  specialize (find_env_ch S' s s' t H1) as X1. destruct X1 as [T' [X1 X2]].
  apply find_type_rule with (S := T1) in X2; try easy.
  apply env_equiv_trans with (T2 := S'); easy.
Qed.


Lemma pick_mea_exists {rmax:nat}: forall S l m b x n, @qstate_wt ((((x,BNum 0,BNum n)::l, Cval m b)::S)) ->
          exists r v, @pick_mea n (Cval m b) (r,v).
Proof.
  intros.
  unfold qstate_wt in *.
  specialize (H ((x, BNum 0, BNum n) :: l) m b).
  assert (In ((x, BNum 0, BNum n) :: l, Cval m b)
      (((x, BNum 0, BNum n) :: l, Cval m b) :: S)). simpl in *.
  left. easy. apply H in H0.
  assert (exists i, 0 <= i < m). exists 0. lia. destruct H1.
  remember (b x0) as ra. destruct ra.
  exists (Cmod c). exists (a_nat2fb r n).
  apply pick_meas with (i := x0); try easy.
Qed. 


Axiom mask_state_exists: forall n m bl r v,
             @pick_mea n (Cval m bl) (r,v) ->
          (exists na p, build_state_ch n v (Cval m bl) = Some (Cval na p) /\ na > 0).

Definition kind_env_wf (env:aenv) : Prop :=
  forall x n, AEnv.MapsTo x (QT n) env -> n > 0.

Definition env_wf (env:type_map) : Prop :=
   forall x t, In (x,t) env -> simple_ses x.

Lemma find_env_simple: forall T l l' t, @find_env se_type T l (Some (l',t)) -> simple_tenv T -> simple_ses l'.
Proof.
  intros. remember (Some (l', t)) as a. induction H; subst; try easy.
  inv Heqa. unfold simple_tenv in *.
  apply (H0 l' t). simpl. left. easy.
  apply IHfind_env; try easy.
  unfold simple_tenv in *. intros. apply (H0 a b). simpl in *. right. easy.
Qed.

(*
Lemma find_type_simple: forall T l l' t, find_type T l (Some (l',t)) -> simple_tenv T -> simple_ses l'.
Proof.
  intros. inv H. apply env_equiv_simple_type in H1; try easy. eapply (find_env_simple S' l l' t); try easy.
Qed.
*)

Lemma qstate_wt_app_l: forall s s1, qstate_wt (s++s1) -> qstate_wt s.
Proof.
  intros. unfold qstate_wt in *. intros.
  eapply H. apply in_app_iff. left. apply H0.
Qed.

Lemma qstate_wt_app_r: forall s s1, qstate_wt (s++s1) -> qstate_wt s1.
Proof.
  intros. unfold qstate_wt in *. intros.
  eapply H. apply in_app_iff. right. apply H0.
Qed.

Lemma qstate_wt_app: forall s s1, qstate_wt s -> qstate_wt s1 -> qstate_wt (s++s1).
Proof.
  induction s; intros; simpl in *; try easy.
  unfold qstate_wt. intros. simpl in *. destruct H1; subst.
  eapply H. simpl. left. easy.
  apply IHs in H0.  apply H0 in H1. easy.
  unfold qstate_wt. intros. eapply H. simpl. right. apply H2.
Qed.


Lemma simple_ses_app_l: forall l l', simple_ses (l++l') -> simple_ses l.
Proof.
  intros. induction l; try easy. constructor.
  inv H. constructor; try easy. apply IHl. easy.
Qed.

Lemma simple_ses_app_r: forall l l', simple_ses (l++l') -> simple_ses l'.
Proof.
  intros. induction l; try easy. 
  simpl in *. inv H. apply IHl. easy.
Qed.

Lemma simple_ses_subst: forall s x v, simple_ses s -> (subst_locus s x v) = s.
Proof.
  induction s; intros;simpl in *; try easy.
  inv H. rewrite IHs; try easy.
  unfold subst_range in *.
  unfold simple_bound in *. destruct x0 eqn:eq1. easy.
  destruct y eqn:eq2. easy.
  unfold subst_bound. easy.
Qed.

Lemma simple_env_subst: forall T x v, simple_tenv T -> (subst_type_map T x v) = T.
Proof.
  induction T; intros; simpl in *; try easy.
  unfold simple_tenv in *. intros. destruct a.
  rewrite IHT. simpl in *.
  rewrite simple_ses_subst. easy.
  specialize (H l s). apply H. left. easy.
  intros. eapply H. simpl. right. apply H0.
Qed.

Lemma aenv_find_add {A:Type}: forall k v (m:AEnv.t A),
        AEnv.find k (AEnv.add k v m) = Some v.
Proof.
      intros.
      apply AEnv.find_1.
      apply AEnv.add_1.
      easy.
Qed.

Lemma aenv_mapsto_add1 {A:Type}: forall k v1 v2 (s:AEnv.t A),
        AEnv.MapsTo k v1 (AEnv.add k v2 s) -> v1 = v2.
Proof.
      intros.
      apply AEnv.find_1 in H.
      rewrite aenv_find_add in H.
      inversion H.
      reflexivity.
Qed.

Lemma aenv_mapsto_always_same {A:Type} : forall k v1 v2 (s:AEnv.t A),
           AEnv.MapsTo k v1 s ->
            AEnv.MapsTo k v2 s -> 
                       v1 = v2.
Proof.
     intros.
     apply AEnv.find_1 in H.
     apply AEnv.find_1 in H0.
     rewrite H in H0.
     injection H0.
     easy.
Qed.

Lemma aenv_mapsto_equal {A:Type} : forall k v (s1 s2:AEnv.t A),
           AEnv.Equal s1 s2 -> AEnv.MapsTo k v s1 ->
            AEnv.MapsTo k v s2.
Proof.
     intros.
     specialize (AEnvFacts.Equal_mapsto_iff s1 s2) as X1.
     destruct X1.
     apply H1 with (k := k) (e := v) in H.
     apply H in H0. easy.
Qed.

(*
Lemma kind_env_stack_equal: forall env s1 s2, AEnv.Equal s1 s2 -> kind_env_stack env s1 -> kind_env_stack env s2.
Proof.
  intros. unfold kind_env_stack in *.
  intros. split; intros.
  apply H0 in H1. destruct H1.
  apply aenv_mapsto_equal with (s4 := s2) in H1; try easy.
  exists x0. easy.
  destruct H1.
  apply H0.
  apply AEnvFacts.Equal_sym in H.
  apply aenv_mapsto_equal with (s4 := s1) in H1; try easy.
  exists x0. easy.
Qed.
*)

Lemma type_cbexp_class: forall env b t, type_cbexp env b t -> t = CT.
Proof.
  intros. induction H; try easy.
Qed.

(*We assume a subset of allowed bexp syntax. *)
Axiom eval_bexp_exists : forall aenv n b s l l1 m f, type_bexp aenv b (QT n, l) 
   -> exists f', @eval_bexp ((l++l1, Cval m f)::s) b ((l++l1, Cval m f')::s).

Lemma type_bexp_gt : forall env b n l, type_bexp env b (QT n, l) -> n > 0.
Proof.
  intros. remember (QT n, l) as t. induction H; try easy.
  inv Heqt.
  apply type_cbexp_class in H. inv H. inv Heqt. lia.
  inv Heqt. lia. inv Heqt. lia. inv Heqt. lia. inv Heqt. lia.
  subst. apply IHtype_bexp. easy.
Qed.

Lemma union_f_same: forall t t1 t2 t3, union_f t t1 t2 -> union_f t t1 t3 -> t2 = t3.
Proof.
  intros. generalize dependent t3.
  induction H; intros; subst;try easy.
  inv H0. easy. inv H0. easy.
  inv H0. easy. inv H0. easy. 
Qed.

Lemma type_aexp_only: forall env b t t', type_aexp env b t
         -> type_aexp env b t' -> t = t'.
Proof.
  intros. generalize dependent t'.
  induction H; intros;subst. inv H0. easy.
  apply aenv_mapsto_always_same with (v1 := CT) in H3; try easy; subst.
  inv H0.
  apply aenv_mapsto_always_same with (v1 := QT n) in H3; try easy; subst.
  apply aenv_mapsto_always_same with (v1 := QT n) in H3; try easy; subst.
  inv H3. easy.
  inv H0. easy.
  inv H2.
  apply IHtype_aexp1 in H5.
  apply IHtype_aexp2 in H7. subst.
  apply union_f_same with (t2 := t3) in H9; subst;try easy.
  inv H2.
  apply IHtype_aexp1 in H5.
  apply IHtype_aexp2 in H7. subst.
  apply union_f_same with (t2 := t3) in H9; subst;try easy.
Qed.

Lemma type_cbexp_only: forall env b t t', type_cbexp env b t
         -> type_cbexp env b t' -> t = t'.
Proof.
  intros. induction H. inv H0.
  apply type_aexp_only with (t := (CT, l0)) in H; subst; try easy.
  inv H0.
  apply type_aexp_only with (t := (CT, l0)) in H; subst; try easy.
Qed.

Lemma type_bexp_only: forall env b t t', type_bexp env b t
         -> type_bexp env b t' -> t = t'.
Proof.
  intros. induction H. inv H0.
  apply type_cbexp_only with (t := t0) in H; subst; try easy.
  inv H0.
  apply aenv_mapsto_always_same 
      with (v1 := (QT m0)) in H; try easy; subst.
  apply aenv_mapsto_always_same 
      with (v1 := (QT n0)) in H1; try easy; subst.
  inv H. inv H1. easy.
  inv H0.
  apply aenv_mapsto_always_same 
      with (v1 := (QT m0)) in H; try easy; subst.
  apply aenv_mapsto_always_same 
      with (v1 := (QT n0)) in H1; try easy; subst.
  inv H. inv H1. easy.
  inv H0.
  apply aenv_mapsto_always_same 
      with (v1 := (QT m0)) in H; try easy; subst.
  apply aenv_mapsto_always_same 
      with (v1 := (QT n0)) in H1; try easy; subst.
  inv H. inv H1. easy.
  inv H0.
  apply aenv_mapsto_always_same 
      with (v1 := (QT m0)) in H; try easy; subst.
  apply aenv_mapsto_always_same 
      with (v1 := (QT n0)) in H1; try easy; subst.
  inv H. inv H1. easy.
  inv H0. easy.
  inv H0.
  apply IHtype_bexp. easy.
Qed.

Axiom fun_all_equal : forall (f c: rz_val), f = c \/ f <> c.

Lemma find_basis_elems_exists: forall n n' f fc i, exists m acc, find_basis_elems n n' f fc i m acc.
Proof.
  induction i;intros;simpl in *.
  exists 0, (fun _ => (C0,allfalse)). apply find_basis_empty.
  destruct IHi as [m [acc H]].
  assert (f = cut_n (lshift_fun (snd (fc i)) n') n \/ f <> cut_n (lshift_fun (snd (fc i)) n') n) by apply classic.
  destruct H0.
  exists (S m),(update acc m (fc i)). constructor; try easy.
  exists m,acc. constructor; try easy.
Qed.

Lemma assem_bool_exists: forall n n' i m f fc, exists mv fv, assem_bool n n' i f (Cval m fc) (Cval mv fv).
Proof.
  induction i;intros;simpl in *.
  exists 0, (fun _ => (C0,allfalse)). apply assem_bool_empty.
  destruct (IHi m f fc) as [m' [acc H]].
  destruct (find_basis_elems_exists n n' (cut_n (snd (f i)) n) fc m) as [mv [fv H1]].
  destruct mv.
  exists (S m'), ((update acc m' (f i))).
  eapply assem_bool_many_1; try easy. apply H1.
  destruct (assem_list (S mv) m' n (cut_n (snd (f i)) n) fv acc) eqn:eq1.
  exists n0,p.
  eapply assem_bool_many_2 with (mv := (S mv)); try easy. apply H. lia. apply H1. easy.
Qed.

Lemma simple_subst_ses: forall s i l, simple_ses (subst_locus s i l) -> (forall v, simple_ses (subst_locus s i v)).
Proof.
  intros.
  induction s. simpl in *. easy.
  simpl in *. inv H.
  unfold subst_range in *. destruct a. destruct p. inv H0.
  constructor.
  unfold simple_bound in *.
  unfold subst_bound in *.
  destruct b0. bdestruct (i =? v1); easy. easy.
  unfold simple_bound,subst_bound in *.
  destruct b. bdestruct (i =? v1); easy. easy.
  apply IHs. easy.
Qed.

Lemma simple_tenv_subst_right: forall T i l,
  simple_tenv (subst_type_map T i l) -> (forall v, simple_tenv (subst_type_map T i v)).
Proof.
  intros. unfold simple_tenv in *.
  intros. induction T; simpl in *. easy.
  destruct a0. simpl in *. destruct H0. inv H0.
  specialize (H (subst_locus l0 i l) b). 
  assert ((subst_locus l0 i l, b) = (subst_locus l0 i l, b) \/
    In (subst_locus l0 i l, b) (subst_type_map T i l)). left. easy.
  apply H in H0. eapply simple_subst_ses. apply H0.
  apply IHT. intros. apply H with (b := b0). right. easy.
  easy.
Qed.


Lemma simple_tenv_app_l: forall T T1, simple_tenv (T++T1) -> simple_tenv T.
Proof.
  intros. unfold simple_tenv in *; intros. eapply H.
  apply in_app_iff. left. apply H0.
Qed.

Lemma simple_tenv_app_r: forall T T1, simple_tenv (T++T1) -> simple_tenv T1.
Proof.
  intros. unfold simple_tenv in *; intros. eapply H.
  apply in_app_iff. right. apply H0.
Qed.

Lemma simple_tenv_app: forall T T1, simple_tenv T -> simple_tenv T1 -> simple_tenv (T++T1).
Proof.
  intros. unfold simple_tenv in *; intros.
  apply in_app_iff in H1. destruct H1. eapply H. apply H1.
  eapply H0. apply H1.
Qed.

Lemma bexp_extend: forall aenv b n l l1 v v' s sa, type_bexp aenv b (QT n, l) ->
      eval_bexp ((l ++ l1, v) :: s) b ((l ++ l1, v') :: s) ->
      eval_bexp ((l ++ l1, v) :: s++sa) b ((l ++ l1, v') :: s++sa).
Proof.
  intros. remember ((l ++ l1, v) :: s) as S1. remember ((l ++ l1, v') :: s) as S2.
  induction H0; simpl in *; subst; try easy. inv HeqS1. inv HeqS2.
  apply beq_sem_1. easy.
  inv HeqS1. inv HeqS2.
  apply beq_sem_2. easy.
  inv HeqS1. inv HeqS2.
  apply blt_sem_1. easy.
  inv HeqS1. inv HeqS2.
  apply blt_sem_2. easy.
Qed.

Lemma bexp_extend_1: forall aenv b n l l1 v v' s, type_bexp aenv b (QT n, l) ->
      eval_bexp ((l ++ l1, v) :: s) b ((l ++ l1, v') :: s) ->
      eval_bexp ((l ++ l1, v) :: nil) b ((l ++ l1, v') :: nil).
Proof.
  intros. remember ((l ++ l1, v) :: s) as S1. remember ((l ++ l1, v') :: s) as S2.
  induction H0; simpl in *; subst; try easy. inv HeqS1. inv HeqS2.
  apply beq_sem_1. easy.
  inv HeqS1. inv HeqS2.
  apply beq_sem_2. easy.
  inv HeqS1. inv HeqS2.
  apply blt_sem_1. easy.
  inv HeqS1. inv HeqS2.
  apply blt_sem_2. easy.
Qed.

(*
Lemma qfor_sem_local: forall rmax aenv s e s' s1,
   @qfor_sem rmax aenv s e s' -> @qfor_sem rmax aenv (fst s, (snd s)++s1) e (fst s', (snd s')++s1).
Proof.
  intros. induction H using qfor_sem_ind'; simpl in *; try easy.
  constructor. apply let_sem_c with (n0 := n); try easy.
  destruct s; simpl in *.
  replace (s, s' ++ s1) with (fst ((s, q ++ s1)), s' ++ s1) by easy.
  apply let_sem_m with (W0 := W) (n0 := n); try easy.
  apply let_sem_q with (W'0 := W') (r0 := r) (v0 := v) (va'0 := va'); try easy.
  constructor. easy.
  constructor. easy.
  constructor; easy.
  constructor; easy.
  constructor; easy.
  apply if_sem_cf. easy.
  apply (if_sem_q aenv W W' l l1 n n' (s++s1) (s'++s1) b e m f f' fc fc' fc''); try easy.
  apply bexp_extend with (aenv := aenv) (n := n); try easy.
  apply seq_sem with (s4 := (fst s0, snd s0 ++ s1)); try easy.
  apply for_sem.
  remember (h-l) as n. clear Heqn. clear H.
  generalize dependent s'.
  induction n; intros; simpl in *; try easy.
  inv H0.
  apply ForallA_nil.
  inv H0. apply IHn in H1.
  apply ForallA_cons with (s' := (fst s'0, snd s'0 ++ s1)); try easy.
Qed.

Lemma simple_tenv_ses_system: forall rmax t aenv T e T',
  simple_tenv T -> @locus_system rmax t aenv T e T' -> simple_tenv T'.
Proof.
  intros. induction H0; simpl in *; try easy.
  apply simple_tenv_app_l in H as X1.
  apply simple_tenv_app_r in H as X2.
  apply simple_tenv_app; try easy. apply IHlocus_system. easy.
  apply IHlocus_system. rewrite simple_env_subst; try easy.
  apply IHlocus_system; try easy.
  apply IHlocus_system. unfold simple_tenv in *.
  intros. simpl in *. destruct H3. inv H3.
  specialize (H ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
    In ((y, BNum 0, BNum n) :: a, CH) T ). left. easy.
  apply H in H3. inv H3. easy. eapply H. right. apply H3.
  unfold simple_tenv in *. intros. simpl in *. destruct H2; try easy.
  inv H2. eapply H. left. easy.
  unfold simple_tenv in *. intros. simpl in *. destruct H2; try easy.
  inv H2. eapply H. left. easy.
  apply IHlocus_system; try easy.
  apply IHlocus_system2; try easy.
  apply IHlocus_system1; try easy.
  apply simple_tenv_subst_right with (v := h) in H. easy.
Qed.
*)

Lemma type_progress : 
    forall e rmax t aenv s tenv tenv', @env_state_eq tenv s ->
      @locus_system rmax t aenv tenv e tenv' -> freeVarsNotCPExp aenv e
       -> @qstate_wt s -> simple_tenv tenv ->
          simple_tenv tenv' /\
          (exists s' r e', @step rmax aenv s e r s' e'
             /\ @qstate_wt s').
Proof.
  intros.
  generalize dependent s.
  induction H0; simpl in *; intros.
 - apply env_state_eq_app in H as X1; try easy.
  destruct X1 as [s1 [s2 [X1 [X2 X3]]]].
  subst. apply env_state_eq_same_length in X1; try easy.
  destruct X1. apply simple_tenv_app_l in H3 as X1.
  apply qstate_wt_app_l in H3 as X2.
  destruct (IHlocus_system H2 X1 (s0,s1) H5 H0 X2) as [Y1 [sa [Y2 [Y3 [Y4 Y5]]]]].
  split. apply simple_tenv_app; try easy.
  apply simple_tenv_app_r in H4; try easy.
  destruct sa; simpl in *. exists (s3,q0++s2). split.
  apply qfor_sem_local with (s1 := s2) in Y2; try easy.
  split; try easy. split. simpl. apply qstate_wt_app; try easy.
  apply qstate_wt_app_r in H3. easy. apply env_state_eq_app_join; try easy.
 - 
  split. easy.
  exists s; try easy. split. constructor. easy.
 - 
  apply freeVars_pexp_in with (v := v) in H2 as X1; try easy.
  rewrite simple_env_subst in *; try easy.
  specialize (IHlocus_system X1 H4 s H3 H5 H6).
  destruct IHlocus_system. split. easy.
  destruct H8 as [s' [X4 [X5 X6]]].
  exists s'.
  split. apply let_sem_c with (n := v); try easy. easy.
 - 
  apply kind_env_stack_exist with (s := fst s) in H as X1; try easy.
  destruct X1.
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x1 =? x); subst.
  apply aenv_mapsto_add1 in H9. inv H9. easy.
  apply AEnv.add_3 in H9; try lia.
  apply H2 with (x0 := x1). simpl.
  apply in_app_iff. right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  specialize (IHlocus_system H8 H4 (update_cval s x x0)).
  unfold update_cval in IHlocus_system;simpl in *.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x x0 (fst s))).
  unfold kind_env_stack. intros. split. intros.
  bdestruct (x1 =? x); subst.
  exists x0. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H9; try easy.
  unfold AEnv.In,AEnv.Raw.PX.In in *.
  apply H5 in H9. destruct H9. exists x2. apply AEnv.add_2. lia. easy. lia.
  intros.
  bdestruct (x1 =? x); subst.
  apply AEnv.add_1. easy.
  destruct H9.
  apply AEnv.add_3 in H9; try easy.
  assert (AEnv.In x1 (fst s)). exists x2. easy. apply H5 in H11.
  apply AEnv.add_2. lia. easy. lia.
  destruct s. simpl in *.
  specialize (IHlocus_system H3 H9 H6).
  destruct IHlocus_system as [X2 [s' [X3 [X4 X5]]]].
  split. easy.
  exists (s, snd s').
  split. apply let_sem_m with (n := x0) (W := fst s'); try easy.
  destruct s'; try easy.
  split. simpl in *. easy. split; try easy.
  unfold freeVarsNotCAExp, freeVarsNotCPExp in *.
  intros. simpl in *. apply H2 with (x0 := x0); try easy.
  apply in_app_iff. left. easy.
 -
  destruct s. simpl in *. inv H3. inv H12. 
  destruct (@pick_mea_exists rmax l2 (l) m bl y n H6) as [ra [va X1]].
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H7. inv H7. easy.
  apply AEnv.add_3 in H7; try lia.
  apply H2 with (x0 := x0). simpl.
  right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  apply mask_state_exists in X1 as eq1.
  destruct eq1 as [na [p [X2 X3]]].
  assert (simple_tenv ((l, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H7. inv H7.
  specialize (H4 ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
     In ((y, BNum 0, BNum n) :: a, CH) T). left. easy.
  apply H4 in H7.
  inv H7. easy. apply H4 with (b:= b). right. easy.
  specialize (IHlocus_system H3 H7 (AEnv.add x (ra,va) s,(l,(Cval na p))::l2)); simpl in *.
  assert (env_state_eq ((l, CH) :: T) ((l, Cval na p) :: l2)).
  constructor. easy. constructor.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x (ra, va) s)).
  unfold kind_env_stack in *. intros. split; intros.
  bdestruct (x0 =? x); subst.
  exists (ra, va). apply AEnv.add_1. easy.
  apply AEnv.add_3 in H9; try lia.
  apply H5 in H9. destruct H9.
  exists x1. apply AEnv.add_2; try lia. easy.
  bdestruct (x0 =? x); subst. apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia. apply H5. destruct H9. apply AEnv.add_3 in H9; try lia.
  exists x1. easy.
  assert (@qstate_wt ((l, Cval na p) :: l2)).
  unfold qstate_wt in *. intros.
  simpl in *. destruct H10. inv H10. lia.
  apply H6 with (s := s0) (bl0 := bl0). right. easy.
  destruct (IHlocus_system H8 H9 H10) as [Y1 [sa [Y2 [Y3 Y4]]]].
  split. easy.
  exists (s,(snd sa)).
  split. apply let_sem_q with (r := ra) (v := va) (va' := (Cval na p))
        (W' := fst sa); simpl in *; try easy.
  destruct sa. easy. simpl.
  split; try easy.
 -
  destruct s; simpl in *.
  inv H1. inv H11. inv H10.
  split. unfold simple_tenv in *.
  intros. simpl in *. destruct H1; try easy. inv H1.
  specialize (H4 a TNor). apply H4. left. easy.
  assert (simple_ses (l)).
  unfold simple_tenv in *. intros.
  eapply H4. simpl. left. easy.
  destruct (@eval_nor_exists rmax env l n p r e H H1 H0) as [ba X2]. destruct ba.
  exists (s, (l, Nval c r0) :: nil).
  split. apply appu_sem_nor; try easy.
  split. easy.
  split. simpl.
  unfold qstate_wt in *.
  intros. simpl in *. destruct H6; try easy.
  constructor; try easy. constructor. constructor.
 -
  destruct s; simpl in *.
  inv H1. inv H11. inv H10.
  split. unfold simple_tenv in *.
  intros. simpl in *. destruct H1; try easy. inv H1.
  specialize (H4 (l ++ l') CH). apply H4. left. easy.
  assert (simple_ses (l++l')).
  unfold simple_tenv in *. intros.
  specialize (H4 (l++l') CH). apply H4. simpl. left. easy.
  apply simple_ses_app_l in H1 as X1.
  Check eval_ch_exists.
  destruct (@eval_ch_exists rmax m env l n bl e H X1 H0) as [ba X2].
  exists (s, (l ++ l', Cval m ba) :: nil).
  split. apply appu_sem_ch; try easy. split. easy.
  split.
  unfold qstate_wt in *.
  intros. simpl in *. destruct H6; try easy. inv H6.
  specialize (H5 (l++l') m0 bl).
  assert ((l ++ l', Cval m0 bl) = (l ++ l', Cval m0 bl) \/ False). left. easy.
  apply H5 in H6. easy.
  constructor; try easy. constructor. constructor.
 - 
  split. unfold simple_tenv in *. intros.
  simpl in *. destruct H6; try easy. inv H6. specialize (H4 ([a]) TNor). apply H4. left. easy.
  destruct s; simpl in *. inv H1.
  inv H11. inv H10.
  assert (simple_ses ([a])) as X1.
  unfold simple_tenv in *. specialize (H4 ([a]) TNor). assert (In ([a], TNor) [([a], TNor)]).
  simpl. left. easy.
  apply H4 in H1. easy.
  apply ses_len_simple in X1 as X2. destruct X2 as [x X2].
  exists (s,([a],(Hval (eval_to_had x r)) )::nil).
  split. apply appsu_sem_h_nor; try easy.
  split.
  easy.
  split.
  simpl in *. unfold qstate_wt in *.
  intros. inv H1; try easy.
  constructor; try easy. constructor. constructor.
 -
  split. unfold simple_tenv in *. intros.
  simpl in *. destruct H6; try easy. inv H6. specialize (H4 ([a]) THad). apply H4. left. easy.
  destruct s; simpl in *. inv H1.
  inv H11. inv H10.
  assert (simple_ses ([a])) as X1.
  unfold simple_tenv in *. specialize (H4 ([a]) THad). assert (In ([a], THad) (([a], THad) :: nil)).
  simpl. left. easy.
  apply H4 in H1. easy. apply ses_len_simple in X1 as X2. destruct X2 as [x X2].
  exists (s,([a],(Nval C1 (eval_to_nor x bl)))::nil).
  split. apply appsu_sem_h_had; try easy.
  split. easy. split.
  simpl in *. unfold qstate_wt in *.
  intros. inv H1; try easy.
  constructor; try easy. constructor. constructor.
 -
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *; simpl in *.
  intros. apply H2 with (x := x); try easy.
  apply in_app_iff. right. easy.
  destruct (IHlocus_system H7 H4 s H3 H5 H6) as [X1 [sa [X2 [X3 X4]]]].
  split. easy.
  exists sa. split. apply if_sem_ct; try easy.
  split. easy. split. easy. easy.
 -
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *; simpl in *.
  intros. apply H2 with (x := x); try easy.
  apply in_app_iff. right. easy.
  split. easy.
  exists s. split. apply if_sem_cf; try easy.
  split. easy.
  split. easy. easy.
 -
  destruct s; simpl in *. inv H0. inv H11. inv H10.
  apply eval_bexp_exists with (s := nil) (l1 := l1) (m := m) (f := bl) in H as X1.
  destruct X1 as [f' X1].
  apply find_env_simple with (l := l++l1) (l' := l++l1) (t := CH) in H4 as X2.
  apply simple_ses_app_r in X2 as X3.
  apply ses_len_simple in X3 as X4. destruct X4 as [n' X4].
  specialize (fch_mut_state 0 n n' (fst (grab_bool f' m n)) (snd (grab_bool f' m n))) as X5.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros; simpl in *.
  eapply H2. apply in_app_iff. right. apply H0. easy.
  assert (simple_tenv ((l1, CH) :: nil)).
  unfold simple_tenv in *. intros. simpl in *. destruct H6; try easy. inv H6.
  apply simple_ses_app_r in X2. easy.
  specialize (IHlocus_system H0 H6 
   (s,(l1,(Cval (fst (grab_bool f' m n)) (mut_fch_state 0 n n' (snd (grab_bool f' m n)))))::nil)).
  simpl in *.
  assert (env_state_eq ((l1, CH) :: nil)
                     ((l1,
                      Cval (fst (grab_bool f' m n))
                        (mut_fch_state 0 n n' (snd (grab_bool f' m n)))) :: nil)).
  constructor. constructor. constructor.
  assert (qstate_wt
                     ((l1,
                      Cval (fst (grab_bool f' m n))
                        (mut_fch_state 0 n n' (snd (grab_bool f' m n)))) :: nil)).
  unfold qstate_wt in *.
  intros. simpl in *. destruct H8. inv H8.
  apply grab_bool_gt. apply H5 with (s := l++s0) (bl0 := bl). left. easy.
  apply type_bexp_gt in H. easy.
  apply H5 with (s := s0) (bl0 := bl0). right. easy.
  destruct (IHlocus_system H7 H3 H8) as [X7 [sa [X8 [X9 [X10 X11]]]]].
  destruct sa; simpl in *. inv X11. inv H13. inv H14.
  split. easy.
  destruct (assem_bool_exists n n' m m0 f' bl0) as [mv [fv X12]].
  exists (s0, (l++l1, Cval mv fv)::nil).
  split. eapply if_sem_q; try easy. apply H. apply X1. apply X4. apply X5.
  apply X8. apply X12. split. easy.
  split.
  unfold qstate_wt in *. intros; simpl in *.
  destruct H9; try easy. inv H9.
  specialize (H5 (l++l1) m bl).
  assert ((l ++ l1, Cval m bl) = (l ++ l1, Cval m bl) \/ False).
  left. easy. apply H5 in H9.
  specialize (X10 l1 m0 bl0).
  assert ((l1, Cval m0 bl0) = (l1, Cval m0 bl0) \/ False).
  left. easy. apply X10 in H10.
  apply assem_bool_gt in X12 as X13; try easy. lia.
  constructor. constructor. constructor.
  constructor. apply ses_sub_prop with (b' := nil).
  rewrite app_nil_r. apply ses_eq_id.
- 
  assert (freeVarsNotCPExp env e1).
  unfold freeVarsNotCPExp in *. intros; simpl in *.
  eapply H2. apply in_app_iff. left. apply H1.
  easy.
  assert (freeVarsNotCPExp env e2).
  unfold freeVarsNotCPExp in *. intros; simpl in *.
  eapply H2. apply in_app_iff. right. apply H5.
  easy.
  destruct (IHlocus_system1 H1 H4 s H H0 H3) as [X1 [s' [X2 [X3 [X4 X5]]]]].
  apply kind_env_stack_equal with (s2 := (fst s')) in H0; try easy.
  destruct (IHlocus_system2 H5 X1 s' X5 H0 X4) as [Y1 [s'' [Y2 [Y3 [Y4 Y5]]]]].
  split. easy.
  exists s''. split. apply seq_sem with (s1 := s'); try easy.
  split; try easy. apply AEnvFacts.Equal_trans with (m' := fst s'); try easy.
- split. easy.
  exists s.
  split. constructor. assert (h-l = 0) by lia. rewrite H5 in *. constructor.
  split. easy. split. easy. easy.
- split. eapply simple_tenv_subst_right. apply H4.
  remember (h-l) as na.
  assert (h=l+na) by lia. rewrite H8 in *. clear H8. clear h.
  assert (exists s' : state,
          ForallA rmax (@qfor_sem) na env s l i b e s' /\
          AEnv.Equal (fst s) (fst s') /\
          qstate_wt (snd s') /\ env_state_eq (subst_type_map T i (l+na)) (snd s')).
  assert (forall v, freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v))) as Y1.
  intros.
  unfold freeVarsNotCPExp in *.
  intros;simpl in *. apply H2 with (x := x); try easy.
  bdestruct (x =? i); subst. assert (AEnv.In i env). exists (Mo t). easy.
  easy.
  apply in_app_iff in H8. destruct H8.
  apply freeVarsBExp_subst in H8.
  apply in_app_iff. left. apply list_sub_not_in; easy.
  apply in_app_iff. right. apply freeVarsPExp_subst in H8.
  apply list_sub_not_in; try easy. 
  clear H. clear H2. clear Heqna.
  induction na;intros;simpl in *.
  exists s. split. constructor. split. easy. split. easy.
  replace (l+0) with l by lia. easy.
  assert (forall v : nat,
        l <= v < l + na ->
        @locus_system rmax q env (subst_type_map T i v) (If (subst_bexp b i v) (subst_pexp e i v))
          (subst_type_map T i (v + 1))).
  intros. apply H1. lia.
  assert ((forall v : nat,
        l <= v < l + na ->
        freeVarsNotCPExp env
          (If (subst_bexp b i v) (subst_pexp e i v)) ->
        simple_tenv (subst_type_map T i v) ->
        forall s : stack * qstate,
        env_state_eq (subst_type_map T i v) (snd s) ->
        kind_env_stack env (fst s) ->
        qstate_wt (snd s) ->
        simple_tenv (subst_type_map T i (v + 1)) /\
        (exists s' : state,
           @qfor_sem rmax env s (If (subst_bexp b i v) (subst_pexp e i v))
             s' /\
           AEnv.Equal (fst s) (fst s') /\
           qstate_wt (snd s') /\
           env_state_eq (subst_type_map T i (v + 1)) (snd s')))).
  intros. apply H3; try lia; try easy.
  destruct (IHna H H2) as [sa [X1 [X2 [X3 X4]]]].
  assert (l <= l+ na < l + S na) by lia.
  specialize (Y1 (l+na)).
  apply simple_tenv_subst_right with (v := (l+na)) in H4 as Y2.
  apply kind_env_stack_equal with (env := env) in X2 as X5; try easy.
  destruct (H3 (l+na) H8 Y1 Y2 sa X4 X5 X3) as [Y3 [sb [Y4 [Y5 [Y6 Y7]]]]].
  exists sb. split. apply ForallA_cons with (s' := sa); try easy.
  split.
  apply AEnvFacts.Equal_trans with (m' := fst sa); try easy.
  split. easy.
  replace ((l + na + 1)) with (l + S na) in * by lia. easy.
  destruct H8 as [sa [Y1 [Y2 [Y3 Y4]]]].
  exists sa. split. constructor.
  replace (l + na - l) with na by lia. easy. 
  easy.
Qed.

Lemma simp_aexp_no_eval: forall s a v, eval_aexp s a v -> simp_aexp a = None.
Proof.
 intros. induction H; simpl in *; try easy.
 rewrite IHeval_aexp. easy.
 rewrite H0. rewrite IHeval_aexp. easy.
 rewrite IHeval_aexp. easy.
 rewrite H0. rewrite IHeval_aexp. easy.
Qed.

Lemma type_aexp_mo_no_simp: forall env a, type_aexp env a (Mo MT,nil) -> simp_aexp a = None.
Proof.
  intros. remember (Mo MT, []) as t. induction H; subst;simpl in *; try easy.
  inv H1; try easy.
  rewrite IHtype_aexp2; try easy. destruct (simp_aexp e1); try easy.
  rewrite IHtype_aexp1; try easy.
  inv H1; try easy.
  rewrite IHtype_aexp2; try easy. destruct (simp_aexp e1); try easy.
  rewrite IHtype_aexp1; try easy.
Qed.

Lemma type_cbexp_no_qtype: forall env b n t, type_cbexp env b t -> t <> QT n.
Proof.
  intros. induction H; try easy.
  unfold is_class_type in *. destruct t1; try easy.
  destruct t2; try easy.
  unfold is_class_type in *. destruct t1; try easy.
  destruct t2; try easy.
Qed.

Lemma simp_bexp_no_qtype: forall env b n l, 
        type_bexp env b (QT n,l) -> simp_bexp b = None.
Proof.
 intros. remember (QT n, l) as t. induction H; simpl in *; try easy.
 apply type_cbexp_no_qtype with (n := n) in H. inv Heqt. easy.
 apply IHtype_bexp in Heqt. rewrite Heqt. easy.
Qed.

Lemma type_sem_local: forall e rmax q env T T' W s1 s2 s, simple_tenv T ->
   env_state_eq T s1 -> @locus_system rmax q env T e T' ->
      @qfor_sem rmax env (W, s1 ++ s2) e s -> 
            (exists s1', snd s = s1' ++ s2 /\ 
           @qfor_sem rmax env (W, s1) e (fst s, s1') /\ env_state_eq T' s1').
Proof.
  intros. generalize dependent s1. generalize dependent s2. generalize dependent s.
  generalize dependent W.
  induction H1; intros;simpl in *; subst; try easy.
- apply env_state_eq_app in H0 as X1; try easy.
  destruct X1 as [sa [sb [X1 [X2 X3]]]].
  destruct s0; simpl in * ; subst. apply env_state_eq_same_length in X1; try easy.
  destruct X1. apply simple_tenv_app_l in H as X1.
  rewrite <- app_assoc in *.
  destruct (IHlocus_system X1 W (s0,q0) (sb++s2) sa H3 H2) as [sc [Y1 [Y2 Y3]]]; simpl in *; subst.
  exists (sc++sb). rewrite app_assoc. split; try easy.
  split.
  apply qfor_sem_local with (s1 := sb) in Y2; try easy.
  apply env_state_eq_app_join; try easy.
- inv H2. inv H0. exists nil. simpl. split; try easy. split. constructor. constructor.
- inv H4. rewrite H1 in H11. inv H11. rewrite simple_env_subst in *; try easy.
  apply IHlocus_system in H12; try easy.
  destruct H12 as [sa [X1 [X2 X3]]]. exists sa. split. easy.
  split. apply let_sem_c with (n0 := n); try easy. easy.
  apply simp_aexp_no_eval in H11. rewrite H11 in *. easy.
- inv H4. apply type_aexp_mo_no_simp in H0. rewrite H0 in *; try easy.
  unfold update_cval in *. simpl in *.
  apply IHlocus_system in H12; try easy.
  destruct H12 as [sa [X1 [X2 X3]]]; simpl in *.
  exists sa. split; try easy. split. apply let_sem_m with (W1 := W0) (n0 := n); try easy.
  easy.
- inv H4. inv H3. simpl in *. inv H6.
  assert (simple_tenv ((l, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H3. inv H3.
  specialize (H ((y, BNum 0, BNum n) :: a0) CH).
  assert (((y, BNum 0, BNum n) :: a0, CH) = ((y, BNum 0, BNum n) :: a0, CH) \/
    In ((y, BNum 0, BNum n) :: a0, CH) T). left. easy.
  apply H in H3.
  inv H3. easy. apply H with (b:= b). right. easy.
  assert (env_state_eq ((l, CH) :: T) ((l, va') :: l2)).
  constructor; try easy.
  unfold build_state_ch in *. destruct a; try easy.
  destruct (build_state_pars m n v (to_sum_c m n v b) b) eqn:eq1; try easy. inv H14. constructor.
  destruct (IHlocus_system H3 (AEnv.add x (r, v) W)
     (W', s') s2 ((l, va') :: l2) H4 H15) as [sa [X1 [X2 X3]]].
  simpl in *; subst.
  exists sa. split; try easy.
  split. apply let_sem_q with (W'0 := W') (r0 := r) (v0 := v) (va'0 := va'); try easy.
  easy.
- inv H2. inv H8. inv H9. inv H3.
  simpl in *. exists ([(l, Nval ra ba)]); simpl in *. split. easy.
  split; try constructor; try easy. constructor. constructor.
- inv H2. inv H8. inv H9. inv H3.
  simpl in *. exists ([(l ++ l0, Cval m ba)]); simpl in *. split. easy.
  split; try constructor; try easy. constructor. constructor.
- inv H2. inv H8. inv H9. inv H3.
  exists ([([a], Hval (eval_to_had n r))]); simpl in *.
  split; try easy. split; try constructor; try easy.
  constructor. constructor.
- inv H2. inv H8. inv H9. inv H3.
  exists ([([a], Nval C1 (eval_to_nor n bl))]); simpl in *.
  split; try easy. split; try constructor; try easy.
  constructor. constructor.
- inv H4. apply IHlocus_system in H11; try easy.
  destruct H11 as [sa [X1 [X2 X3]]].
  destruct s; simpl in *; subst. exists sa.
  split; try easy. split; try constructor; try easy.
  rewrite H1 in H10. easy.
  apply type_bexp_only with (t := (QT n, l)) in H0; subst; try easy.
- inv H3. rewrite H1 in H8. easy.
  exists s1. split; try easy.
  split. apply if_sem_cf. easy. easy.
  apply type_bexp_only with (t := (QT n, l)) in H0; subst; try easy.
- inv H2.  inv H8. inv H9. inv H3.
  apply simp_bexp_no_qtype in H0. rewrite H0 in *. easy.
  apply simp_bexp_no_qtype in H0. rewrite H0 in *. easy.
  assert (simple_tenv ((l1, CH) :: nil)).
  unfold simple_tenv in *. intros. simpl in *; try easy. destruct H2; try easy.
  inv H2.
  specialize (H (l ++ a) CH).
  assert ((l ++ a, CH) = (l ++ a, CH) \/ False).
  left. easy. apply H in H2.
  apply simple_ses_app_r in H2. easy.
  apply type_bexp_only with (t := (QT n0, l0)) in H0; try easy.
  inv H0. apply app_inv_head_iff in H4; subst.
  specialize (IHlocus_system H2 W (W', (l1, fc') :: s') s2 ([(l1, fc)])); simpl in *.
  assert (env_state_eq ((l1, CH) :: nil) ((l1, fc) :: nil)).
  constructor; try easy. constructor.
  inv H15. constructor.
  simpl in *.
  destruct (IHlocus_system H0 H16) as [sa [X1 [X2 X3]]].
  inv X3. inv H7. inv H8. simpl in *. inv X1.
  exists ([(l ++ l1, fc'')]); simpl in *.
  split. easy.
  split. apply (if_sem_q env W W' l l1 n n' nil nil b e m bl f' fc (Cval m0 bl0) fc''); try easy.
  apply bexp_extend_1 with (aenv := env) (n := n) (s := s2); try easy.
  constructor. constructor.
  inv H17; try constructor.
- apply simple_tenv_ses_system in H1_ as X1; try easy. inv H2.
  apply IHlocus_system1 in H6; try easy.
  destruct H6 as [sa [Y1 [Y2 Y3]]]. destruct s3 in *; simpl in *; subst.
  apply IHlocus_system2 in H8; try easy.
  destruct H8 as [sb [Y4 [Y5 Y6]]]. destruct s in *; simpl in *; subst.
  exists sb. split; try easy.
  split; try easy.
  apply seq_sem with (s4 := (s0,sa)); try easy.
- inv H2. assert (h-l = 0) by lia. rewrite H2 in *. inv H11.
  exists s1. split; try easy. split; try easy.
  simpl in *. constructor. rewrite H2. constructor.
- inv H5.
  remember (h-l) as na.
  assert (h=l+na) by lia. rewrite H5 in *. clear H5. clear h.
  clear H0. clear Heqna.
  generalize dependent s.
  induction na;intros;simpl in *.
  inv H14.
  replace (l+0) with l by lia.
  exists s1. split; try easy. split. constructor.
  replace (l-l) with 0 by lia. constructor. easy.
  inv H14.
  assert (forall v : nat,
        l <= v < l + na ->
        @locus_system rmax q env (subst_type_map T i v)
          (If (subst_bexp b i v) (subst_pexp e i v))
          (subst_type_map T i (v + 1))).
  intros. apply H2. lia.
  assert ((forall v : nat,
        l <= v < l + na ->
        simple_tenv (subst_type_map T i v) ->
        forall (W : stack) (s : state) (s2 : list (locus * state_elem))
          (s1 : qstate),
        env_state_eq (subst_type_map T i v) s1 ->
        @qfor_sem rmax env (W, s1 ++ s2) (If (subst_bexp b i v) (subst_pexp e i v))
          s ->
        exists s1' : list (locus * state_elem),
          snd s = s1' ++ s2 /\
          @qfor_sem rmax env (W, s1) (If (subst_bexp b i v) (subst_pexp e i v))
            (fst s, s1') /\ env_state_eq (subst_type_map T i (v + 1)) s1')).
  intros. apply H3; try lia; try easy.
  destruct (IHna H0 H7 s' H5) as [sa [X1 [X2 X3]]].
  assert (l <= l+ na < l + S na) by lia.
  apply simple_tenv_subst_right with (v := (l+na)) in H as Y2.
  destruct s'; simpl in *; subst.
  destruct (H3 (l + na) H8 Y2 s0 s s2 sa X3 H6) as [sb [X4 [X5 X6]]].
  exists sb. split; try easy.
  split. constructor.
  replace ((l + S na - l)) with (S na) by lia.
  apply ForallA_cons with (s' := (s0, sa)); try easy. inv X2.
  replace ((l + na - l)) with na  in H17 by lia. easy.
  replace ((l + na + 1)) with (l + S na) in * by lia. easy.
Qed.

Lemma type_preserve: forall rmax q env T T' s s' e, @locus_system rmax q env T e T' 
  -> env_state_eq T (snd s) -> kind_env_stack env (fst s) -> freeVarsNotCPExp env e
  -> simple_tenv T 
      -> @qfor_sem rmax env s e s' 
        -> simple_tenv T' /\ AEnv.Equal (fst s) (fst s') /\ env_state_eq T' (snd s').
Proof.
  intros. generalize dependent s. generalize dependent s'.
  induction H; intros;simpl in *; subst.
 -
  destruct s0; simpl in *.
  apply env_state_eq_app in H0 as X1; try easy.
  destruct X1 as [s1 [s2 [X1 [X2 X3]]]].
  subst. apply env_state_eq_same_length in X1; try easy.
  destruct X1. apply simple_tenv_app_l in H3 as X1.
  apply type_sem_local with (q := q) (env := env) (T := T) (T' := T') in H4; try easy.
  destruct H4 as [sa [Y1 [Y2 Y3]]]; subst. destruct s'; simpl in *; subst.
  apply IHlocus_system in Y2; try easy. destruct Y2 as [A1 [A2 A3]].
  split. apply simple_tenv_app; try easy.
  apply simple_tenv_app_r in H3; try easy. split. easy.
  apply env_state_eq_app_join; try easy.
 -
  inv H4. easy.
 -
  inv H6.
  rewrite H0 in H13. inv H13.
  rewrite simple_env_subst in IHlocus_system; try easy.
  apply freeVars_pexp_in with (v := n) in H2 as X1; try easy.
  specialize (IHlocus_system X1 H3 s' s H4 H5 H14). easy.
  apply simp_aexp_no_eval in H13. rewrite H0 in *. easy.
 -
  inv H6. 
  apply type_aexp_mo_no_simp in H. rewrite H in *. easy.
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H7. inv H7. easy.
  apply AEnv.add_3 in H7; try lia.
  apply H2 with (x0 := x0). simpl.
  apply in_app_iff. right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  specialize (IHlocus_system H6 H3 (W, s'0) (update_cval s x n)).
  simpl in *.
  assert (kind_env_stack
                     (AEnv.add x (Mo MT) env)
                     (AEnv.add x n (fst s))).
  unfold kind_env_stack. split. intros.
  bdestruct (x0 =? x); subst.
  exists n. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H7; try easy.
  apply H5 in H7. destruct H7.
  exists x1. apply AEnv.add_2. lia. easy. lia.
  intros.
  bdestruct (x0 =? x); subst.
  apply AEnv.add_1. easy.
  destruct H7.
  apply AEnv.add_3 in H7; try easy.
  assert (AEnv.In x0 (fst s)). exists x1. easy.
  apply H5 in H9.
  apply AEnv.add_2. lia. easy. lia.
  destruct (IHlocus_system H4 H7 H14) as [Y1 [Y2 Y3]].
  split. easy.
  split; try easy.
 -
  inv H6.
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H7. inv H7. easy.
  apply AEnv.add_3 in H7; try lia.
  apply H2 with (x0 := x0). simpl.
  right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  assert (simple_tenv ((l, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H7. inv H7.
  specialize (H3 ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
     In ((y, BNum 0, BNum n) :: a, CH) T). left. easy.
  apply H3 in H7.
  inv H7. easy. apply H3 with (b:= b). right. easy.
  unfold build_state_ch in *. destruct va; try easy.
  destruct (build_state_pars m n0 v (to_sum_c m n0 v b) b); try easy.
  inv H15.
  inv H4.
  specialize (IHlocus_system H6 H7 (W', s'0) (AEnv.add x (r, v) W, (l0, Cval n1 p) :: s0)).
  assert (env_state_eq ((l0, CH) :: T) ((l0, Cval n1 p) :: s0)).
  constructor. easy. constructor.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x (r, v) W)).
  unfold kind_env_stack in *. split; intros.
  bdestruct (x0 =? x); subst.
  exists (r, v). apply AEnv.add_1. easy.
  apply AEnv.add_3 in H8; try lia.
  apply H5 in H8. destruct H8.
  exists x1. apply AEnv.add_2; try lia. easy. simpl in *.
  bdestruct (x0 =? x); subst. apply AEnv.add_1. easy.
  assert (AEnv.In (elt:=R * nat) x0 W).
  destruct H8. exists x1. apply AEnv.add_3 in H8; try lia. easy.
  apply H5 in H12. apply AEnv.add_2. lia. easy.
  destruct (IHlocus_system H4 H8 H16) as [Y1 [Y2 Y3]]. split; try easy.
 -
  inv H5; simpl in *. inv H1. inv H7. 
  split. easy. split;try easy. constructor. constructor. constructor.
  inv H1. inv H13.
 - 
  inv H5. inv H1. inv H13.
  inv H1. inv H7.
  apply app_inv_head_iff in H9. subst.
  split. easy. split. easy.
  constructor. constructor. constructor.
 -
  inv H5. inv H1. inv H8.
  split.
  unfold simple_tenv in *. intros.
  simpl in *. destruct H1; try easy. inv H1. apply H3 with (b := TNor).
  left. easy.
  split; try easy.
  constructor. constructor. constructor.
  inv H1. inv H14.
 -
  inv H5. inv H1. inv H14.
  inv H1. inv H8. split.
  unfold simple_tenv in *. intros.
  simpl in *. destruct H1; try easy. inv H1. apply H3 with (b := THad).
  left. easy.
  split; try easy.
  constructor. constructor. constructor.
 -
  inv H6.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros.
  simpl in *. apply H2 with (x := x); try easy.
  apply in_app_iff. right. easy.
  specialize (IHlocus_system H6 H3 s' s H4 H5 H13). split; easy.
  rewrite H0 in H12. inv H12.
  apply type_bexp_only with (t := (QT n, l)) in H; subst; try easy.
 - 
  inv H5. rewrite H0 in H10. inv H10.
  easy.
  apply type_bexp_only with (t := (QT n, l)) in H; subst; try easy.
 -
  inv H5. apply simp_bexp_no_qtype in H. rewrite H in *. easy.
  apply simp_bexp_no_qtype in H. rewrite H in *. easy.
  split. easy. inv H1. inv H7.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros.
  simpl in *. apply H2 with (x := x); try easy.
  apply in_app_iff. right. easy.
  assert (simple_tenv ((l1, CH) :: nil)).
  unfold simple_tenv in *. intros. simpl in *; try easy. destruct H5; try easy.
  inv H5.
  specialize (H3 (l ++ a) CH).
  assert ((l ++ a, CH) = (l ++ a, CH) \/ False).
  left. easy. apply H3 in H5.
  apply simple_ses_app_r in H5. easy.
  apply type_bexp_only with (t := (QT n0, l0)) in H; try easy.
  inv H. apply app_inv_head_iff in H13; subst.
  specialize (IHlocus_system H1 H5
          (W', (l2, fc') :: s'0) (W, (l2, fc) :: nil)).
  assert (env_state_eq ((l2, CH) :: nil)
                     (snd (W, (l2, fc) :: nil))).
  constructor; try easy. constructor.
  inv H11. constructor.
  simpl in *.
  destruct (IHlocus_system H H4 H14) as [X1 X2].
  inv X2. constructor; try easy.
  inv H7. inv H15.
  constructor. constructor.
  inv H16; try constructor.
 -
  inv H5.
  assert (freeVarsNotCPExp env e1).
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x); try easy.
  simpl in *. apply in_app_iff. left. easy.
  assert (freeVarsNotCPExp env e2).
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x); try easy.
  simpl in *. apply in_app_iff. right. easy.
  destruct (IHlocus_system1 H5 H3 s1 s H1 H4 H10) as [X1 [X2 X3]].
  apply kind_env_stack_equal with (env := env) in X2 as X4; try easy.
  destruct (IHlocus_system2 H6 X1 s' s1 X3 X4 H12) as [Y1 [Y2 Y3]].
  split; try easy. split; try easy.
  apply AEnvFacts.Equal_trans with (m' := fst s1); try easy.
 -
  inv H4. assert (h-l = 0) by lia. rewrite H4 in *. inv H13.
  split; try easy.
 -
  split. eapply simple_tenv_subst_right. apply H3.
  inv H7.
  remember (h-l) as na.
  assert (h=l+na) by lia. rewrite H7 in *. clear H7. clear h.
  assert (forall v, freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v))) as Y1.
  intros.
  unfold freeVarsNotCPExp in *.
  intros;simpl in *. apply H2 with (x := x); try easy.
  apply in_app_iff in H7. 
  bdestruct (x =? i); subst.
  assert (AEnv.In i env). exists (Mo t). easy. easy.
  destruct H7.
  apply in_app_iff. left.
  apply list_sub_not_in; try easy.
  apply freeVarsBExp_subst in H7. easy.
  apply in_app_iff. right.
  apply list_sub_not_in; try easy.
  apply freeVarsPExp_subst in H7. easy.
  clear H. clear H2. clear Heqna.
  generalize dependent s'.
  induction na;intros;simpl in *.
  inv H16. split. easy.
  replace (l+0) with l by lia. easy.
  inv H16.
  assert (forall v : nat,
        l <= v < l + na ->
        @locus_system rmax q env (subst_type_map T i v) (If (subst_bexp b i v) (subst_pexp e i v))
          (subst_type_map T i (v + 1))).
  intros. apply H1. lia.
  assert ((forall v : nat,
        l <= v < l + na ->
        freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v)) ->
        simple_tenv (subst_type_map T i v) ->
        forall (s' : state) (s : stack * qstate),
        env_state_eq (subst_type_map T i v) (snd s) ->
        kind_env_stack env (fst s) ->
        @qfor_sem rmax env s (If (subst_bexp b i v) (subst_pexp e i v)) s' ->
        simple_tenv (subst_type_map T i (v + 1)) /\
        AEnv.Equal (fst s) (fst s') /\
        env_state_eq (subst_type_map T i (v + 1)) (snd s'))).
  intros. apply H4; try lia; try easy.
  destruct (IHna H H8 s'0 H2) as [X1 X2].
  assert (l <= l+ na < l + S na) by lia.
  apply simple_tenv_subst_right with (v := (l+na)) in H3 as Y2.
  apply kind_env_stack_equal with (env := env) in X1 as X4; try easy.
  destruct (H4 (l + na) H9 (Y1 (l+na)) Y2 s' s'0 X2 X4 H7) as [X7 [X8 X9]].
  split.
  apply AEnvFacts.Equal_trans with (m' := fst s'0); try easy.
  replace ((l + na + 1)) with (l + S na) in * by lia. easy.
Qed.

Lemma type_preserves: forall na b e rmax q env i l T s s',
  (forall v : nat, l <= v < l + na -> @locus_system rmax q env (subst_type_map T i v)
       (If (subst_bexp b i v) (subst_pexp e i v)) (subst_type_map T i (v + 1)))
  -> env_state_eq (subst_type_map T i l) (snd s) -> kind_env_stack env (fst s) 
  -> (forall v, freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v)))
  -> (forall v : nat, simple_tenv (subst_type_map T i v))
  -> ForallA rmax (@qfor_sem) na env s l i b e s'
  -> AEnv.Equal (fst s) (fst s') /\ env_state_eq (subst_type_map T i (l + na)) (snd s').
Proof.
  induction na; intros; simpl in *; try easy.
  inv H4. split. easy.
  replace (l+0) with l by lia.
  easy.
  inv H4. apply IHna with (q := q) (T := T) in H6; try easy.
  destruct H6.
  apply type_preserve with (q := q) (T := (subst_type_map T i (l + na)))
    (T' := (subst_type_map T i (l + S na))) in H7; try easy.
  destruct H7 as [X1 [X2 X3]].
  split. apply AEnvFacts.Equal_trans with (m' := fst s'0); try easy.
  easy.
  specialize (H (l+na)).
  replace (l+na + 1) with (l + S na) in H by lia.
  apply H. lia.
  apply kind_env_stack_equal with (s2 := (fst s'0)) in H1; try easy.
  intros. apply H. lia.
Qed.

Lemma eval_aexp_twice_same: forall s a v v1, eval_aexp s a v
  -> eval_aexp s a v1 -> v = v1.
Proof.
  intros. generalize dependent v1. induction H; intros; simpl in *; try easy.
  inv H0; try easy.
  apply aenv_mapsto_always_same with (v1 := (r0,n0)) in H; try easy.
  inv H0. easy.
  inv H1.
  rewrite H0 in H7. inv H7.
  apply IHeval_aexp in H5. inv H5. easy.
  apply simp_aexp_no_eval in H5. rewrite H5 in *. easy.
  inv H1. apply simp_aexp_no_eval in H5. rewrite H5 in *. easy.
  rewrite H0 in H7. inv H7.
  apply IHeval_aexp in H5. inv H5. easy.
  inv H1.
  rewrite H0 in H7. inv H7.
  apply IHeval_aexp in H5. inv H5. easy.
  apply simp_aexp_no_eval in H5. rewrite H5 in *. easy.
  inv H1. apply simp_aexp_no_eval in H5. rewrite H5 in *. easy.
  rewrite H0 in H7. inv H7.
  apply IHeval_aexp in H5. inv H5. easy.
Qed.

(*
Lemma qfor_sem_single_out: forall rmax env s e s1 s2,
   @qfor_sem rmax env s e s1 -> @qfor_sem rmax env s e s2 -> s1 = s2.
Proof.
  intros. generalize dependent s2.
  induction H; intros; simpl in *; try easy.
  inv H0. easy.
  inv H1. apply IHqfor_sem. rewrite H in H8. inv H8. easy.
  apply simp_aexp_no_eval in H8. rewrite H8 in *. easy.
  inv H1. apply simp_aexp_no_eval in H. rewrite H in *. easy.
  apply eval_aexp_twice_same with (v := n0) in H; try easy; subst.
  apply IHqfor_sem in H9. inv H9. easy.
  inv H3. inv H0. inv H15.
  inv H1.
Qed.
*)

Lemma foralla_sub: forall v rmax na env s l i b e s',
    v <= na ->
    ForallA rmax (@qfor_sem) na env s l i b e s'
   -> exists sa, ForallA rmax (@qfor_sem) v env s l i b e sa 
    /\ ForallA rmax (@qfor_sem) (na-v) env sa (l+v) i b e s'.
Proof.
  induction na; intros; simpl in *; try easy.
  assert (v = 0) by lia. subst.
  exists s. split. constructor.
  replace (l+0) with l by lia.
  easy.
  bdestruct (v =? S na); subst.
  replace (na-na) with 0 by lia.
  exists s'. split. easy. constructor.
  inv H0.
  apply IHna in H3; try lia.
  destruct H3 as [sa [X1 X2]].
  exists sa. split; try easy.
  assert (match v with
                         | 0 => S na
                         | S l0 => na - l0
                         end  = S (na -v)).
  destruct v. lia.
  lia.
  rewrite H0.
  apply ForallA_cons with (s' := s'0); try easy.
  replace ((l + v + (na - v))) with (l+na) by lia.
  easy.
Qed.

Lemma set_inter_app:
 forall l l1 l2, ListSet.set_inter posi_eq_dec (l++l1) l2 = []
           -> ListSet.set_inter posi_eq_dec l1 l2 = [].
Proof.
  induction l;intros;simpl in *. easy.
  destruct (ListSet.set_mem posi_eq_dec a l2) eqn:eq1.
  apply ListSet.set_mem_correct1 in eq1.
  apply IHl. easy.
  apply IHl in H. easy.
Qed.

Lemma gen_qubit_ses_app: forall l l1 A, gen_qubit_ses (l ++ l1) = Some A -> 
     exists B, exists C, gen_qubit_ses l1 = Some C /\ A = B ++ C.
Proof.
  induction l; intros; simpl in *.
  exists [], A. simpl in *. easy.
  destruct (gen_qubit_ses (l ++ l1)) eqn:eq1; simpl in *; try easy.
  destruct (gen_qubit_range a) eqn:eq2; simpl in *; try easy.
  inv H.
  destruct (IHl l1 l0 eq1) as [B [C [X1 X2]]].
  exists (l2 ++ B), C. split. easy. rewrite X2.
  rewrite app_ass. easy.
Qed.

Lemma subst_type_simple: forall T T1 i v, simple_tenv T1 ->
        subst_type_map T i v ++ T1 = subst_type_map (T++T1) i v.
Proof.
  induction T; intros; simpl in *. rewrite simple_env_subst; try easy.
  destruct a; try easy. simpl in *. rewrite IHT. easy. easy.
Qed.

