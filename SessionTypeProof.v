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
Require Import QWhileSyntax.
Require Import SessionDef.
Require Import SessionKind.
Require Import SessionSem.
Require Import SessionType.
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

(*TODO: Le Chang, additional theorem. *)
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
  
Lemma env_state_eq_trans: forall r T T' S, env_state_eq T S -> env_equiv T T' -> (exists S', @state_equiv r S S' /\ env_state_eq T' S').
Proof.
   intros. generalize dependent S. induction H0...
  - intros. exists S0. split. constructor. easy.
  - intros... 
    inv H. exists l2. split. constructor. easy.
  - intros. apply env_state_eq_app in H as X1.
    destruct X1 as [b1 [b2 [X1 [X2 X3]]]]; subst.
    exists (b2 ++ b1). split. apply state_comm. apply env_state_eq_app_comm; try easy.
  - intros.
Admitted.

(*TODO: Le Chang, us eht result in find_env_state. *)
Lemma find_type_state : forall s s' t r T S, env_state_eq T S -> find_type T s (Some (s++s',t))
       -> (exists S' a, @state_equiv r S S' /\ find_env S' s (Some (s++s',a)) /\ type_state_elem_same t a).
Proof.
  intros.  inv H0. 
  (* use the env_state_eq_trans.  *)
  specialize (find_env_state s s' t T S H) as X1.
Admitted.

Lemma find_type_state_1 : forall s s' t r T M S, env_state_eq T S -> find_type T s (Some (s++s',t))
       -> (exists a, @find_state r (M,S) s (Some (s++s',a)) /\ type_state_elem_same t a).
Proof.
  intros. apply find_type_state with (r := r) (S := S) in H0.
  destruct H0 as [S' [a [X1 [X2 X3]]]].
  exists a. split. apply find_qstate_rule with (S'0 := S'); try easy. apply X3. easy.
Qed.

(*TODO: Le Chang, please finish the proof.
  Should be easy, just have sub-lemma to induct on find_env. see what is its relation with up_state. *)
Lemma find_state_up_good {rmax}: forall S s s' v v', @find_state rmax S s (Some (s',v)) -> exists S', @up_state rmax S s v' S'.
Proof.
  intros. inv H.
Admitted.

Lemma find_state_up_good_1 {rmax}: forall S s s' v v', @find_state rmax S s (Some (s',v)) -> exists S', @up_state rmax S s' v' S'.
Proof.
  intros. inv H.
Admitted.

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
          exists r v, @pick_mea (((x,BNum 0,BNum n)::l, Cval m b)::S) (r,v).
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


Lemma mask_state_exists: forall S l x n m bl r v,
             @pick_mea (((x,BNum 0,BNum n)::l, Cval m bl)::S) (r,v) ->
          (exists na p, build_state_ch n v (Cval m bl) = Some (Cval na p) /\ na > 0).
Proof.
  intros. inv H.
Admitted.


Definition kind_env_stack (env:aenv) (s:stack) : Prop :=
  forall x t, AEnv.MapsTo x (Mo t) env -> AEnv.In x s.

Definition kind_env_wf (env:aenv) : Prop :=
  forall x n, AEnv.MapsTo x (QT n) env -> n > 0.

Definition env_wf (env:type_map) : Prop :=
   forall x t, In (x,t) env -> simple_ses x.

Inductive env_state_eqv {r:nat} : type_map -> qstate ->  Prop :=
    env_state_eqv_rule : forall l1 l2 l1' l2', 
      env_equiv l1 l1' -> @state_equiv r l2 l2' -> env_state_eq l1' l2' -> env_state_eqv l1 l2.

Lemma env_state_equiv :
  forall rmax s t1 t2, @env_state_eqv rmax t1 s -> env_equiv t1 t2 -> (exists s1, @state_equiv rmax s s1 /\ @env_state_eqv rmax t2 s1).
  Proof. Admitted.

Lemma env_equiv_simple_type : forall T T', env_equiv T T' -> simple_tenv T -> simple_tenv T'.
Proof.
  intros. induction H; simpl in *. easy.
  unfold simple_tenv in *. intros. apply (H0 a b). simpl. right. easy.
  unfold simple_tenv in *. intros.
  apply (H0 a b). apply in_or_app. apply in_app_iff in H. destruct H. right. easy. left. easy.
  unfold simple_tenv in *. intros.
  simpl in H1. destruct H1. inv H1. apply (H0 a v). simpl. left. easy.
  apply (H0 a b). simpl. right. easy.
  unfold simple_tenv in *. intros.
  simpl in *. destruct H1. inv H1. apply (H0 a b). left. easy.
  assert (forall (a : session) (b : se_type),
               In (a, b) S -> simple_ses a).
  intros. apply (H0 a0 b0). right. easy.
  specialize (IHenv_equiv H2). apply (IHenv_equiv a b). easy.
Admitted.

Lemma find_env_simple: forall T l l' t, @find_env se_type T l (Some (l',t)) -> simple_tenv T -> simple_ses l'.
Proof.
  intros. remember (Some (l', t)) as a. induction H; subst; try easy.
  inv Heqa. unfold simple_tenv in *.
  apply (H0 l' t). simpl. left. easy.
  apply IHfind_env; try easy.
  unfold simple_tenv in *. intros. apply (H0 a b). simpl in *. right. easy.
Qed.

Lemma find_type_simple: forall T l l' t, find_type T l (Some (l',t)) -> simple_tenv T -> simple_ses l'.
Proof.
  intros. inv H. apply env_equiv_simple_type in H1; try easy. eapply (find_env_simple S' l l' t); try easy.
Qed.

Lemma update_env_simple: forall T l t T', update_env T l t T' -> simple_tenv T -> simple_ses l -> simple_tenv T'.
Proof.
  intros. induction H; simpl in *; try easy.
  unfold simple_tenv in *. intros. simpl in *. inv H; try easy. inv H2. easy.
  unfold simple_tenv in *. intros. simpl in *. inv H2. inv H3. easy.
  apply H0 with (b := b). right. easy.
  unfold simple_tenv in *. intros. simpl in *.
  inv H3. inv H4.
Admitted.

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

Lemma qstate_wt_eq : forall r S S', @qstate_wt S -> @state_equiv r S S' -> @qstate_wt S'.
Proof.
  intros.
Admitted.

(*
Lemma qstate_wt_stack_eq: forall r W W' S, @qstate_wt r S -> @qstate_wt r (W',S).
Proof.
 intros. unfold qstate_wt in *.
 intros. apply H with (s := s) (s' := s') (bl := bl).
 inv H0. apply find_qstate_rule with (S'0 := S'); try easy.
Qed.
*)

Lemma simple_ses_subst: forall s x v, simple_ses s -> (subst_session s x v) = s.
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
  specialize (H s s0). apply H. left. easy.
  intros. eapply H. simpl. right. apply H0.
Qed.

Lemma aenv_find_add : forall k v (m:aenv),
        AEnv.find k (AEnv.add k v m) = Some v.
Proof.
      intros.
      apply AEnv.find_1.
      apply AEnv.add_1.
      easy.
Qed.

Lemma aenv_mapsto_add1 : forall k v1 v2 (s:aenv),
        AEnv.MapsTo k v1 (AEnv.add k v2 s) -> v1 = v2.
Proof.
      intros.
      apply AEnv.find_1 in H.
      rewrite aenv_find_add in H.
      inversion H.
      reflexivity.
Qed.

Lemma type_cbexp_class: forall env b t, type_cbexp env b t -> exists t', t = Mo t'.
Proof.
  intros. induction H. unfold is_class_type in *.
  destruct t1 eqn:eq1; try easy. destruct a0. destruct t2 eqn:eq2; try easy.
  destruct a0. exists CT; easy.
  exists MT. easy.
  destruct t2 eqn:eq2; try easy. destruct a0.
  exists MT. unfold meet_ktype in *. easy. exists MT. easy.
  unfold is_class_type in *.
  destruct t1 eqn:eq1; try easy. destruct a0. destruct t2 eqn:eq2; try easy.
  destruct a0. exists CT; easy.
  exists MT. easy.
  destruct t2 eqn:eq2; try easy. destruct a0.
  exists MT. unfold meet_ktype in *. easy. exists MT. easy.
Qed.

Lemma eval_bexp_exists : forall aenv n b s l l1 m f, type_bexp aenv b (QT n, l) 
   -> exists f', @eval_bexp ((l++l1, Cval m f)::s) b ((l++l1, Cval m f')::s).
Proof.
  intros. remember (QT n, l) as S. induction H.
  apply type_cbexp_class in H. destruct H; subst. inv HeqS.
  inv HeqS.
  exists (eval_eq_bool f m m0 b). apply beq_sem_1.
  inv HeqS.
  exists (eval_eq_bool f m m0 b). apply beq_sem_2.
  inv HeqS.
  exists (eval_lt_bool f m m0 b). apply blt_sem_1.
  inv HeqS.
  exists (eval_rlt_bool f m m0 b). apply blt_sem_2.
  inv HeqS.
  exists f. apply btext_sem.
Admitted.

Lemma simple_ses_get_core_exists : forall l, simple_ses l -> exists l', get_core_ses l = Some l'.
Proof.
  induction l; intros;simpl in *.
  exists nil. easy.
  inv H. apply IHl in H4. unfold simple_bound in *.
  destruct x; try easy. destruct y; try easy.
  destruct H4. exists ((a0, n, n0) :: x). rewrite H. easy.
Qed.

Lemma simple_ses_len_exists : forall l, simple_ses l -> exists  n, ses_len l = Some n.
Proof.
  intros. apply simple_ses_get_core_exists in H. destruct H.
  unfold ses_len in *. rewrite H. exists (ses_len_aux x). easy.
Qed.

Lemma type_bexp_gt : forall env b n l, type_bexp env b (QT n, l) -> n > 0.
Proof.
  intros. remember (QT n, l) as t. induction H; try easy.
  apply type_cbexp_class in H. destruct H; subst. inv Heqt. inv Heqt. lia.
  inv Heqt. lia. inv Heqt. lia. inv Heqt. lia. inv Heqt. lia.
  subst. apply IHtype_bexp. easy.
Qed.

Axiom fun_all_equal : forall (f c: rz_val), f = c \/ f <> c.

Lemma assem_elem_exists: forall m m' c f, exists l, assem_elem m m' c f l.
Proof.
  induction m;intros;simpl in *.
  exists nil. apply assem_elem_0.
  specialize (fun_all_equal (cut_n (snd (f m)) m') c) as X1.
  destruct X1.
  destruct (IHm m' c f).
  exists (m::x). apply assem_elem_st; try easy.
  destruct (IHm m' c f).
  exists x. apply assem_elem_sf; try easy.
Qed.


Lemma assem_bool_exists: forall m m' n f' fc, exists fa, assem_bool m m' n f' fc fa.
Proof.
  induction m;intros;simpl in *.
  exists (0,fun _ => (C0,allfalse)). apply assem_bool_0.
  destruct (IHm m' n f' fc). destruct x.
  destruct (assem_elem_exists m' n (cut_n (snd (f' m)) n) fc).
  destruct (Nat.eq_dec (length x) 0). apply length_zero_iff_nil in e. subst.
  exists (n0+1, update p n0 (f' m)).
  apply assem_bool_sf; try easy.
  assert (x <> nil). intros R.
  apply length_zero_iff_nil in R. lia.
  exists (assem_list n0 x fc p).
  apply assem_bool_st; try easy.
Qed.

Lemma simple_subst_ses: forall s i l, simple_ses (subst_session s i l) -> (forall v, simple_ses (subst_session s i v)).
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
  specialize (H (subst_session s i l) b). 
  assert ((subst_session s i l, b) = (subst_session s i l, b) \/
    In (subst_session s i l, b) (subst_type_map T i l)). left. easy.
  apply H in H0. eapply simple_subst_ses. apply H0.
  apply IHT. intros. apply H with (b := b0). right. easy.
  easy.
Qed.

Lemma type_soundness : 
    forall e rmax t aenv s tenv tenv', @env_state_eq tenv (snd s) -> kind_env_stack aenv (fst s) ->
      @session_system rmax t aenv tenv e tenv' -> freeVarsNotCPExp aenv e -> @qstate_wt (snd s) -> simple_tenv tenv ->
          simple_tenv tenv' /\
          (exists s', @qfor_sem rmax aenv s e s'
             /\ kind_env_stack aenv (fst s') /\ @qstate_wt (snd s') /\ env_state_eq tenv' (snd s')).
Proof.
  intros.
  generalize dependent s.
  induction H1; simpl in *; intros.
 -
  specialize (env_equiv_simple_type T1 T2 H H4) as X1.
  specialize (IHsession_system H2 X1).
  specialize (env_state_eq_trans rmax T1 T2 (snd s0) H0 H) as X2.
  destruct X2 as [Sa [X2 X3]].
  specialize (IHsession_system (fst s0,Sa) X3 H3).
  destruct s0; simpl in *. apply qstate_wt_eq with (r := rmax) (S' := Sa) in H5; try easy.
  apply IHsession_system in H5. destruct H5. split. easy.
  destruct H6 as [s' [X4 [X5 X6]]].
  exists s'. split. apply state_eq_sem with (f' := Sa); try easy. easy.
 - 
  split. easy.
  exists s; try easy. split. constructor. easy.
 - 
  apply freeVars_pexp_in with (v := v) in H2 as X1; try easy.
  rewrite simple_env_subst in *; try easy.
  specialize (IHsession_system X1 H4 s H0 H3 H5).
  destruct IHsession_system. split. easy.
  destruct H7 as [s' [X4 [X5 X6]]].
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
  specialize (IHsession_system H8 H4 (update_cval s x x0)).
  unfold update_cval in IHsession_system;simpl in *.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x x0 (fst s))).
  unfold kind_env_stack. intros.
  bdestruct (x1 =? x); subst.
  exists x0. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H9; try easy.
  unfold AEnv.In,AEnv.Raw.PX.In in *.
  apply H5 in H9. destruct H9. exists x2. apply AEnv.add_2. lia. easy. lia.
  destruct s. simpl in *.
  specialize (IHsession_system H3 H9 H6).
  destruct IHsession_system as [X2 [s' [X3 [X4 X5]]]].
  split. easy.
  exists s'. split. apply let_sem_m with (n := x0); try easy.
  split. 
  unfold kind_env_stack in *. intros.
  bdestruct (x1 =? x); subst.
  apply X4 with (t := MT). apply AEnv.add_1. easy.
  apply X4 with (t := t). apply AEnv.add_2. lia. easy.
  easy.
  unfold freeVarsNotCAExp, freeVarsNotCPExp in *.
  intros. simpl in *. apply H2 with (x0 := x0); try easy.
  apply in_app_iff. left. easy.
 -
  destruct s. simpl in *. inv H3. inv H12. 
  destruct (@pick_mea_exists rmax l2 l m bl y n H6) as [ra [va X1]].
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
  specialize (IHsession_system H3 H7 (AEnv.add x (ra,va) s,(l,(Cval na p))::l2)); simpl in *.
  assert (env_state_eq ((l, CH) :: T) ((l, Cval na p) :: l2)).
  constructor. easy. constructor.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x (ra, va) s)).
  unfold kind_env_stack in *. intros.
  bdestruct (x0 =? x); subst.
  exists (ra, va). apply AEnv.add_1. easy.
  apply AEnv.add_3 in H9; try lia.
  apply H5 in H9. destruct H9.
  exists x1. apply AEnv.add_2; try lia. easy.
  assert (@qstate_wt ((l, Cval na p) :: l2)).
  unfold qstate_wt in *. intros.
  simpl in *. destruct H10. inv H10. lia.
  apply H6 with (s := s0) (bl0 := bl0). right. easy.
  destruct (IHsession_system H8 H9 H10) as [Y1 [sa [Y2 [Y3 Y4]]]].
  split. easy.
  exists sa. split. apply let_sem_q with (r := ra) (v := va) (va' := (Cval na p)); try easy.
  split.
  unfold kind_env_stack in *; intros; simpl in *.
  bdestruct (x0 =? x); subst.
  apply Y3 with (t := MT). apply AEnv.add_1. easy.
  apply Y3 with (t := t). apply AEnv.add_2. lia. easy.
  easy.
 -
  destruct s; simpl in *.
  inv H1. inv H11.
  split. unfold simple_tenv in *.
  intros. simpl in *. destruct H1; try easy. inv H1.
  specialize (H4 (l ++ l') TNor). apply H4. left. easy.
  eapply H4. right. apply H1.
  assert (simple_ses (l++l')).
  unfold simple_tenv in *. intros.
  specialize (H4 (l++l') TNor). apply H4. simpl. left. easy.
  apply simple_ses_app_l in H1 as X1.
  destruct (@eval_nor_exists rmax env l n p r e H X1 H0) as [ba X2]. destruct ba.
  exists (s, (l ++ l', Nval c r0) :: l2).
  split. apply appu_sem_nor; try easy. split. easy.
  split.
  unfold qstate_wt in *.
  intros. simpl in *. destruct H6. inv H6. eapply H5. right. apply H6.
  constructor; try easy. constructor.
 -
  destruct s; simpl in *.
  inv H1. inv H11.
  split. unfold simple_tenv in *.
  intros. simpl in *. destruct H1; try easy. inv H1.
  specialize (H4 (l ++ l') CH). apply H4. left. easy.
  eapply H4. right. apply H1.
  assert (simple_ses (l++l')).
  unfold simple_tenv in *. intros.
  specialize (H4 (l++l') CH). apply H4. simpl. left. easy.
  apply simple_ses_app_l in H1 as X1.
  Check eval_ch_exists.
  destruct (@eval_ch_exists rmax m env l n bl e H X1 H0) as [ba X2].
  exists (s, (l ++ l', Cval m ba) :: l2).
  split. apply appu_sem_ch; try easy. split. easy.
  split.
  unfold qstate_wt in *.
  intros. simpl in *. destruct H6. inv H6. eapply H5. left. easy.
  eapply H5. right. apply H6.
  constructor; try easy. constructor.
 - 
  split. unfold simple_tenv in *. intros.
  simpl in *. destruct H6. inv H6. specialize (H4 ([a]) TNor). apply H4. left. easy.
  eapply H4. right. apply H6.
  destruct s; simpl in *. inv H1.
  inv H11.
  exists (s,([a],(Hval (fun i => (update allfalse 0 (r i)))) )::l2).
  split. apply appsu_sem_h_nor; try easy.
  split.
  easy.
  split.
  simpl in *. unfold qstate_wt in *.
  intros. inv H1. inv H6. eapply H5. simpl. right. apply H6. 
  constructor; try easy. constructor.
 -
  split. unfold simple_tenv in *. intros.
  simpl in *. destruct H6. inv H6. specialize (H4 ([a]) THad). apply H4. left. easy.
  eapply H4. right. apply H6.
  destruct s; simpl in *. inv H1.
  inv H11.
  exists (s,([a],(Nval C1 (fun j => bl j 0)))::l2).
  split. apply appsu_sem_h_had; try easy.
  split. easy. split.
  simpl in *. unfold qstate_wt in *.
  intros. inv H1. inv H6. eapply H5. simpl. right. apply H6. 
  constructor; try easy. constructor.
 -
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *; simpl in *.
  intros. apply H2 with (x := x); try easy.
  apply in_app_iff. right. easy.
  destruct (IHsession_system H7 H4 s H3 H5 H6) as [X1 [sa [X2 [X3 X4]]]].
  split. easy.
  exists sa. split. apply if_sem_ct; try easy.
  split. easy.
  split. easy. easy.
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
  destruct s; simpl in *. inv H3. inv H12.
  apply eval_bexp_exists with (s := l2) (l1 := l1) (m := m) (f := bl) in H as X1.
  destruct X1 as [f' X1].
  apply find_env_simple with (l := l++l1) (l' := l++l1) (t := CH) in H4 as X2.
  apply simple_ses_app_r in X2 as X3.
  apply simple_ses_len_exists in X3 as X4. destruct X4 as [n' X4].
  specialize (fch_mut_state 0 n n' (fst (grab_bool f' m n)) (snd (grab_bool f' m n))) as X5.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros; simpl in *.
  eapply H2. apply in_app_iff. right. apply H3. easy.
  assert (simple_tenv ((l1, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *. destruct H7. inv H7.
  apply simple_ses_app_r in X2. easy. apply H4 with (b := b0). right. easy.
  specialize (IHsession_system H3 H7 
   (s,(l1,(Cval (fst (grab_bool f' m n)) (mut_fch_state 0 n n' (snd (grab_bool f' m n)))))::l2)).
  simpl in *.
  assert (env_state_eq ((l1, CH) :: T)
                     ((l1,
                      Cval (fst (grab_bool f' m n))
                        (mut_fch_state 0 n n' (snd (grab_bool f' m n)))) :: l2)).
  constructor. easy. constructor.
  assert (qstate_wt
                     ((l1,
                      Cval (fst (grab_bool f' m n))
                        (mut_fch_state 0 n n' (snd (grab_bool f' m n)))) :: l2)).
  unfold qstate_wt in *.
  intros. simpl in *. destruct H9. inv H9.
  apply grab_bool_gt. apply H6 with (s := l ++ s0) (bl0 := bl). left. easy.
  apply type_bexp_gt in H. easy.
  apply H6 with (s := s0) (bl0 := bl0). right. easy.
  destruct (IHsession_system H8 H5 H9) as [X7 [s' [X8 [X9 [X10 X11]]]]].
  destruct s'; simpl in *. inv X11. inv H16.
  split. easy.
  specialize (fch_mut_state 0 n' n m0 bl0) as X11.
  destruct (assem_bool_exists m m0 n f' (mut_fch_state 0 n' n bl0)) as [fa X12].
  exists (s0, (l++l1, Cval (fst fa) (snd fa))::l3).
  split. eapply if_sem_q; try easy. apply H. apply X1. apply X4. apply X5.
  apply X8. apply X11. apply X12. split. easy.
  split.
  unfold qstate_wt in *. intros; simpl in *.
  destruct H10. inv H10.
  specialize (H6 (l++l1) m bl).
  assert ((l ++ l1, Cval m bl) = (l ++ l1, Cval m bl) \/ In (l ++ l1, Cval m bl) l2).
  left. easy. apply H6 in H10.
  specialize (X10 l1 m0 bl0).
  assert ((l1, Cval m0 bl0) = (l1, Cval m0 bl0) \/ In (l1, Cval m0 bl0) l3).
  left. easy. apply X10 in H12.
  apply assem_bool_gt in X12 as X13; try easy.
  eapply X10. right. apply H10.
  constructor. easy. constructor.
  constructor. apply ses_sub_prop with (b' := nil). simpl.
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
  destruct (IHsession_system1 H1 H4 s H H0 H3) as [X1 [s' [X2 [X3 [X4 X5]]]]].
  destruct (IHsession_system2 H5 X1 s' X5 X3 X4) as [Y1 [s'' [Y2 [Y3 [Y4 Y5]]]]].
  split. easy.
  exists s''. split. apply seq_sem with (s1 := s'); try easy.
  easy.
- split. easy.
  exists s.
  split. constructor. assert (h-l = 0) by lia. rewrite H5 in *. constructor.
  split. easy. split. easy. easy.
- split. eapply simple_tenv_subst_right. apply H4.
  remember (h-l) as na.
  assert (h=l+na) by lia. rewrite H7 in *. clear H7. clear h.
  assert (exists s' : state,
          ForallA rmax (@qfor_sem) na env s l i b e s' /\
          kind_env_stack env (fst s') /\
          qstate_wt (snd s') /\ env_state_eq (subst_type_map T i (l+na)) (snd s')).
  assert (forall v, freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v))) as Y1.
  intros.
  unfold freeVarsNotCPExp in *.
  intros;simpl in *. apply H2 with (x := x); try easy.
  apply in_app_iff in H7. destruct H7. apply freeVarBexp_subst in H7. 
  apply in_app_iff. left. easy.
  apply freeVarPExp_subst in H7.
  apply in_app_iff. right. easy.
  clear H. clear H2. clear Heqna.
  induction na;intros;simpl in *.
  exists s. split. constructor. split. easy. split. easy.
  replace (l+0) with l by lia. easy.
  assert (forall v : nat,
        l <= v < l + na ->
        @session_system rmax q env (subst_type_map T i v) (If (subst_bexp b i v) (subst_pexp e i v))
          (subst_type_map T i (v + 1))).
  intros. apply H0. lia.
  assert (forall v : nat,
        l <= v < l + na ->
        freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v)) ->
        simple_tenv (subst_type_map T i v) ->
        forall s : stack * qstate,
        env_state_eq (subst_type_map T i v) (snd s) ->
        kind_env_stack env (fst s) ->
        qstate_wt (snd s) ->
        simple_tenv (subst_type_map T i (v + 1)) /\
        (exists s' : state,
           @qfor_sem rmax env s (If (subst_bexp b i v) (subst_pexp e i v)) s' /\
           kind_env_stack env (fst s') /\
           qstate_wt (snd s') /\ env_state_eq (subst_type_map T i (v + 1)) (snd s'))).
  intros. apply H1; try lia; try easy.
  destruct (IHna H H2) as [sa [X1 [X2 [X3 X4]]]].
  assert (l <= l+ na < l + S na) by lia.
  specialize (Y1 (l+na)).
  apply simple_tenv_subst_right with (v := (l+na)) in H4 as Y2.
  destruct (H1 (l+na) H7 Y1 Y2 sa X4 X2 X3) as [Y3 [sb [Y4 [Y5 [Y6 Y7]]]]].
  exists sb. split. apply ForallA_cons with (s' := sa); try easy.
  split. easy. split. easy.
  replace ((l + na + 1)) with (l + S na) in * by lia. easy.
  destruct H7 as [sa [Y1 [Y2 [Y3 Y4]]]].
  exists sa. split. constructor.
  replace (l + na - l) with na by lia. easy. easy.
Qed.


