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

Definition type_value_eq (t: se_type) (v:state_elem) := 
  match t with TNor => match v with Nval p c => True | _ => False end
             | THad => match v with Hval f => True | _ => False end
             | CH => match v with Cval m f => True | _ => False end
  end.

Inductive env_state_eq : type_map -> qstate ->  Prop :=
    env_state_eq_empty : env_state_eq nil nil
  | env_state_eq_many : forall s t a l1 l2, env_state_eq l1 l2 -> type_value_eq t a -> env_state_eq ((s,t)::l1) ((s,a)::l2).

Definition qstate_wt {rmax} S := forall s s' m bl, @find_state rmax S s (Some (s',Cval m bl)) -> m > 0.

(*TODO: Le Chang, please finish the proof.*)
Lemma find_type_state : forall s s' t r T S, env_state_eq T S -> find_type T s (Some (s++s',t))
       -> (exists S' a, @state_equiv r S S' /\ find_env S' s (Some (s++s',a)) /\ type_state_elem_same t a).
Proof.
  intros. inv H0.
  induction H1.
  inv H.
Admitted.

(*TODO: Le Chang, please finish the proof.
  Should be easy, just have sub-lemma to induct on find_env. see what is its relation with up_state. *)
Lemma find_state_up_good {rmax}: forall S s s' v v', @find_state rmax S s (Some (s',v)) -> exists S', @up_state rmax S s v' S'.
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


Inductive find_env {A:Type}: list (session * A) -> session -> option (session * A) -> Prop :=
  | find_env_empty : forall l, find_env nil l None
  | find_env_many_1 : forall S x y t, ses_sub x y -> find_env ((y,t)::S) x (Some (y,t))
  | find_env_many_2 : forall S x y v t, ~ ses_sub x y -> find_env S y t -> find_env ((x,v)::S) y t.

Lemma find_type_ch : forall T1 s s' t, find_type T1 s (Some (s',t)) -> find_type T1 s (Some (s',CH)).
Proof.
  intros. inv H.
  specialize (find_env_ch S' s s' t H1) as X1. destruct X1 as [T' [X1 X2]].
  apply find_type_rule with (S := T1) in X2; try easy.
  apply env_equiv_trans with (T2 := S'); easy.
Qed.

Lemma pick_mea_exists {rmax}: forall T S t s' x n, @qstate_wt rmax S -> env_state_eq T (snd S) 
             -> find_type T ([(x,BNum 0,BNum n)]) (Some (([(x,BNum 0,BNum n)])++s',t)) -> 
          exists r v, @pick_mea rmax S x n (r,v).
Proof.
  intros.
  apply find_type_ch in H1.
  apply find_type_state with (r := rmax) (S := snd S) in H1 as X1.
  destruct X1 as [S' [a [X1 [X2 X3]]]].
  inv X3.
  assert (@find_state rmax S [(x, BNum 0, BNum n)] (Some ([(x, BNum 0, BNum n)] ++ s', Cval m bl))).
  destruct S. apply find_qstate_rule with (S'0 := S'); try easy.
  apply H in H2 as X3.
  assert (exists i, 0 <= i < m). exists 0. lia. destruct H3.
  remember (bl x0) as ra. destruct ra.
  exists (Cmod c). exists (a_nat2fb r n).
  apply pick_meas with (l := s') (m0 := m) (b := bl) (i := x0); try easy.
  easy.
Qed. 

(*

   pick_meas : forall s x n l m b i r bl, @find_state rmax s ([(x,BNum 0,BNum n)]) (Some (([(x,BNum 0,BNum n)])++l, Cval m b))
            -> 0 <= i < m -> b i = (r,bl) -> pick_mea s x n (Cmod r, a_nat2fb bl n).

  | let_sem_q : forall aenv s s' x a n e r v, AEnv.MapsTo x (QT n) aenv ->
                       @pick_mea rmax s a n (r,v) -> @mask_state rmax ([(a,BNum 0,BNum n)]) v (snd s) s'
                  -> qfor_sem (AEnv.add x (Mo MT) aenv) s (Let x (Meas a) e) (update_cval (fst s,s') x (r,v)) e


@pick_mea rmax s a n (r,v) -> @mask_state rmax ([(a,BNum 0,BNum n)]) v s s'
                  -> qfor_sem (AEnv.add x (Mo MT) aenv) s (Let x (Meas a) e) (update_cval s' x (r,v)) e
*)

Definition kind_env_stack (env:aenv) (s:stack) : Prop :=
  forall x t, AEnv.MapsTo x (Mo t) env -> AEnv.In x s.

Inductive env_state_eqv {r:nat} : type_map -> qstate ->  Prop :=
    env_state_eqv_rule : forall l1 l2 l1' l2', 
      env_equiv l1 l1' -> @state_equiv r l2 l2' -> env_state_eq l1' l2' -> env_state_eqv l1 l2.

Lemma env_state_equiv :
  forall rmax s t1 t2, @env_state_eqv rmax t1 s -> env_equiv t1 t2 -> (exists s1, @state_equiv rmax s s1 /\ @env_state_eqv rmax t2 s1).
  Proof. Admitted.


Lemma session_progress_1 : 
    forall e rmax t aenv s tenv tenv', @env_state_eq tenv (snd s) -> kind_env_stack aenv (fst s) ->
      @session_system rmax t aenv tenv e tenv' -> freeVarsNotCPExp aenv e -> @qstate_wt rmax s ->
           e = PSKIP \/ (exists e' s', @qfor_sem rmax aenv s e s' e').
Proof.
  intros. induction H1; simpl in *.
  left. easy.
  right. exists ((subst_pexp e x v)).
  exists s. apply let_sem_c; simpl in *; easy.
  right.
  exists e.
  unfold freeVarsNotCPExp in H2. simpl in H2.
  assert (freeVarsNotCAExp env a).
  unfold freeVarsNotCAExp. intros. apply (H2 x0); try easy.
  apply in_app_iff. left. easy.
  apply kind_aexp_class_empty in H1 as X2; subst.
  specialize (kind_env_stack_exist env (fst s) a H0 H5 H1) as X1.
  destruct X1.
  exists (update_cval s x x0). constructor. easy. right. easy.
 (* Let rule with measure. *)
  right. exists e.
  apply (@pick_mea_exists rmax T s) in H4 as X1.
  destruct X1 as [r [cv X1]].
Admitted.
                                 

Lemma session_progress : 
    forall e rmax t aenv s tenv tenv1 tenv', @env_state_eq tenv (snd s) ->
      @env_equiv tenv tenv1 ->
      @session_system rmax t aenv tenv1 e tenv' ->
           e = PSKIP \/ (exists e' s1 s', @state_equiv rmax (snd s) s1 -> @qfor_sem rmax aenv (fst s,s1) e s' e').
Proof. Admitted.




