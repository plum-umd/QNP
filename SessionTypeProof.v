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

(*
  | let_sem_q : forall aenv s s' x a n e r v, AEnv.MapsTo x (QT n) aenv ->
                       @pick_mea rmax s a n (r,v) -> @mask_state rmax ([(a,BNum 0,BNum n)]) v (snd s) s'
                  -> qfor_sem (AEnv.add x (Mo MT) aenv) s (Let x (Meas a) e) (update_cval (fst s,s') x (r,v)) e


  exists (update_cval s x n).
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
      @session_system rmax t aenv tenv e tenv' -> freeVarsNotCPExp aenv e ->
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
  specialize (kind_env_stack_exist env (fst s) a H0 H4 H1) as X1.
  destruct X1.
  exists (update_cval s x x0). constructor. easy. right. easy.
 (* Let rule with measure. *)
  right. exists e.

Admitted.
                                 

Lemma session_progress : 
    forall e rmax t aenv s tenv tenv1 tenv', @env_state_eq tenv (snd s) ->
      @env_equiv tenv tenv1 ->
      @session_system rmax t aenv tenv1 e tenv' ->
           e = PSKIP \/ (exists e' s1 s', @state_equiv rmax (snd s) s1 -> @qfor_sem rmax aenv (fst s,s1) e s' e').
Proof. Admitted.




