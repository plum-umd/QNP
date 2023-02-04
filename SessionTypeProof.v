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

Definition kind_env_stack (env:aenv) (s:stack) : Prop :=
  forall x t, AEnv.MapsTo x (Mo t) env -> AEnv.In x s.

Inductive env_state_eqv {r:nat} : type_map -> qstate ->  Prop :=
    env_state_eqv_rule : forall l1 l2 l1' l2', 
      env_equiv l1 l1' -> @state_equiv r l2 l2' -> env_state_eq l1' l2' -> env_state_eqv l1 l2.

Lemma env_state_equiv :
  forall rmax s t1 t2, @env_state_eqv rmax t1 s -> env_equiv t1 t2 -> (exists s1, @state_equiv rmax s s1 /\ @env_state_eqv rmax t2 s1).
  Proof. Admitted.

Lemma kind_env_stack_exist : forall env s l a, kind_env_stack env s -> freeVarsNotCAExp env a ->
              type_aexp env a (Mo MT, l) -> exists v, eval_aexp s a v.
Proof.
  intros. remember (Mo MT, l) as t.
  induction H1; simpl in *.
  destruct H1; subst.
  destruct (H b MT); try easy.
  exists x. simpl in *. destruct x.
  constructor; easy.
  apply H0 in H2. contradiction. simpl. left. easy.
  inv Heqt. inv Heqt. exists (r,n). constructor.
  
  
Qed.

Lemma session_progress_1 : 
    forall e rmax t aenv s tenv tenv', @env_state_eq tenv (snd s) -> kind_env_stack aenv (fst s) ->
      @session_system rmax t aenv tenv e tenv' ->
           e = PSKIP \/ (exists e' s', @qfor_sem rmax aenv s e s' e').
Proof.
  intros. induction H1; simpl in *.
  left. easy.
  right. exists ((subst_pexp e x v)).
  exists s. apply let_sem_c; simpl in *; easy.
  right.
  exists e.
  assert (exists v, eval_aexp (fst s) a v).
  
  exists (update_cval s x n).
Admitted.
                                 

Lemma session_progress : 
    forall e rmax t aenv s tenv tenv1 tenv', @env_state_eq tenv (snd s) ->
      @env_equiv tenv tenv1 ->
      @session_system rmax t aenv tenv1 e tenv' ->
           e = PSKIP \/ (exists e' s1 s', @state_equiv rmax (snd s) s1 -> @qfor_sem rmax aenv (fst s,s1) e s' e').
Proof. Admitted.




