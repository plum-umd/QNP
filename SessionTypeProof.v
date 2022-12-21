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

Inductive env_state_eqv {r:nat} : type_map -> qstate ->  Prop :=
    env_state_eqv_rule : forall l1 l2 l1' l2', 
      env_equiv l1 l1' -> @state_equiv r l2 l2' -> env_state_eq l1' l2' -> env_state_eqv l1 l2.


Lemma session_progress_1 : 
    forall e rmax t aenv s tenv tenv', @env_state_eqv rmax tenv (snd s) ->
      @session_system rmax t aenv tenv e tenv' ->
           e = PSKIP \/ (exists e' s', @qfor_sem rmax aenv s e s' e' /\ @env_state_eqv rmax tenv' (snd s')).
Proof.
  intros. induction H0. destruct IHsession_system as [X1 | X2];subst.
  destruct s; simpl in *. inv H.
  (* env_equiv T2 l1' *)
  (* env_state_eqv T2 q0 *)
  
Admitted.
(*

Inductive session_system {rmax:nat}
           : atype -> aenv -> type_map -> pexp -> type_map -> Prop :=

Inductive qfor_sem {rmax:nat}
           : aenv -> state -> pexp -> state -> Prop :=

*)

