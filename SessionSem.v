Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import QWhileSyntax.
Require Import SessionDef.
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

Inductive eval_aexp : stack -> aexp -> (R * nat) -> Prop :=
    | var_sem : forall s x r n, AEnv.MapsTo x (r,n) s -> eval_aexp s (BA x) (r,n)
    | num_sem : forall s n, eval_aexp s (Num n) (1%R,n)
    | aplus_sem: forall s e1 e2 r n1 n2, eval_aexp s e1 (r,n1) -> eval_aexp s e2 (1%R,n2) -> eval_aexp s (APlus e1 e2) (r,n1 + n2)
    | amult_sem: forall s e1 e2 r n1 n2, eval_aexp s e1 (r,n1) -> eval_aexp s e2 (1%R,n2) -> eval_aexp s (AMult e1 e2) (r,n1 * n2). 

Inductive simp_varia {qenv: var -> nat}: varia -> (var * nat * nat) -> Prop :=
    | aexp_sem : forall x, simp_varia (AExp (BA x)) (x,0,qenv x)
    | index_sem : forall x v, simp_varia (Index x (Num v)) (x,v,v+1).

Inductive qfor_sem  {qenv: var -> nat} {rmax:nat}
           : aenv -> state -> pexp -> state -> Prop :=
  | skip_sem: forall aenv s, qfor_sem aenv s PSKIP s
  | let_sem_c : forall aenv s s' x a n e, simp_aexp a = Some n -> qfor_sem aenv s (subst_pexp e x n) s' -> qfor_sem aenv s (Let x (AE a) CT e) s'
  | let_sem_m : forall aenv s s' x a n e, eval_aexp (fst s) a n -> qfor_sem (AEnv.add x (AType MT) aenv) (update_cval s x n) e s'
             -> qfor_sem aenv s (Let x (AE a) MT e) s'
  | let_sem_q : forall aenv s s' s'' x a e r v, @pick_mea rmax s a (qenv a) (r,v) -> @mask_state rmax ([(a,0,qenv a)]) v (snd s) s' ->
            qfor_sem (AEnv.add x (AType MT) aenv) (update_cval (fst s,s') x (r,v)) e s''
                  -> qfor_sem aenv s (Let x (Meas a) MT e) s''
  | appsu_sem_h_nor : forall aenv s s' p a b, @simp_varia qenv p a -> @find_state rmax s ([a]) (Some (([a]),Nval b)) -> 
                @up_state rmax s ([a]) (Hval (fun i => (update allfalse 0 (b i)))) s' -> qfor_sem aenv s (AppSU (RH p)) s
  | appsu_sem_h_had : forall aenv s s' p a b, @simp_varia qenv p a -> @find_state rmax s ([a]) (Some (([a]),Hval b)) ->
           (@up_state rmax s ([a]) (Nval (fun j => b j 0)) s') -> qfor_sem aenv s (AppSU (RH p)) s'
  (* rewrite the tenv type for oqasm with respect to the ch list type. *)
  | appu_sem : forall aenv s a e,  qfor_sem aenv s (AppU a e) s
  | seq_sem: forall aenv e1 e2 s s1 s2, qfor_sem aenv s e1 s1 -> qfor_sem aenv s1 e2 s2 -> qfor_sem aenv s (PSeq e1 e2) s2.
  | if_sem : forall aenv l1 l2 b e s s', type_pexp qenv aenv e (Ses l1) -> type_bexp aenv b (Ses l2) 
                -> qfor_sem aenv s e s'
     (*TODO: rewrite Fval state design, instead of function, we use list. 
        for every items in the s whose session is l1++l2, the result is 
              s[l1++l2 |-> ori_l1 ++ if s(l1) = true then s(l2)_of_l1 update to s'; otherwise s ] *)
           -> qfor_sem aenv s (If b e) s.




