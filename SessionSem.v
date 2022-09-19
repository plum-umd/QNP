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

Definition add_one_ch_aux_1 (rmax m:nat) (v v' : nat -> R * rz_val * rz_val) (c:rz_val) :=
   (fun i => if i <? m then v i else (fst (fst (v' (i-m))), n_rotate rmax c (snd (fst (v' (i-m)))), snd (v' (i-m)))).

Definition add_one_ch_aux_2 (rmax m:nat) (v v' : nat -> C * rz_val) (c:rz_val) :=
   (fun i => if i <? m then v i else (((get_amplitude rmax (1%R) c) + (fst (v' (i-m)%nat)))%C, snd (v' (i-m)))).

Definition add_one_ch (rmax:nat) (v v': state_elem) (c:rz_val) := 
   match (v,v') with (Cval m f,Cval m' f') => Some (Cval (2*m) (add_one_ch_aux_1 rmax m f f' c))
                   | (Fval m f,Fval m' f') => Some (Fval (2*m) (add_one_ch_aux_2 rmax m f f' c))
                   | _ => None
   end.

Definition is_core_var (b:bexp) (x:var) (n:nat) := 
   match b with BEq a b y (Num m) => ((x = y) /\ (n = m))
             | BLt a b y (Num m) => ((x = y) /\ (n = m))
             | _ => False
   end. 

Definition merge_one_ch (rmax:nat) (v1 v2 v3 : state_elem) (b:bool) :=
   match (v1,v2,v3) with (Cval m f,Cval m' f', Cval n f2)
           => Some (Cval (n*m) (fun i => f2 i))
                   | _ => None
   end.

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
  | seq_sem: forall aenv e1 e2 s s1 s2, qfor_sem aenv s e1 s1 -> qfor_sem aenv s1 e2 s2 -> qfor_sem aenv s (PSeq e1 e2) s2
  | if_sem_1 : forall aenv l x n v v' v'' c e M M' s s' s'', type_pexp qenv aenv e (Ses l) -> add_one_ch rmax v v' (c 0) = Some v''
                -> qfor_sem aenv (M,(l,v)::s) e (M',(l,v')::s') -> @find_state rmax (M,s) ([(x,n,S n)]) (Some (([(x,n,S n)]),Hval c))
         -> @up_state rmax (M',s') ((x,n,S n)::l) v'' s'' -> qfor_sem aenv (M,(l,v)::s) (If (BTest x (Num n)) e) s''
  | if_sem_2 : forall aenv l l1 b x n v v' va c v'' e M M' s s' s'', type_pexp qenv aenv e (Ses l) -> type_bexp aenv b (Ses ((x,n,S n)::l1))
                -> merge_one_ch rmax v v' va (c 0) = Some v'' -> is_core_var b x n -> @find_state rmax (M,s) ((x,n,S n)::l1) (Some (l1,va))
                -> @find_state rmax (M,s) ([(x,n,S n)]) (Some (([(x,n,S n)]),Nval c))
                -> qfor_sem aenv (M,(l,v)::s) e (M',(l,v')::s')
         -> @up_state rmax (M',s') ((x,n,S n)::l) v'' s'' -> qfor_sem aenv (M,(l,v)::s) (If b e) s''.



