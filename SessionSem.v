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
    | mnum_sem: forall s r n, eval_aexp s (MNum r n) (r,n)
    | aplus_sem: forall s e1 e2 r n1 n2, eval_aexp s e1 (r,n1) -> eval_aexp s e2 (1%R,n2) -> eval_aexp s (APlus e1 e2) (r,n1 + n2)
    | amult_sem: forall s e1 e2 r n1 n2, eval_aexp s e1 (r,n1) -> eval_aexp s e2 (1%R,n2) -> eval_aexp s (AMult e1 e2) (r,n1 * n2). 

Inductive simp_varia : aenv -> varia -> range -> Prop :=
    | aexp_sem : forall env x n, AEnv.MapsTo x (QT n) env -> simp_varia env (AExp (BA x)) (x,BNum 0, BNum n)
    | index_sem : forall env x v, simp_varia env (Index x (Num v)) (x,BNum v,BNum (v+1)).

(* This is the semantics for basic gate set of the language. *)
Definition id_qenv : (var -> nat) := fun _ => 0.

Fixpoint compile_exp_to_oqasm (e:exp) :(option OQASM.exp) :=
   match e with SKIP x (Num v) => Some (OQASM.SKIP (x,v))
              | X x (Num v) => Some (OQASM.X (x,v))
              | CU x (Num v) e => 
        match compile_exp_to_oqasm e with None => None
                                       | Some e' => Some (OQASM.CU (x,v) e')
        end
              | RZ q x (Num v) => Some (OQASM.RZ q (x,v))
              | RRZ q x (Num v) => Some (OQASM.RRZ q (x,v))
              | SR q x => Some (OQASM.SR q x)
              | SRR q x => Some (OQASM.SRR q x)
              | Lshift x => Some (OQASM.Lshift x)
              | Rshift x => Some (OQASM.Rshift x)
              | Rev x => Some (OQASM.Rev x)
              | QFT x v => Some (OQASM.QFT x v)
              | RQFT x v => Some (OQASM.RQFT x v)
              | Seq e1 e2 =>
        match compile_exp_to_oqasm e1 with None => None
                       | Some e1' =>       
           match compile_exp_to_oqasm e2 with None => None
                        | Some e2' => Some (OQASM.Seq e1' e2')
           end
        end
           | _ => None
   end.

Fixpoint var_in_list (l : list var) (a:var) := 
    match l with nil => false
         | (x::xl) => (x =? a) && (var_in_list xl a)
   end.

Fixpoint compile_ses_qenv (env:aenv) (l:session) : ((var -> nat) * list var) :=
   match l with nil => (id_qenv,nil)
       | ((x,a,b)::xl) => match AEnv.find x env with
              Some (QT n) =>
              match compile_ses_qenv env xl with (f,l) => 
                 if var_in_list l x then (f,l) else (fun y => if y =? x then n else f y,x::l)
                end
            | _ => compile_ses_qenv env xl
             end
   end.

Fixpoint compile_range_state (n st i:nat) (x:var) (b: rz_val) (f:posi -> val) :=
    match n with 0 => f
            | S m => (compile_range_state m st i x b f)[(x,st+m) |-> (nval (b (i+m)) allfalse)]
    end.

Fixpoint compile_ses_state' (i:nat) (l:session) (b:rz_val) :=
   match l with nil => (fun _ => nval false allfalse)
           | ((x,BNum l,BNum r)::xl) => compile_range_state (r-l) l i x b (compile_ses_state' (i+(r-l)) xl b)
           | (_::xl) => compile_ses_state' i xl b
   end.
Definition compile_ses_state (l:session) (b:rz_val) := compile_ses_state' 0 l b.

Fixpoint turn_oqasm_range (rmax n st i:nat) (x:var) (f:posi -> val) (r:rz_val) (b: rz_val) : option (rz_val * rz_val) :=
    match n with 0 => Some (r,b)
            | S m => match (turn_oqasm_range rmax m st i x f r b)
         with None => None
         | Some (r',b') => match f (x,st+m) with nval ba ra => Some (n_rotate rmax ra r', update b' (i+m) ba)
                                             | _ => None
                            end
               end
    end.

Fixpoint turn_oqasm_ses' (rmax i:nat) (l:session) (f:posi -> val) (b:rz_val) :=
   match l with nil => Some (allfalse, b)
           | ((x,BNum l,BNum r)::xl) => 
               match turn_oqasm_ses' rmax (i+(r-l)) xl f b with None => None
               | Some (ra,ba) => turn_oqasm_range rmax (r-l) l i x f ra ba
               end
           | _ => None
   end.
Definition turn_oqasm_ses rmax (l:session) (f:posi -> val) b  := turn_oqasm_ses' rmax 0 l f b.

Definition cover_n (f:rz_val) (n:nat) := fun i => if i <? n then false else f i.

Definition eval_nor (rmax:nat) (env:aenv) (l:session) (r:C) (b:rz_val) (e:exp) :=
   match compile_ses_qenv env l with (f,ss) =>
       match compile_exp_to_oqasm e with
                None => None
              | Some e' => 
       match ses_len l with None => None
            | Some na => 
           match turn_oqasm_ses rmax l (exp_sem f e' (compile_ses_state l b)) (cover_n b na)
                with None => None
                  | Some (ra,ba) => Some ((r* (Cexp (2*PI * (turn_angle ra rmax))))%C, ba)
           end
            end
       end
     end.

Fixpoint eval_ch (rmax:nat) (env:aenv) (l:session) (m:nat) f (e:exp) :=
   match m with 0 => Some (fun _ => (C0 , allfalse))
          | S n => match eval_nor rmax env l (fst (f n)) (snd (f n)) e with None => None
              | Some (ra,ba) => match eval_ch rmax env l n f e with None => None
                 | Some fa => Some (update fa n (ra , ba))
            end
          end
   end.

Inductive qfor_sem {rmax:nat}
           : aenv -> state -> pexp -> state -> Prop :=
  | state_eq_sem: forall aenv e s f f', @state_equiv rmax f f' -> qfor_sem aenv (s,f) e (s,f')
  | skip_sem: forall aenv s, qfor_sem aenv s PSKIP s
  | let_sem_c : forall aenv s s' x a n e, simp_aexp a = Some n 
        -> qfor_sem aenv s (subst_pexp e x n) s' -> qfor_sem aenv s (Let x (AE a) e) s'
  | let_sem_m : forall aenv s s' x a n e, eval_aexp (fst s) a n -> qfor_sem (AEnv.add x (Mo MT) aenv) (update_cval s x n) e s'
             -> qfor_sem aenv s (Let x (AE a) e) s'
  | let_sem_q : forall aenv s s' s'' x a n e r v, AEnv.MapsTo x (QT n) aenv ->
                       @pick_mea rmax s a n (r,v) -> @mask_state rmax ([(a,BNum 0,BNum n)]) v (snd s) s' ->
            qfor_sem (AEnv.add x (Mo MT) aenv) (update_cval (fst s,s') x (r,v)) e s''
                  -> qfor_sem aenv s (Let x (Meas a) e) s''
  | appsu_sem_h_nor : forall aenv s s' p a b, @simp_varia aenv p a -> @find_state rmax s ([a]) (Some (([a]),Nval (C1) b)) -> 
                @up_state rmax s ([a]) (Hval (fun i => (update allfalse 0 (b i)))) s' -> qfor_sem aenv s (AppSU (RH p)) s

  | appsu_sem_h_had : forall aenv s s' p a b, @simp_varia aenv p a -> @find_state rmax s ([a]) (Some (([a]),Hval b)) ->
           (@up_state rmax s ([a]) (Nval C1 (fun j => b j 0)) s') -> qfor_sem aenv s (AppSU (RH p)) s'
  (* rewrite the tenv type for oqasm with respect to the ch list type. *)
  | appu_sem_nor : forall aenv s s' a e l r b ra ba, @find_state rmax s a (Some (a++l,Nval r b)) ->
                 eval_nor rmax aenv a r b e = Some (ra,ba) -> 
           (@up_state rmax s (a++l) (Nval ra ba) s') -> qfor_sem aenv s (AppU a e) s'
  | appu_sem_ch : forall aenv s s' a e l b m ba, @find_state rmax s a (Some (a++l,Cval m b)) ->
                 eval_ch rmax aenv a m b e = Some ba -> 
           (@up_state rmax s (a++l) (Cval m ba) s') -> qfor_sem aenv s (AppU a e) s'
  | seq_sem: forall aenv e1 e2 s s1 s2, qfor_sem aenv s e1 s1 -> qfor_sem aenv s1 e2 s2 -> qfor_sem aenv s (PSeq e1 e2) s2.
  | if_sem_1 : forall aenv l x n v v' v'' c e M M' s s' s'', type_pexp qenv aenv e (Ses l) -> add_one_ch rmax v v' (c 0) = Some v''
                -> qfor_sem aenv (M,(l,v)::s) e (M',(l,v')::s') -> @find_state rmax (M,s) ([(x,n,S n)]) (Some (([(x,n,S n)]),Hval c))
         -> @up_state rmax (M',s') ((x,n,S n)::l) v'' s'' -> qfor_sem aenv (M,(l,v)::s) (If (BTest x (Num n)) e) s''
  | if_sem_2 : forall aenv l l1 b x n v v' va c v'' e M M' s s' s'', type_pexp qenv aenv e (Ses l) -> type_bexp aenv b (Ses ((x,n,S n)::l1))
                -> merge_one_ch rmax v v' va (c 0) = Some v'' -> is_core_var b x n -> @find_state rmax (M,s) ((x,n,S n)::l1) (Some (l1,va))
                -> @find_state rmax (M,s) ([(x,n,S n)]) (Some (([(x,n,S n)]),Nval c))
                -> qfor_sem aenv (M,(l,v)::s) e (M',(l,v')::s')
         -> @up_state rmax (M',s') ((x,n,S n)::l) v'' s'' -> qfor_sem aenv (M,(l,v)::s) (If b e) s''.


Inductive eval_aexp : stack -> aexp -> (R * nat) -> Prop :=
    | var_sem : forall s x r n, AEnv.MapsTo x (r,n) s -> eval_aexp s (BA x) (r,n)
    | num_sem : forall s n, eval_aexp s (Num n) (1%R,n)
    | aplus_sem: forall s e1 e2 r n1 n2, eval_aexp s e1 (r,n1) -> eval_aexp s e2 (1%R,n2) -> eval_aexp s (APlus e1 e2) (r,n1 + n2)
    | amult_sem: forall s e1 e2 r n1 n2, eval_aexp s e1 (r,n1) -> eval_aexp s e2 (1%R,n2) -> eval_aexp s (AMult e1 e2) (r,n1 * n2). 



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



