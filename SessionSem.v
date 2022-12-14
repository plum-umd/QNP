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

(* functions for defining boolean. *)
Inductive eval_cbexp : stack -> cbexp -> bool -> Prop :=
    | ceq_sem : forall s x y r1 n1 r2 n2, eval_aexp s x (r1,n1) -> eval_aexp s y (r2,n2) -> eval_cbexp s (CEq x y) (n1 =? n2)
    | clt_sem : forall s x y r1 n1 r2 n2, eval_aexp s x (r1,n1) -> eval_aexp s y (r2,n2) -> eval_cbexp s (CLt x y) (n1 <? n2).

Check xorb.

Fixpoint eval_eq_bool (f:nat -> C * rz_val) (m size v:nat) :=
  match m with 0 => f
           | S m' => update (eval_eq_bool f m' size v) m' 
                   (fst (f m'),update (snd (f m')) size (xorb ((a_nat2fb (snd (f m')) size) =? v) ((snd (f m')) size)))
  end.

Fixpoint eval_lt_bool (f:nat -> C * rz_val) (m size v:nat) :=
  match m with 0 => f
           | S m' => update (eval_lt_bool f m' size v) m' 
                   (fst (f m'),update (snd (f m')) size (xorb ((a_nat2fb (snd (f m')) size) <? v) ((snd (f m')) size)))
  end.

Fixpoint eval_rlt_bool (f:nat -> C * rz_val) (m size v:nat) :=
  match m with 0 => f
           | S m' => update (eval_rlt_bool f m' size v) m' 
                   (fst (f m'),update (snd (f m')) size (xorb (v <? (a_nat2fb (snd (f m')) size)) ((snd (f m')) size)))
  end.

Fixpoint grab_bool_elem (f:nat -> C * rz_val) (m i size:nat) (acc:nat -> C * rz_val) :=
  match m with 0 => (i,acc)
           | S m' => if (snd (f m')) size then 
                  grab_bool_elem f m' (i+1) size (update acc i (f m'))
                else grab_bool_elem f m' i size acc
   end.
Definition grab_bool f m size := grab_bool_elem f m 0 size (fun _ => (C0,allfalse)).

Inductive eval_bexp {rmax:nat} {env:aenv}: state -> bexp -> state -> Prop :=
    | beq_sem_1 : forall s s' x y z i l n t m f, AEnv.MapsTo x (QT n) env -> AEnv.MapsTo z (QT t) env ->
                @find_state rmax s ((x,BNum 0,BNum n)::[(z,BNum i,BNum (S i))]) 
                                (Some (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f)) ->
                   @up_state rmax s ((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l) (Cval m (eval_eq_bool f m n y)) s'
                   -> eval_bexp s (BEq (BA x) ((Num y)) z (Num i)) s'
    | beq_sem_2 : forall s s' x y z i l n t m f, AEnv.MapsTo x (QT n) env -> AEnv.MapsTo z (QT t) env ->
                @find_state rmax s ((x,BNum 0,BNum n)::[(z,BNum i,BNum (S i))]) 
                                (Some (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f)) ->
                   @up_state rmax s ((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l) (Cval m (eval_eq_bool f m n y)) s'
                   -> eval_bexp s (BEq ((Num y)) (BA x) z (Num i)) s'
    | blt_sem_1 : forall s s' x y z i l n t m f, AEnv.MapsTo x (QT n) env -> AEnv.MapsTo z (QT t) env ->
                @find_state rmax s ((x,BNum 0,BNum n)::[(z,BNum i,BNum (S i))]) 
                                (Some (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f)) ->
                   @up_state rmax s ((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l) (Cval m (eval_lt_bool f m n y)) s'
                   -> eval_bexp s (BLt (BA x) ((Num y)) z (Num i)) s'
    | blt_sem_2 : forall s s' x y z i l n t m f, AEnv.MapsTo x (QT n) env -> AEnv.MapsTo z (QT t) env ->
                @find_state rmax s ((x,BNum 0,BNum n)::[(z,BNum i,BNum (S i))]) 
                                (Some (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f)) ->
                   @up_state rmax s ((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l) (Cval m (eval_rlt_bool f m n y)) s'
                   -> eval_bexp s (BEq ((Num y)) (BA x) z (Num i)) s'
    | btext_sem : forall s z i, eval_bexp s (BTest z (Num i)) s.

Inductive assem_elem : nat -> nat -> rz_val -> (nat-> C * rz_val) -> list nat -> Prop :=
    assem_elem_0 : forall size c f, assem_elem 0 size c f nil
  | assem_elem_st : forall size c f m l, assem_elem m size c f l -> cut_n (snd (f m)) size = c
                 -> assem_elem (S m) size c f (m::l)
  | assem_elem_sf : forall size c f m l, assem_elem m size c f l -> cut_n (snd (f m)) size <> c
                 -> assem_elem (S m) size c f l.

Fixpoint assem_list (i:nat) (s:list nat) (f: nat -> C * rz_val) (acc:nat -> C*rz_val) :=
    match s with nil => (i,acc) 
              | (a::l) => (assem_list (i+1) l f (update acc i (f a)))
    end.

Inductive assem_bool : nat -> nat -> nat -> (nat -> C * rz_val) -> (nat -> C * rz_val) -> (nat * (nat -> C*rz_val)) -> Prop :=
    assem_bool_0: forall m' size f f', assem_bool 0 m' size f f' (0,fun _ => (C0,allfalse))
  | assem_bool_sf: forall n i m' size f f' acc, assem_bool n m' size f f' (i,acc) ->
               assem_elem m' size (cut_n (snd (f n)) size) f' nil -> 
               assem_bool (S n) m' size f f' (i+1, update acc i (f n))
  | assem_bool_st: forall n i l m' size f f' acc, assem_bool n m' size f f' (i,acc) ->
               assem_elem m' size (cut_n (snd (f n)) size) f' l -> l <> nil ->
               assem_bool (S n) m' size f f' (assem_list i l f' acc).

Fixpoint subst_qstate (l:qstate) (x:var) (n:nat) :=
  match l with nil => nil
          | (y,v)::yl => (subst_session y x n,v)::(subst_qstate yl x n)
  end.
Definition subst_state (l:state) (x:var) n := (fst l,subst_qstate (snd l) x n).


(* defining diffusion. *)
Fixpoint sum_c_list (l:list nat) (f: nat -> C * rz_val) :=
   match l with nil => C0
              | a::xl => (fst (f a) + sum_c_list xl f)%C
   end.
Definition cal_fc (l:list nat) (f:nat -> C*rz_val) (n:nat) :=
     ((1/(2^(n-1)))%R * (sum_c_list l f))%C.

Fixpoint trans_nat (l:list nat) (f:nat -> C*rz_val) (size:nat) :=
  match l with nil => nil
       | a::xl => (a_nat2fb (snd (f a)) size, fst (f a)):: trans_nat xl f size
  end.

Fixpoint find_c (l:list (nat * C)) (a:nat) :=
   match l with nil => None
       | ((x,y)::xl) => if x =? a then Some y else find_c xl a
   end.

Definition merge_two (n:nat) (c:rz_val) (size:nat) :=
   fun i => if i <? size then (nat2fb n) i else c i.

Fixpoint assem_dis (l:list (nat * C)) (c:rz_val) (f:nat -> C*rz_val) (sum:C) (size:nat) (i:nat) (n:nat) :=
   match n with 0 => f
             | S m => match find_c l m with None 
                      => assem_dis l c (update f i (sum,merge_two m c size)) sum size (i+1) m
                         | Some z => assem_dis l c (update f i ((sum - z)%C,merge_two m c size)) sum size (i+1) m
                      end
   end.

Inductive find_same_group : nat -> nat -> nat -> rz_val -> (nat -> C * rz_val) -> list nat -> Prop :=
   find_same_group_0 : forall pos size c f, find_same_group 0 pos size c f nil
  | find_same_group_st: forall n pos size c f l, find_same_group n pos size c f l -> 
       cut_n (lshift_fun (snd (f n)) pos) size = c -> find_same_group (S n) pos size c f (n::l)
  | find_same_group_sf: forall n pos size c f l, find_same_group n pos size c f l -> 
       cut_n (lshift_fun (snd (f n)) pos) size <> c -> find_same_group (S n) pos size c f l.

Inductive dis_sem : nat -> nat -> nat -> nat -> (nat -> C * rz_val) -> (list nat) -> (nat * (nat -> C * rz_val)) -> Prop :=
   dis_sem_0 : forall pos size n f l, dis_sem pos size n 0 f l (0,fun _ => (C0,allfalse))
  | dis_sem_sf: forall pos size n m f l acc, dis_sem pos size n m f l acc -> In m l -> dis_sem pos size n (S m) f l acc
  | dis_sem_st: forall pos size n m f l acc la, dis_sem pos size n m f (la++l) acc -> ~ In m l ->
             find_same_group pos size n (cut_n (lshift_fun (snd (f m)) pos) size) f la ->
         dis_sem pos size n (S m) f l
          (fst acc+2^pos,assem_dis (trans_nat la f pos) (snd (f m)) (snd acc) (sum_c_list la f) pos (fst acc) (2^pos)).

Inductive qfor_sem {rmax:nat}
           : aenv -> state -> pexp -> state -> pexp -> Prop :=
  | state_eq_sem: forall aenv e s f f', @state_equiv rmax f f' -> qfor_sem aenv (s,f) e (s,f') e
  | let_sem_c : forall aenv s x a n e, simp_aexp a = Some n 
        -> qfor_sem aenv s (Let x (AE a) e) s (subst_pexp e x n)
  | let_sem_m : forall aenv s x a n e, eval_aexp (fst s) a n 
             -> qfor_sem aenv s (Let x (AE a) e) (update_cval s x n) e
  | let_sem_q : forall aenv s s' x a n e r v, AEnv.MapsTo x (QT n) aenv ->
                       @pick_mea rmax s a n (r,v) -> @mask_state rmax ([(a,BNum 0,BNum n)]) v (snd s) s'
                  -> qfor_sem (AEnv.add x (Mo MT) aenv) s (Let x (Meas a) e) (update_cval (fst s,s') x (r,v)) e
  | appsu_sem_h_nor : forall aenv s s' p a b, @simp_varia aenv p a -> @find_state rmax s ([a]) (Some (([a]),Nval (C1) b)) -> 
                @up_state rmax s ([a]) (Hval (fun i => (update allfalse 0 (b i)))) s' -> qfor_sem aenv s (AppSU (RH p)) s PSKIP
  | appsu_sem_h_had : forall aenv s s' p a b, @simp_varia aenv p a -> @find_state rmax s ([a]) (Some (([a]),Hval b)) ->
           (@up_state rmax s ([a]) (Nval C1 (fun j => b j 0)) s') -> qfor_sem aenv s (AppSU (RH p)) s' PSKIP
  (* rewrite the tenv type for oqasm with respect to the ch list type. *)
  | appu_sem_nor : forall aenv s s' a e l r b ra ba, @find_state rmax s a (Some (a++l,Nval r b)) ->
      eval_nor rmax aenv a r b e = Some (ra,ba) -> (@up_state rmax s (a++l) (Nval ra ba) s') -> qfor_sem aenv s (AppU a e) s' PSKIP
  | appu_sem_ch : forall aenv s s' a e l b m ba, @find_state rmax s a (Some (a++l,Cval m b)) ->
        eval_ch rmax aenv a m b e = Some ba -> (@up_state rmax s (a++l) (Cval m ba) s') -> qfor_sem aenv s (AppU a e) s' PSKIP
  | seq_sem_1: forall aenv e1 e1' e2 s s1 s2, e1 <> PSKIP -> qfor_sem aenv s e1 s1 e1' -> qfor_sem aenv s (PSeq e1 e2) s2 (PSeq e1' e2)
  | seq_sem_2: forall aenv e2 s, qfor_sem aenv s (PSeq PSKIP e2) s e2
  | if_sem_ct : forall aenv M s b e, eval_cbexp M b true -> qfor_sem aenv (M,s) (If (CB b) e) (M,s) e
  | if_sem_cf : forall aenv M s b e, eval_cbexp M b false -> qfor_sem aenv (M,s) (If (CB b) e) (M,s) PSKIP
  | if_sem_q_1 : forall aenv l l1 n n' s s' sa sa' sac b e e' m m' f f' fc fc' fa,
               type_bexp aenv b (QT (n+1),l) -> @eval_bexp rmax aenv s b s' ->
                @find_state rmax s' l (Some (l++l1, Cval m f)) -> ses_len l1 = Some n' ->
                 mut_state 0 (n+1) n' (Cval (fst (grab_bool f m n)) (snd (grab_bool f m n))) fc ->
                @up_state rmax s' (l++l1) fc sa -> qfor_sem aenv sa e sa' e' -> e <> PSKIP ->
                 @find_state rmax sa' l1 (Some (l1, fc')) -> mut_state 0 n' (n+1) fc' (Cval m' f') ->
                assem_bool m m' (n+1) f f' fa -> @up_state rmax s (l++l1) (Cval (fst fa) (snd fa)) sac ->
                    qfor_sem aenv s (If b e) sac (If b e')
  | if_sem_q_2 : forall aenv s b, qfor_sem aenv s (If b PSKIP) s PSKIP
  | for_0 : forall aenv s x l h b p, h <= l -> qfor_sem aenv s (For x (Num l) (Num h) b p) s PSKIP
  | for_s : forall aenv s x l h b p, l < h -> 
          qfor_sem aenv s (For x (Num l) (Num h) b p) s (PSeq (If b p) (For x (Num (l+1)) (Num h) b p))
  | diffuse_a: forall aenv s s' x n l n' l1 m f m' acc, type_vari aenv x (QT n,l) ->
                @find_state rmax s l (Some (l++l1, Cval m f)) -> ses_len l1 = Some n' ->
                dis_sem n n' m m f nil (m',acc) ->  @up_state rmax s (l++l1) (Cval m' acc) s' ->
                qfor_sem aenv s (Diffuse x) s' PSKIP.


(*

Inductive session_system {rmax:nat}
           : atype -> aenv -> type_map -> pexp -> type_map -> Prop :=

Inductive qfor_sem {rmax:nat}
           : aenv -> state -> pexp -> state -> Prop :=

*)

