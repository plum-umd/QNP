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

(* Type system -- The Static Type system, and the dynamic gradual typing part will be merged with the triple rule. *)

(* Type system for oqasm. *)


Definition bits := list bool.

Definition get_cus (n:nat) (f:posi -> val) (x:var) := 
          fun i => if i <? n then (match f (x,i) with nval b r => b | _ => false end) else allfalse i.

Definition rotate (r :rz_val) (q:nat) := addto r q.

Definition times_rotate (v : val) (q:nat) := 
     match v with nval b r => if b then nval b (rotate r q) else nval b r
                  | qval rc r =>  qval rc (rotate r q)
     end.

Fixpoint sr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (sr_rotate' st x m size)[(x,m) |-> times_rotate (st (x,m)) (size - m)]
   end.
Definition sr_rotate st x n := sr_rotate' st x (S n) (S n).

Definition r_rotate (r :rz_val) (q:nat) := addto_n r q.

Definition tenv : Type := (session * rz_val). 
    (* varaible -> global phase rz_val : nat -> bool (nat), nat -> bool (nat) |0010101> *)
Definition look_tenv (env:tenv) (x:posi) := (snd env) (find_pos x (fst env)).
Definition look_range (env:tenv) (x:var) :=
      match find_range x (fst env) with None => None
              | Some pos => Some (lshift_fun (cut_n (snd env) (snd pos)) (fst pos))
      end.
Definition up_range (env:tenv) (x:var) (f:rz_val) :=
    match find_range x (fst env) with None => env
             | Some pos =>
         (fst env, fun i => if i <? (fst pos) then (snd env) i 
                            else if ((fst pos) <=? i) && (i <? snd pos)
                            then f i else (snd env) i)
    end.

Definition flip_i (l:rz_val) (i:nat) := update l i (negb (l i)).
Definition exchange (env:tenv) (p:posi) :=
    let pos := (find_pos p (fst env)) in (fst env, flip_i (snd env) pos).

Definition up_phase_phi (tenv:tenv) (x:var) (n:nat) :=
  match look_range tenv x with None => None
          | Some f => Some (up_range tenv x (rotate f n)) end.

Definition up_phase_phi_r (tenv:tenv) (x:var) (n:nat) :=
  match look_range tenv x with None => None
          | Some f => Some (up_range tenv x (r_rotate f n)) end.

(*
Definition up_phase (tenv:tenv) (x:var) (q:nat) :=
  match tenv x with (r,l) => update tenv x (rotate r q,l) end.

Definition up_phase_r (tenv:tenv) (x:var) (q:nat) :=
  match tenv x with (r,l) => update tenv x (r_rotate r q,l) end.

Definition up_phase_phi (tenv:tenv) (x:var) (n:nat) :=
  match tenv x with (r,q) => update tenv x (r, (rotate q n)) end.

Definition up_phase_phi_r (tenv:tenv) (x:var) (n:nat) :=
  match tenv x with (r, q) => update tenv x (r, (r_rotate q n)) end.

Fixpoint list_in (l:list var) (x:var) := match l with [] => false | (y::yl) => if x =? y then true else list_in yl x end.

Definition list_subset (al bl :list var) := (forall x, In x al -> In x bl).
*)

Fixpoint oqasm_type (qenv: var -> nat) (tv:tenv) (e:exp) :=
   match e with SKIP x a => Some tv
              | (X x (Num v)) => Some (exchange tv (x,v))
              | (CU x (Num v) e) => if look_tenv tv (x,v) then oqasm_type qenv tv e else Some tv
              | (RZ q x (Num v)) => Some tv
              | (RRZ q x (Num v)) => Some tv
              | (SR n x) => (up_phase_phi tv x (S n))
              | (SRR n x) => (up_phase_phi_r tv x (S n))
              | (QFT x b) => Some tv
              | RQFT x b => Some tv
              | Seq s1 s2 => match oqasm_type qenv tv s1 with Some tv1 => oqasm_type qenv tv1 s2 | _ => None end
              | _ => Some tv
   end.

Definition gen_ch_set (qenv: var -> nat) (st:nat -> rz_val) (s:session) (e:exp) :=
    fun i => match oqasm_type qenv (s, (st i)) e
             with Some tv => snd tv
                | None => allfalse
             end.

Definition double_type (m:nat) (t t': type_cfac) :=
   fun i => if i <? m then (fb_push false (t i)) else fb_push true (t' (i-m)).

Definition get_core_ses (b:bexp) :=
    match b with BEq c d x (Num v) => Some (x,v,v+1)
               | BLt c d x (Num v) => Some (x,v,v+1)
               | _ => None
    end.

Definition eval_bexp_set (b:bexp) (y:var) (v:nat) :=
    match b with BEq (AExp (BA x)) (AExp (Num a)) i t => if x =? y then Some (v =? a) else None
               | BLt (AExp (BA x)) (AExp (Num a)) i t => if x =? y then Some (v <? a) else None
               | _ => None
    end.

Definition form_bits (n:nat) (t t':rz_val) (a:bool) := 
               fun i => if i <? n then t i else fb_push a t' (i-n).

Definition flat_type (x:var) (n:nat) (b:bexp) (a:bool) (t t': type_cfac) :=
   fun i => match eval_bexp_set b x (a_nat2fb (t i) n)
        with None => allfalse
           | Some true => if a then form_bits n (t i) (lshift_fun (t' i) n) a
                               else form_bits n (t i) (lshift_fun (t i) n) (negb a)
           | Some false => if a then form_bits n (t i) (lshift_fun (t i) n) (negb a)
                                else form_bits n (t i) (lshift_fun (t' i) n) a
        end.

Definition gen_diff_set (n:nat) (size:nat) (c:rz_val) :=
   fun i => if i <? n then (fun j => if j <? size then (nat2fb i) j else c j) else allfalse.

Fixpoint add_elem_set' (m size n:nat) (acc:type_cfac) (c:rz_val) :=
    match m with 0 => (size+1,update acc size c)
              | S i => if a_nat2fb (acc i) n =? a_nat2fb c n then (size,acc) else add_elem_set' i size n acc c
    end.
Definition add_elem_set (n:nat) (acc:nat*type_cfac) (c:rz_val) := add_elem_set' (fst acc) (fst acc) n (snd acc) c.

Fixpoint add_n_elems (n:nat) (size:nat) (acc:nat * type_cfac) (addt:type_cfac) :=
   match n with 0 => acc
             | S i => add_n_elems i size (add_elem_set size acc (addt i)) addt
   end.

Fixpoint cal_set' (m:nat) (n:nat) (size:nat) (c:type_cfac) (acc:nat * type_cfac) :=
   match m with 0 => acc
            | S i => cal_set' i n size c (add_n_elems (2^n) size acc (gen_diff_set (2^n) n (c i)))
   end.
Definition cal_set (m n size:nat) (c:type_cfac) := cal_set' m n size c (0,fun i => allfalse).


Inductive session_system {qenv: var -> nat} {rmax:nat}
           : atype -> aenv -> type_map -> pexp -> session -> se_type -> Prop :=
    | skip_ses : forall q env T l t, session_system q env T (PSKIP) l t
    | assign_ses_c : forall q env x v e T l t, session_system q env T (subst_pexp e x v) l t
                  -> session_system q env T (Let x (Num v) CT e) l t
    | assign_ses_m1 : forall q env x a e T l t, type_aexp env a MT ->
              session_system q (AEnv.add x (AType MT) env) T e l t -> session_system q env T (Let x a MT e) l t
    | assign_ses_m2 : forall env x y e T T' l t, find_type T ([(y,0,qenv y)]) (Some (([(y,0,(qenv y))]),CH None)) ->
              remove_type T ([(y,0,(qenv y))]) T' ->
              session_system MT (AEnv.add x (AType MT) env) T' e l t -> session_system CT env T (Let x (Meas y) MT e) l t
    | assign_ses_m3 : forall env x y e T T' la l m ta t, find_type T ([(y,0,qenv y)]) (Some ((y,0,qenv y)::la,CH (Some (m,ta)))) ->
              up_type T la (mask_type ([(y,0,qenv y)]) m (qenv y) ta) T' ->
              session_system MT (AEnv.add x (AType MT) env) T' e l t -> session_system CT env T (Let x (Meas y) MT e) l t
    | appu_ses_h_nor:  forall q env T p s n, gen_ses qenv p = Some (s,n)
                  -> find_type T s (Some (s,(TNor (Some allfalse)))) ->
                    session_system q env T (AppSU (RH p)) s ((TH (Some Uni)))
    | appu_ses_h_had:  forall q env T p s n, gen_ses qenv p = Some (s,n) -> 
                 find_type T s (Some (s,(TH (Some Uni)))) ->
                    session_system q env T (AppSU (RH p)) s ((TNor (Some allfalse)))
    | appu_ses_h_ch:  forall q env T p s s' n b, gen_ses qenv p = Some (s,n) -> find_type T s (Some (s',(CH (Some b)))) ->
                    session_system q env T (AppSU (RH p)) s' ((CH None))
    | appu_ses_qft_nor:  forall q env T x, find_type T ([(x,0,qenv x)]) (Some (([(x,0,qenv x)]),(TNor (Some allfalse)))) ->
                    session_system q env T (AppSU (SQFT x)) ([(x,0,qenv x)]) ((TH (Some Uni)))
    | appu_ses_qft_had:  forall q env T x, find_type T ([(x,0,qenv x)]) (Some (([(x,0,qenv x)]),(TH (Some Uni)))) ->
         session_system q env T (AppSU (SRQFT x)) ([(x,0,qenv x)]) ((TNor (Some allfalse)))
    | appu_ses_qft_ch:  forall q env T x b s, find_type T ([(x,0,qenv x)]) (Some (s,(CH (Some b)))) ->
         session_system q env T (AppSU (SQFT x)) s ((CH None))
    | appu_ses_ch:  forall q env T e s s' m b, type_exp qenv env e (Ses s) -> find_type T s (Some (s', (CH (Some (m,b)))))
                -> session_system q env T (AppU s e) s' (CH (Some (m,gen_ch_set qenv b s' e)))
    | appu_ses_ch_1:  forall q env T e s s', type_exp qenv env e (Ses s) -> find_type T s (Some (s', (CH None)))
                -> session_system q env T (AppU s e) s' (CH (None))
    | qif_ses_had : forall q env T x n e m m' s c t t', find_type T ([(x,n,S n)]) (Some (([(x,n,S n)]),TH c)) ->
        find_type T s (Some (s,CH (Some (m,t)))) -> session_system MT env T e s (CH (Some (m',t')))
                    -> session_system q env T (If (BTest x (Num n)) e) ((x,n,S n)::s) (CH (Some (m+m',double_type m t t')))
    | qif_ses_ch: forall q env T a b e x n y m c s' m' c', 
           get_core_ses b = Some (x,n,S n) -> find_type T ([(x,n,S n)]) (Some ([(x,n,S n)],(TNor (Some a)))) ->
           type_bexp env b (Ses ((y,0,qenv y)::[(x,n,S n)])) -> type_pexp qenv env (If b e) (Ses ((y,0,qenv y)::s')) ->
           find_type T ((y,0,qenv y)::s') (Some ((y,0,qenv y)::s',CH (Some (m,c))))
           -> session_system MT env T e ((y,0,qenv y)::s') (CH (Some (m',c')))
         -> session_system q env T (If b e) ((y,0,qenv y)::((x,n,S n)::s')) (CH (Some (m', flat_type y (qenv y) b (a 0) c c')))
    | qfor_ses_ch: forall q env T i l h b e s t, 
        (forall v, l <= v < h -> session_system q env T (If (subst_bexp b i v) (subst_pexp e i v)) s t)
              -> session_system q env T (For i (Num l) (Num h) b e) s t
    | amp_ses_ch: forall q env T x v s t, find_type T ([(x,0,qenv x)]) (Some (s,t)) ->
                 session_system q env T (Amplify x (Num v)) s t
    | dif_ses_ch: forall q env T x s m c, find_type T ([(x,0,qenv x)]) (Some (([(x,0,qenv x)])++s,(CH (Some (m,c))))) ->
                 session_system q env T (Diffuse (AExp (BA x))) (([(x,0,qenv x)])++s)
                           (CH (Some (cal_set m (qenv x) (ses_len (([(x,0,qenv x)])++s)) c))).


