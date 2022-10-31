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
Require Import SessionType.
Require Import SessionSem.
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

(*
Definition session :Set := (var * nat * nat).
Definition atpred_elem :Type := (list session * se_type).
Definition atpred := list atpred_elem.
*)

(*
TODO: define apply operation with few different applications:
1: switching: mimicing the session position switching equivalence relation.
2. masking: mimicing the partial measurement.
3. oracle function application using oracle semantics.
4. if conditional as entanglement.
5. H/QFT state prepreation.
*)

(*
Inductive sval := ST (x:state_elem) | SV (s:session)
               | Mask (y:sval) (u:nat) (z:aexp) | AppA (x:exp) (y:sval)
               | FSL (e:sval) (l:session) (s:nat)
               | SSL (e:sval) (a:sval) (b:bexp) (l1:session) (l2:session).
*)

Inductive sval := SV (s:session) | Frozen (b:bexp) (s:sval) | Unfrozen (b:bexp) (s:sval) | FM (x:var) (n:nat) (s:sval).

Inductive cpred_elem := PFalse | CP (b:cbexp) | SEq (x:sval) (y:state_elem) | CNeg (b:cbexp).
                             (* x = y|_{u=z} x is a new session from the old y by cutting session u to be value z. *)


Definition cpred := list cpred_elem.
Definition fresh (l:nat) := l +1.

Fixpoint sval_subst_c t x v :=
  match t with SV s => SV (subst_session s x v)
              | Frozen b s => Frozen (subst_bexp b x v) (sval_subst_c s x v)
              | Unfrozen b s => Frozen (subst_bexp b x v) (sval_subst_c s x v)
              | FM y n s => FM y n (sval_subst_c s x v)
  end.

Definition celem_subst_c t x v := 
  match t with PFalse => PFalse 
          | CP b => CP (subst_cbexp b x v)
          | SEq a y => (SEq (sval_subst_c a x v) y)
          | CNeg b => CNeg (subst_cbexp b x v) end.
Fixpoint cpred_subst_c t x v := 
   match t with nil => nil | (a::al) => (celem_subst_c a x v)::(cpred_subst_c al x v) end.


(*
Definition selem_subst_val (s:sval) x v :=
   match s with SeVar y => if x =? y then v else SeVar y 
              | SV y => SV y
   end.

Definition celem_subst_l t x v :=
  match t with PFalse => PFalse 
          | SEq a b => SEq (selem_subst_val a x v) (selem_subst_val b x v) 
          | SMap a b => SMap (selem_subst_val a x v) b
          | a => a end.
*)

Inductive sublist : list var -> aenv -> Prop :=
  sublist_empty : forall l, sublist nil l
 | sublist_many : forall a l1 l2, AEnv.In a l2 -> sublist l1 l2 -> sublist (a::l1) l2.

Fixpoint freeVarsAExp (a:aexp) := match a with BA x => ([x]) | Num n => nil | MNum r n => nil
            | APlus e1 e2 => (freeVarsAExp e1)++(freeVarsAExp e2)
            | AMult e1 e2 => (freeVarsAExp e1)++(freeVarsAExp e2)
  end.
Definition freeVarsVari (a:varia) := match a with AExp x => freeVarsAExp x
            | Index x v => (x::freeVarsAExp v)
  end.
Definition freeVarsCBexp (a:cbexp) := match a with CEq x y => (freeVarsAExp x)++(freeVarsAExp y)
         | CLt x y => (freeVarsAExp x)++(freeVarsAExp y)
  end.
Fixpoint freeVarsBexp (a:bexp) := match a with CB b => (freeVarsCBexp b)
         | BEq x y i a => i::((freeVarsVari x)++(freeVarsVari y)++(freeVarsAExp a))
         | BLt x y i a => i::((freeVarsVari x)++(freeVarsVari y)++(freeVarsAExp a))
         | BTest i a => i::(freeVarsAExp a)
         | BNeg b => freeVarsBexp b
  end.

Fixpoint freeSesSV (a:sval) := match a with SV s => [s]
         | Frozen b s => freeSesSV s
         | Unfrozen b s => freeSesSV s
         | FM x n s => freeSesSV s
  end.

Definition freeSesCElem (a:cpred_elem) := match a with PFalse => nil
         | CP b => nil
         | CNeg b => nil
         | SEq x y => freeSesSV x
  end.

Fixpoint freeSesCPred (a:cpred) := match a with nil => nil | (x::xl) => (freeSesCElem x)++(freeSesCPred xl) end.

Inductive subst_ses_sval : sval -> session -> sval -> sval -> Prop :=
   subst_ses_svt : forall x v, subst_ses_sval (SV x) x v v
   | subst_ses_svf : forall x y v, x <> y -> subst_ses_sval (SV y) x v v
   | subst_ses_fro : forall x v s b v', subst_ses_sval s x v v' -> subst_ses_sval (Frozen b s) x v (Frozen b v')
   | subst_ses_unf : forall x v s b v', subst_ses_sval s x v v' -> subst_ses_sval (Unfrozen b s) x v (Unfrozen b v')
   | subst_ses_fm : forall x v s y n v', subst_ses_sval s x v v' -> subst_ses_sval (FM y n s) x v (FM y n v').

Inductive subst_ses_celem : cpred_elem -> session -> sval -> cpred_elem -> Prop :=
   subst_ses_pf : forall x v, subst_ses_celem PFalse x v PFalse
 | subst_ses_cp : forall b x v, subst_ses_celem (CP b) x v (CP b)
 | subst_ses_cneg : forall b x v, subst_ses_celem (CNeg b) x v (CNeg b)
 | subst_ses_seq: forall a b x v v', subst_ses_sval a x v v' -> subst_ses_celem (SEq a b) x v (SEq v' b).

Inductive subst_ses_cpred : cpred -> session -> sval -> cpred -> Prop :=
   subst_ses_empty: forall x v, subst_ses_cpred nil x v nil
 | subst_ses_many: forall x v a l a' l', subst_ses_celem a x v a' -> subst_ses_cpred l x v l' -> subst_ses_cpred (a::l) x v (a'::l').


Fixpoint ses_in (s:session) (l:list session) :=
  match l with nil => False
       | (a::xl) => ((ses_eq a s) \/ (ses_in s xl))
  end.

Fixpoint ses_sublist (s:list session) (l:list session) :=
  match s with nil => True
       | (a::xl) => ((ses_in a l) \/ (ses_sublist xl l))
  end.

Inductive sval_check : atype -> aenv -> type_map -> sval -> Prop :=
  sval_check_sv: forall g env T s, ses_in s (dom T) -> sval_check g env T (SV s)
 | sval_check_frozen: forall g env T b s, sublist (freeVarsBexp b) env
             -> sval_check g env T s -> sval_check g env T (Frozen b s)
 | sval_check_unfrozen: forall g env T b s, sublist (freeVarsBexp b) env
             -> sval_check g env T s -> sval_check g env T (Unfrozen b s)
 | sval_check_fm: forall g env T x n s, sval_check g env T s -> sval_check g env T (FM x n s).

Inductive pred_check_elem : atype -> aenv -> type_map -> cpred_elem -> Prop :=
   pred_check_f: forall g env T, pred_check_elem g env T (PFalse)
 | pred_check_cb: forall g env T b, sublist (freeVarsCBexp b) env -> pred_check_elem g env T (CP b)
 | pred_check_cneg: forall g env T b, sublist (freeVarsCBexp b) env -> pred_check_elem g env T (CNeg b)
 | pred_check_sv: forall g env T x y, sval_check g env T x -> pred_check_elem g env T (SEq  x y).

Fixpoint pred_check (g:atype) (env:aenv) (T:type_map) (l:cpred) :=
   match l with nil => True | (c::cl) => (pred_check_elem g env T c) \/ (pred_check g env T cl) end.

Fixpoint dom_to_ses (l : list session) :=
  match l with nil => nil
        | (a::al) => a++(dom_to_ses al)
  end.

Definition class_bexp (b:bexp) := match b with CB a => Some a | _ => None end.

Axiom imply : cpred -> cpred -> Prop.

  Inductive triple {rmax:nat} : 
          atype -> aenv -> type_map -> cpred -> pexp -> cpred -> Prop :=
      | triple_comm: forall q env tenv P Q e R, triple q env tenv (Q++P) e R -> triple q env tenv (P++Q) e R
      | triple_frame: forall q env T T' l P Q e R, fv_pexp env e l -> two_ses_dis (dom_to_ses (freeSesCPred R)) l ->
               ses_sub l (dom_to_ses(dom T)) -> triple q env T P e Q -> triple q env (T++T') (P++R) e (Q++R)
      | triple_con: forall q env T T' P P' Q Q' e, imply P P' -> imply Q Q' -> env_equiv T T' -> pred_check q env T' P' ->
                 triple q env T' P' e Q' -> triple q env T P e Q
      | skip_pf: forall q env tenv P, triple q env tenv P PSKIP P
      | let_c_pf: forall q env tenv P x v e Q,
            triple q env tenv P (subst_pexp e x v) Q -> triple q env tenv P (Let x (AE (Num v)) e) Q
      | let_m_pf: forall q env tenv P x a e Q, type_aexp env a (Mo MT,nil) ->
            triple q env tenv (CP (CEq (BA x) a)::P) e Q -> triple q env tenv P (Let x (AE a) e) Q
      | let_q_pf:  forall q env tenv tenv' P P' x y n l e Q, AEnv.MapsTo y (QT n) env
             -> find_type tenv ([(y,BNum 0,BNum n)]) (Some ((y,BNum 0,BNum n)::l,CH)) ->
            subst_ses_cpred P ((y,BNum 0,BNum n)::l) (FM x n (SV l)) P' ->
            up_type tenv l CH tenv' ->
            triple q (AEnv.add x (Mo MT) env) tenv' P' e Q
            -> triple q env tenv P (Let x (Meas y) e) Q
      | apph_pf: forall q env T x n l b, type_vari env x (QT n,l) -> find_type T l (Some (l,TNor)) ->
            triple q env T ([SEq (SV l) (Nval (C1) b)]) (AppSU (RH x)) ([SEq (SV l) (Hval (fun i => (update allfalse 0 (b i))))])
      | appu_pf : forall q env T l l1 m b e ba,  find_type T l (Some (l++l1,CH)) ->
                eval_ch rmax env l m b e = Some ba ->
                triple q env T ([SEq (SV (l++l1)) (Cval m b)]) (AppU l e) ([SEq (SV l) (Cval m ba)])
      | for_pf : forall q env T x l h b p P i, l <= i < h ->
            triple q env T (cpred_subst_c P x i) (If (subst_bexp b x i) (subst_pexp p x i)) (cpred_subst_c P x (i+1)) ->
            triple q env T (cpred_subst_c P x l) (For x (Num l) (Num h) b p) (cpred_subst_c P x h)
      | if_c : forall q env T P Q a b e, class_bexp b = Some a ->
                 triple q env T (CP a::P) e Q -> triple q env T (CNeg a::P) PSKIP Q -> triple q env T P (If b e) Q
      | if_q : forall q env T T' P P' Q Q' b e n l l1, type_bexp env b (QT n,l) -> find_type T l (Some (l++l1,CH)) ->
                  up_type T l1 CH T' -> subst_ses_cpred P (l++l1) (Frozen b (SV l1)) P' -> pred_check q env ([(l1,CH)]) Q' ->
                  triple q env T' P' e (Q++Q') -> triple q env T P (If b e) Q.
      | seq_pf: forall q env tenv tenv' tenv'' N N' N'' P R Q e1 e2,
             @session_system qenv rmax q env tenv e1 tenv' -> up_types tenv tenv' tenv'' ->
             triple q env tenv (N,P) e1 (N',R) -> triple q env tenv'' (N',R) e1 (N'',Q) -> 
              triple q env tenv (N,P) (PSeq e1 e2) (N'',Q).

Definition cpred_subst_c l x v := map (fun a => celem_subst_c a x v) l.

Fixpoint subst_aexp_m (a:aexp) (x:var) (n:aexp) :=
    match a with BA y => if x =? y then n else (BA y)
              | Num a => (Num a)
              | MNum r a => (MNum r a)
              | APlus c d => match ((subst_aexp_m c x n),(subst_aexp_m d x n))
                   with (Num q, Num t) =>  (Num (q+t))
                      | (MNum r q, Num t) =>   (MNum r (q+t))
                      | (Num t, MNum r q) =>   (MNum r (q+t))
                      | (a,b) => APlus a b
                             end
              | AMult c d => match ((subst_aexp_m c x n),(subst_aexp_m d x n))
                   with (Num q, Num t) =>   (Num (q*t))
                      | (MNum r q, Num t) =>   (MNum r (q*t))
                      | (Num t, MNum r q) =>   (MNum r (q*t))
                      | (a,b) => AMult a b
                             end
              | Select s a => Select s (subst_aexp_m a x n)
    end.

Fixpoint sval_subst_m t x v :=
  match t with ST a => ST a | SV s => SV s
              | Mask s u z => Mask (sval_subst_m s x v) u (subst_aexp_m z x v)
              | AppA a b => AppA a (sval_subst_m b x v)
              | FSL e l s => FSL (sval_subst_m e x v) l s
              | SSL e a b l1 l2 => SSL (sval_subst_m e x v) (sval_subst_m a x v) b l1 l2
   end.

Definition celem_subst_m t x v := 
  match t with PFalse => PFalse 
          | CBeq a b => CBeq (subst_aexp_m a x v) (subst_aexp_m b x v)
          | CBge a b => CBge (subst_aexp_m a x v) (subst_aexp_m b x v)  
          | CBlt a b => CBlt (subst_aexp_m a x v) (subst_aexp_m b x v)
          | SEq a b => (SEq (sval_subst_m a x v) (sval_subst_m b x v)) end.

Definition cpred_subst_m l x v := map (fun a => celem_subst_m a x v) l.

Inductive sval_subst_q : sval -> session -> sval -> sval -> Prop :=
    sval_subst_st: forall x l v, sval_subst_q (ST x) l v (ST x)
  | sval_subst_sv_1: forall x l v, x = l -> sval_subst_q (SV x) l v v
  | sval_subst_sv_2: forall x l v, x <> l -> sval_subst_q (SV x) l v (SV x)
  | sval_subst_mask: forall y u z l v v', sval_subst_q y l v v' -> sval_subst_q (Mask y u z) l v (Mask v' u z)
  | sval_subst_app: forall a b l v v', sval_subst_q b l v v' -> sval_subst_q (AppA a b) l v (AppA a v')
  | sval_subst_fsl: forall a c b l v v', sval_subst_q a l v v' -> sval_subst_q (FSL a c b) l v (FSL v' c b)
  | sval_subst_ssl: forall e a b l1 l2 l v v1 v2, sval_subst_q e l v v1 -> sval_subst_q a l v v2
                                -> sval_subst_q (SSL e a b l1 l2) l v (SSL v1 v2 b l1 l2). 

Inductive celem_subst_q : cpred_elem -> session -> sval -> cpred_elem -> Prop :=
    celem_false: forall l v, celem_subst_q (PFalse) l v (PFalse)
  | celem_beq: forall l v x y, celem_subst_q (CBeq x y) l v (CBeq x y)
  | celem_bge: forall l v x y, celem_subst_q (CBge x y) l v (CBge x y)
  | celem_blt: forall l v x y, celem_subst_q (CBlt x y) l v (CBlt x y)
  | celem_seq: forall l v x x' y y', sval_subst_q x l v x' -> 
          sval_subst_q y l v y' -> celem_subst_q (SEq x y) l v (SEq x' y').

Inductive cpred_subst_q : cpred -> session -> sval -> cpred -> Prop :=
   cpred_empy: forall l v, cpred_subst_q nil l v nil
 | cpred_many: forall p p' P P' l v, celem_subst_q p l v p' -> cpred_subst_q P l v P' ->
                 cpred_subst_q (p::P) l v (p'::P').

Inductive state_syn_val : list session -> sval -> Prop :=
  | state_syn_st : forall l x, state_syn_val l (ST x)
  | state_syn_sv : forall l x, In x l -> state_syn_val l (SV x)
  | state_syn_mask : forall l y u z, state_syn_val l y -> state_syn_val l (Mask y u z).

Inductive state_syn_elem : list session -> cpred_elem -> Prop :=
    state_pfalse : forall l, state_syn_elem l (PFalse)
 |  state_cbeq : forall l x y, state_syn_elem l (CBeq x y)
 |  state_cblt : forall l x y, state_syn_elem l (CBlt x y)
 |  state_seq : forall l x y, state_syn_val l x -> state_syn_val l y -> state_syn_elem l (SEq x y).

Definition state_syn (l:type_map) (t:cpred) := Forall (fun x => state_syn_elem (dom l) x) t.


(*TODO: define the model function of a state, and claim that the type and model function of a state should match. *)
Section Triple. 




End Triple.

