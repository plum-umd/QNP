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
Require Import SessionProof.
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

Definition qheap : Type := var * nat -> rz_val.

Definition pval :Type := (var * nat) * rz_val.

Inductive ppred_elem := PPFalse | CPP (b:cbexp) 
           | SPEq (l:session) (v:state_elem)
(* | SUpa (l:var) (v:C) | SUpp (l:var) (x:aexp) (n:bool) *)
           | CPNeg (b:cbexp)
           | TPEq (x:var) (l:session).

(*
Inductive single_mu := MRH (p:var) | MSQFT (x:var) | MSRQFT (x:var).
*)
Inductive mexp := MSKIP 
            | MLet (x:var) (n:maexp) (e:mexp)
              (*| InitQubit (p:posi) *) 
              (* Ethan: Init = reset = trace out = measurement... commeneted out *)
            (*| MAppSU (e:single_mu) *)
            | MAppU (l:var) (e:exp) 
            | MSeq (s1:mexp) (s2:mexp)
          (*compile to CU / CNOT *)
            | MIf (x:bexp) (s1:mexp)
            | Mask (x:var) (l:session) (b:bexp)
            | UnMask (x:var) (l:session) (b:bexp)
            | MFor (x:var) (l:aexp) (h:aexp) (b:bexp) (p:mexp)
                (* for (int x = l; x < h && b ; x++) p; 
                    --> repeat x in (h-l) times of (If b(c/x) p) *)
                   (*  quantum oracle functions executing p, and a list of tuples (x,a,s)
                      the first argument is the list of variables of quantum to p,
                       the second arguments a is the phase of the post-state of x,
                       the third is the state s = f(x) as |x> -> e^2pi i * a *|s>,
                       excluding ancilla qubits  *)
                (* reflection on x with the form aexp x=n. l is the session. (|n><n| - I) tensor x *)
            | MDiffuse (x:var).


Definition ppred := list ppred_elem.

Definition ses_set := list (list var).

Inductive same_ses_set : ses_set -> var -> var -> Prop :=
   same_ses_set_rule: forall s a b al, In a al -> In b al -> In al s -> same_ses_set s a b.


Fixpoint freeVarsInAExp (a:aexp) :=
   match a with BA x => [x] | Num n => nil | MNum r n => nil 
   | APlus x y => freeVarsInAExp x ++ freeVarsInAExp y
   | AMult x y => freeVarsInAExp x ++ freeVarsInAExp y
   end.

Definition freeVarsInVaria (a:varia) :=
  match a with AExp x => freeVarsInAExp x | Index x v => x::(freeVarsInAExp v) end.

Definition freeVarsInCBExp (a:cbexp) :=
   match a with CEq x y => freeVarsInAExp x ++ freeVarsInAExp y
              | CLt x y => freeVarsInAExp x ++ freeVarsInAExp y
   end.

Fixpoint freeVarsInBExp (a:bexp) :=
   match a with CB x => freeVarsInCBExp x
   | BEq x y i a => freeVarsInVaria x ++ freeVarsInVaria y ++ [i] ++ freeVarsInAExp a
   | BLt x y i a => freeVarsInVaria x ++ freeVarsInVaria y ++ [i] ++ freeVarsInAExp a
   | BTest i a => [i] ++ freeVarsInAExp a
   | BNeg b => freeVarsInBExp b
   end.


Definition freeVarsInMAExp (a:maexp) :=
   match a with AE x => freeVarsInAExp x
   | Meas x  => [x]
   end.

Definition freeVarsInBound m := match m with BVar x i => [x] | BNum n => nil end.

Definition freeVarsInRange (a: range) := match a with (x,n,m) => x::freeVarsInBound n++freeVarsInBound m end.

Fixpoint freeVarsInSession (s: session) := match s with nil => nil
                       | a::al => freeVarsInRange a ++ freeVarsInSession al end.

Fixpoint freeVarsInMExp (a:mexp) :=
  match a with MSKIP => nil | MLet x n e => x::freeVarsInMAExp n ++ freeVarsInMExp e
             | MAppU l e => [l]
             | MSeq s1 s2 => freeVarsInMExp s1 ++ freeVarsInMExp s2
             | MIf x s1 => freeVarsInBExp x ++ freeVarsInMExp s1
             | Mask x l b => x::freeVarsInSession l ++ freeVarsInBExp b
             | UnMask x l b => x::freeVarsInSession l ++ freeVarsInBExp b
             | MFor x l h b p => x::freeVarsInAExp l ++ freeVarsInAExp h ++ freeVarsInBExp b ++ freeVarsInMExp p
             | MDiffuse x => [x]
  end.



Definition freeVarsInPPredElem (p:ppred_elem) :=
   match p with PPFalse => nil | CPP b => freeVarsInCBExp b
             | SPEq l v => freeVarsInSession l 
             | CPNeg b => freeVarsInCBExp b
             | TPEq x l => x::freeVarsInSession l
   end.

Fixpoint freeVarsInPPred (p:ppred) := match p with nil => nil | a::al => freeVarsInPPredElem a ++ freeVarsInPPred al end.

Fixpoint same_ses_set_list (s:ses_set) (x:var) (xl:list var) :=
   match xl with nil => False | (a::al) => (same_ses_set s x a \/ same_ses_set_list s x al) end.

Fixpoint same_ses_set_dlist (s:ses_set) (xl yl:list var) :=
   match xl with nil => False | (a::al) => (same_ses_set_list s a yl \/ same_ses_set_dlist s al yl) end.

  Inductive ptriple {rmax:nat} : 
          atype -> aenv -> ses_set -> ppred -> mexp -> ppred -> Prop :=
      | ptriple_comm: forall q env tenv P Q e R, ptriple q env tenv (Q++P) e R -> ptriple q env tenv (P++Q) e R
      | ptriple_frame: forall q env T P Q e R, same_ses_set_dlist T (freeVarsInMExp e) (freeVarsInPPred R) ->
               ptriple q env T P e Q -> ptriple q env T (P++R) e (Q++R)
      | pskip_pf: forall q env tenv P, ptriple q env tenv P MSKIP P

(*
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
*)
      | pappu_pf : forall q env T x l l1 m b e ba,  
                eval_ch rmax env l m b e = Some ba ->
                ptriple q env T ((TPEq x l)::[SPEq ( (l++l1)) (Cval m b)]) (MAppU x e) ((TPEq x l)::[SPEq ( (l++l1)) (Cval m ba)]).

(*
      | dis_pf : forall q env T x n l l1 n' m f m' acc, type_vari env x (QT n,l) -> find_type T l (Some (l++l1,CH)) ->
                 ses_len l1 = Some n' -> dis_sem n n' m m f nil (m',acc) -> 
                triple q env T ([SEq (SV (l++l1)) (Cval m f)]) (Diffuse x) ([SEq (SV (l++l1)) (Cval m' acc)])

      | for_pf : forall q env T x l h b p P i, l <= i < h ->
            triple q env T (cpred_subst_c P x i) (If (subst_bexp b x i) (subst_pexp p x i)) (cpred_subst_c P x (i+1)) ->
            triple q env T (cpred_subst_c P x l) (For x (Num l) (Num h) b p) (cpred_subst_c P x h)
      | if_c : forall q env T P Q a b e, class_bexp b = Some a ->
                 triple q env T (CP a::P) e Q -> triple q env T (CNeg a::P) PSKIP Q -> triple q env T P (If b e) Q
*)

      | pif_q : forall q env T T' P P' Pa Q Q' Qa b e n l l1, type_bexp env b (QT n,l) -> find_type T l (Some (l++l1,CH)) ->
                  up_type T l1 CH T' -> subst_ses_cpred P (l++l1) (Frozen b (SV l1)) P' -> pred_check q env ([(l1,CH)]) Q' ->
                subst_ses_cpred P (l++l1) (Unfrozen n (BNeg b) (SV (l++l1))) Pa ->
                subst_ses_cpred Q' l1 (Unfrozen n b (SV (l++l1))) Qa ->
                  ptriple q env T P (MIf x b e) (Pa++Qa)


      | seq_pf: forall q env tenv tenv' tenv'' P R Q e1 e2,
             @session_system rmax q env tenv e1 tenv' -> up_types tenv tenv' tenv'' -> pred_check q env tenv'' R ->
             triple q env tenv P e1 R -> triple q env tenv'' R e1 Q -> triple q env tenv P (PSeq e1 e2) Q.


Inductive fv_pexp : aenv -> mexp -> session -> Prop :=
  | pskip_fa: forall env, fv_pexp env (PSKIP) nil
  | let_fa_c : forall env x a e, fv_pexp env (Let x (AE a) e) nil
  | let_fa_m : forall env x a e n, AEnv.MapsTo x (QT n) env -> fv_pexp env (Let x (Meas a) e) ([(x,BNum 0,BNum n)])
  | appsu_fa: forall env e s,  fv_su env e s -> fv_pexp env (AppSU e) s
  | appu_fa : forall env l e, fv_pexp env (AppU l e) l
  | if_fa : forall env t l l1 b e, type_bexp env b (t,l) -> fv_pexp env e l1 -> fv_pexp env (If b e) (l++l1)
  | for_fa : forall env t l h x b e, (forall i, l <= i < h -> 
                 fv_pexp env (If (subst_bexp b x i) (subst_pexp e x i)) (subst_session t x i))
                              -> fv_pexp env (For x (Num l) (Num h) b e) (subst_session t x h)
  | pseq_fa : forall env e1 e2 l1 l2, fv_pexp env e1 l1 -> fv_pexp env e2 l2 
                              -> fv_pexp env (PSeq e1 e2) (join_ses l1 l2)
  | dis_fa : forall env x n, AEnv.MapsTo x (QT n) env -> fv_pexp env (Diffuse x) ([(x,BNum 0,BNum n)]).

(*
Inductive sval := SV (s:session) | Frozen (b:bexp) (s:sval) | Unfrozen (n:nat) (b:bexp) (s:sval) | FM (x:var) (n:nat) (s:sval).

Inductive cpred_elem := PFalse | CP (b:cbexp) | SEq (x:sval) (y:state_elem) | CNeg (b:cbexp).
                             (* x = y|_{u=z} x is a new session from the old y by cutting session u to be value z. *)
*)

Inductive state_elem :=
                 | Nval (p:C) (r:rz_val)
                 | Hval (b:nat -> rz_val)
                 | Cval (m:nat) (b : nat -> C * rz_val).


Definition cpred := list cpred_elem.
Definition fresh (l:nat) := l +1.

Fixpoint sval_subst_c t x v :=
  match t with SV s => SV (subst_session s x v)
              | Frozen b s => Frozen (subst_bexp b x v) (sval_subst_c s x v)
              | Unfrozen n b s => Unfrozen n (subst_bexp b x v) (sval_subst_c s x v)
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
         | Unfrozen n b s => freeSesSV s
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
   | subst_ses_unf : forall x v s n b v', subst_ses_sval s x v v' -> subst_ses_sval (Unfrozen n b s) x v (Unfrozen n b v')
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
 | sval_check_unfrozen: forall g env T n b s, sublist (freeVarsBexp b) env
             -> sval_check g env T s -> sval_check g env T (Unfrozen n b s)
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
                triple q env T ([SEq (SV (l++l1)) (Cval m b)]) (AppU l e) ([SEq (SV (l++l1)) (Cval m ba)])
      | dis_pf : forall q env T x n l l1 n' m f m' acc, type_vari env x (QT n,l) -> find_type T l (Some (l++l1,CH)) ->
                 ses_len l1 = Some n' -> dis_sem n n' m m f nil (m',acc) -> 
                triple q env T ([SEq (SV (l++l1)) (Cval m f)]) (Diffuse x) ([SEq (SV (l++l1)) (Cval m' acc)])

      | for_pf : forall q env T x l h b p P i, l <= i < h ->
            triple q env T (cpred_subst_c P x i) (If (subst_bexp b x i) (subst_pexp p x i)) (cpred_subst_c P x (i+1)) ->
            triple q env T (cpred_subst_c P x l) (For x (Num l) (Num h) b p) (cpred_subst_c P x h)
      | if_c : forall q env T P Q a b e, class_bexp b = Some a ->
                 triple q env T (CP a::P) e Q -> triple q env T (CNeg a::P) PSKIP Q -> triple q env T P (If b e) Q
      | if_q : forall q env T T' P P' Pa Q Q' Qa b e n l l1, type_bexp env b (QT n,l) -> find_type T l (Some (l++l1,CH)) ->
                  up_type T l1 CH T' -> subst_ses_cpred P (l++l1) (Frozen b (SV l1)) P' -> pred_check q env ([(l1,CH)]) Q' ->
                subst_ses_cpred P (l++l1) (Unfrozen n (BNeg b) (SV (l++l1))) Pa ->
                subst_ses_cpred Q' l1 (Unfrozen n b (SV (l++l1))) Qa ->
                  triple q env T' P' e (Q++Q') -> triple q env T P (If b e) (Pa++Qa)
      | seq_pf: forall q env tenv tenv' tenv'' P R Q e1 e2,
             @session_system rmax q env tenv e1 tenv' -> up_types tenv tenv' tenv'' -> pred_check q env tenv'' R ->
             triple q env tenv P e1 R -> triple q env tenv'' R e1 Q -> triple q env tenv P (PSeq e1 e2) Q.

