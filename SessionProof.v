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

Inductive sval := ST (x:state_elem) | SV (s:session)
               | Mask (y:sval) (u:nat) (z:aexp) | AppA (x:exp) (y:sval)
               | FSL (e:sval) (l:session) (s:nat)
               | SSL (e:sval) (a:sval) (b:bexp) (l1:session) (l2:session).

Inductive cpred_elem := PFalse | CBeq (x:aexp) (y:aexp) | CBge (x:aexp) (y:aexp) | CBlt (x:aexp) (y:aexp) | SEq (x:sval) (y:sval).
                             (* x = y|_{u=z} x is a new session from the old y by cutting session u to be value z. *)


Definition cpred := list cpred_elem.
Definition fresh (l:nat) := l +1.

Fixpoint sval_subst_c t x v :=
  match t with ST a => ST a | SV s => SV s
              | Mask s u z => Mask (sval_subst_c s x v) u (subst_aexp z x v)
              | AppA a b => AppA a (sval_subst_c b x v)
              | FSL e l s => FSL (sval_subst_c e x v) l s
              | SSL e a b l1 l2 => SSL (sval_subst_c e x v) (sval_subst_c a x v) (subst_bexp b x v) l1 l2
  end.

Definition celem_subst_c t x v := 
  match t with PFalse => PFalse 
          | CBeq a b => CBeq (subst_aexp a x v) (subst_aexp b x v) 
          | CBge a b => CBge (subst_aexp a x v) (subst_aexp b x v)
          | CBlt a b => CBlt (subst_aexp a x v) (subst_aexp b x v)
          | SEq a b => (SEq (sval_subst_c a x v) (sval_subst_c b x v)) end.

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

  Inductive triple {qenv: var -> nat} {rmax:nat} : 
          atype -> aenv -> type_map -> (var * cpred) -> pexp -> (var * cpred) -> Prop :=
      | triple_comm: forall q env tenv S P Q e R, triple q env tenv (S,Q++P) e R -> triple q env tenv (S,P++Q) e R.
      | triple_split: forall q env tenv S x y v v1 v2 sv sv1 sv2 P e Q,
          env_equiv ((x++y,v)::tenv) ((x,v1)::(y,v2)::tenv) -> @state_equiv rmax ([(x++y,sv)]) ((x,sv1)::(y,sv2)::[])
       -> triple q env ((x,v1)::(y,v2)::tenv) (S,(SEq (SV x) (ST sv1))::(SEq (SV y) (ST sv2))::P) e Q
        -> triple q env ((x++y,v)::tenv) (S,(SEq (SV (x++y)) (ST sv))::P) e Q
      | triple_merge: forall q env tenv S x y v v1 v2 sv sv1 sv2 P e Q,
          env_equiv ((x,v1)::(y,v2)::tenv) ((x++y,v)::tenv) -> @state_equiv rmax ((x,sv1)::(y,sv2)::[]) ([(x++y,sv)])
        -> triple q env ((x++y,v)::tenv) (S,(SEq (SV (x++y)) (ST sv))::P) e Q
       -> triple q env ((x,v1)::(y,v2)::tenv) (S,(SEq (SV x) (ST sv1))::(SEq (SV y) (ST sv2))::P) e Q
      | skip_pf: forall q env tenv P, triple q env tenv P PSKIP P
      | let_c_pf: forall q env tenv P x v e Q,
            triple q env tenv P (subst_pexp e x v) Q -> triple q env tenv P (Let x (AE (Num v)) e) Q
      | let_m_pf: forall q env tenv P x a e Q, type_aexp env a (AType MT) ->
            triple q env tenv (fst P, ((CBeq (BA x) a))::(snd P)) e Q
                  -> triple q env tenv P (Let x (AE a) e) Q
      | let_q_pf:  forall q env tenv P x n e Q,
            triple q (AEnv.add x (Ses ([(x,0,n)])) env) ((([(x,0,n)]),TNor (Some allfalse))::tenv) P e Q
            -> triple q env tenv P (Let x (Init n) e) Q
      | mea_q_pf:  forall q env tenv S P x y l m t,
            find_type tenv ([(y,0,qenv y)]) (Some (([(y,0,qenv y)])++l,CH (Some (m,t)))) -> 
            triple q env tenv (S,(cpred_subst_m P x (Select (([(y,0,qenv y)])++l) (Num (qenv y)))))
               (Meas x y) (fresh S,(SEq (SV l) (Mask (SV ((([(y,0,qenv y)])++l))) (qenv y) (BA x)))::P)
      | app_1 : forall q env tenv S P P' l e, cpred_subst_q P l (AppA e (SV l)) P'
                -> triple q env tenv (S, P') (AppU l e) (S,P)
      | qwhile : forall q env tenv N N' P i l h b e iv,
          triple q env tenv (N,(CBlt (Num iv) (Num h))::(cpred_subst_c P i iv))
                       (If b e) (N',cpred_subst_c P i (S iv)) ->
                 triple q env tenv (N,cpred_subst_c P i l) (For i (Num l) (Num h) b e) (N',cpred_subst_c P i h)
      | if_bit : forall q env tenv N N' P P' P'' x v e E l t, 
              @type_pexp qenv env e (Ses l) ->
             find_type tenv ((x,v,S v)::l) (Some (((x,v,S v)::l),CH t)) -> 
              cpred_subst_q P ((x,v,S v)::l) E P' -> cpred_subst_q P ((x,v,S v)::l) (FSL E ((x,v,S v)::l) 1) P'' ->
              triple q env tenv (N,P') e (N',P) -> triple q env tenv (N,P'') (If (BTest x (Num v)) e) (N',P)
      | if_b : forall q env tenv N N' P P' P'' b e E l1 x v l2 t, 
              @type_pexp qenv env e (Ses l2) ->
              @type_pexp qenv env (If b e) (Ses (l1++(x,v, S v)::l2)) ->
             find_type tenv (l1++(x,v, S v)::l2) (Some ((l1++(x,v, S v)::l2),CH t)) -> 
              cpred_subst_q P (l1++(x,v, S v)::l2) E P'
               -> cpred_subst_q P (l1++(x,v, S v)::l2) (SSL E (SV (l1++(x,v, S v)::l2)) b (l1++[(x,v, S v)]) l2) P'' ->
              triple q env tenv (N,P') e (N',P) -> triple q env tenv (N,P'') (If b e) (N',P)
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

