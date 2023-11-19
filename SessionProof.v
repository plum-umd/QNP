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
Require Import SessionKind.
Require Import SessionType.
Require Import SessionSem.
Require Import SessionTypeProof.
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

Inductive sval := SV (s:session) | Frozen (b:bexp) (s:sval) (s:sval) 
     | Unfrozen (n:nat) (b:bexp) (s:sval) | FM (x:var) (n:nat) (rv:R * nat) (s:sval).

Definition qpred_elem : Type := (sval * state_elem).

Definition cpred := list cbexp.
Definition qpred : Type := list qpred_elem.
Definition fresh (l:nat) := l +1.

Inductive qpred_equiv {rmax:nat} : qpred -> qpred -> Prop :=
     | qpred_id : forall S, qpred_equiv S S
 (*    | qpred_empty : forall v S, qpred_equiv ((SV nil,v)::S) S *)
     | qpred_comm :forall a1 a2, qpred_equiv (a1++a2) (a2++a1)
     | qpred_ses_assoc: forall s v S S', qpred_equiv S S' -> qpred_equiv ((s,v)::S) ((s,v)::S')
     | qpred_ses_eq: forall s s' v S, ses_eq s s' -> qpred_equiv ((SV s,v)::S) ((SV s',v)::S)
     | qpred_sub: forall x v n u a, ses_len x = Some n -> @state_same rmax n v u -> qpred_equiv ((SV x,v)::a) ((SV x,u)::a)
     | qpred_mut: forall l1 l2 n a n1 b n2 v u S, ses_len l1 = Some n -> ses_len ([a]) = Some n1 -> ses_len ([b]) = Some n2 ->
            mut_state n n1 n2 v u -> qpred_equiv ((SV (l1++(a::b::l2)),v)::S) ((SV (l1++(b::a::l2)),u)::S)
     | qpred_merge: forall x n v y u a vu, ses_len x = Some n -> 
                       @times_state rmax n v u vu -> qpred_equiv ((SV x,v)::((SV y,u)::a)) ((SV (x++y),vu)::a)
     | qpred_split: forall x n y v v1 v2 a, ses_len x = Some n -> 
                  @split_state rmax n v (v1,v2) -> qpred_equiv ((SV (x++y),v)::a) ((SV x,v1)::(SV y,v2)::a).

Fixpoint sval_subst_c t x v :=
  match t with SV s => SV (subst_session s x v)
              | Frozen b s s' => Frozen (subst_bexp b x v) (sval_subst_c s x v) (sval_subst_c s' x v)
              | Unfrozen n b s => Unfrozen n (subst_bexp b x v) (sval_subst_c s x v)
              | FM y n rv s => FM y n rv (sval_subst_c s x v)
  end.

Definition qelem_subst_c (t: qpred_elem) x v := (sval_subst_c (fst t) x v,snd t).

Definition pred_subst_c (t: cpred * qpred) x v :=
    (List.map (fun a => subst_cbexp a x v) (fst t), List.map (fun a => qelem_subst_c a x v) (snd t)).


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

Definition sublist (l:list var) (env:aenv) := Forall (fun b => AEnv.In b env) l.

Fixpoint freeSesSV (a:sval) := match a with SV s => [s]
         | Frozen b s s' => freeSesSV s'
         | Unfrozen n b s => freeSesSV s
         | FM x n rv s => freeSesSV s
  end.

Definition freeSesQPred (l:qpred) := List.fold_right (fun b a => freeSesSV (fst b)++a) nil l.

Definition freeSesPred (a:cpred * qpred) := (freeSesQPred (snd a)).

Inductive subst_ses_sval : sval -> session -> sval -> sval -> Prop :=
   subst_ses_svt : forall x v, subst_ses_sval (SV x) x v v
   | subst_ses_svf : forall x y v, x <> y -> subst_ses_sval (SV y) x v v
   | subst_ses_unf : forall x v s n b v', subst_ses_sval s x v v' -> subst_ses_sval (Unfrozen n b s) x v (Unfrozen n b v')
   | subst_ses_fm : forall x v s y n rv v', subst_ses_sval s x v v' -> subst_ses_sval (FM y n rv s) x v (FM y n rv v').

Inductive subst_ses_qpred : qpred -> session -> sval -> qpred -> Prop :=
   subst_ses_empty: forall x v, subst_ses_qpred nil x v nil
 | subst_ses_many: forall a b x v a' l l', subst_ses_sval a x v a' -> subst_ses_qpred l x v l'
                -> subst_ses_qpred ((a,b)::l) x v ((a',b)::l').

Inductive resolve_frozen : qpred -> qpred -> Prop :=
   | resolve_frozen_many_1 : forall l q, resolve_frozen ([(SV l,q)]) ([(SV l,q)])
   | resolve_frozen_many_2 : forall l l1 m f f' fc b n n1, @eval_bexp ([(l++l1,Cval m f)]) b ([(l++l1,Cval m f')])
          -> ses_len l = Some n -> ses_len l1 = Some n1 -> 
          mut_state 0 n n1 (Cval (fst (grab_bool f' m n)) (snd (grab_bool f' m n))) fc
               -> resolve_frozen ((Frozen b (SV l) (SV l1),Cval m f)::nil) ((SV l1,fc)::nil).

Inductive resolve_unfrz : qpred -> qpred -> Prop :=
   | resolve_unfrz_many_1 : forall l q l' q', resolve_unfrz ((SV l,q)::[(SV l',q')]) ((SV l,q)::[(SV l',q')])
   | resolve_unfrz_many_2 : forall l l1 q m f m' f' f'' fc b n n1, ses_len l = Some n -> ses_len l1 = Some n1 ->
          eval_bexp ([(l++l1,Cval m f)]) b ([(l++l1,Cval m f')]) -> mut_state 0 n1 n q (Cval m' f'') -> assem_bool m m' n f' f'' fc ->
       resolve_unfrz ((Unfrozen n (BNeg b) (SV (l++l1)),Cval m f)::[((Unfrozen n b (SV (l++l1)),q))]) ([(SV (l++l1),Cval (fst fc) (snd fc))]).

Fixpoint ses_in (s:session) (l:list session) :=
  match l with nil => False
       | (a::xl) => ((ses_eq a s) \/ (ses_in s xl))
  end.

Fixpoint ses_sublist (s:list session) (l:list session) :=
  match s with nil => True
       | (a::xl) => ((ses_in a l) \/ (ses_sublist xl l))
  end.

Definition cpred_check (l:cpred) (env:aenv) := Forall (fun b => sublist (freeVarsCBexp b) env) l.

(*
Inductive sval_check : atype -> aenv -> type_map -> sval -> Prop :=
  sval_check_sv: forall g env T s, ses_in s (dom T) -> sval_check g env T (SV s)
 | sval_check_frozen: forall g env T b s s', sublist (freeVarsBexp b) env
             -> sval_check g env T s -> sval_check g env T s' -> sval_check g env T (Frozen b s s')
 | sval_check_unfrozen: forall g env T n b s, sublist (freeVarsBexp b) env
             -> sval_check g env T s -> sval_check g env T (Unfrozen n b s)
 | sval_check_fm: forall g env T x n s, sval_check g env T s -> sval_check g env T (FM x n s).
*)

Inductive sval_check : session -> sval -> Prop :=
  sval_check_sv: forall s, sval_check s (SV s)
 | sval_check_frozen: forall sa b s s', sval_check sa s' -> sval_check sa (Frozen b s s')
 | sval_check_unfrozen: forall sa n b s, sval_check sa s -> sval_check sa (Unfrozen n b s)
 | sval_check_fm: forall sa x n rv s, sval_check sa s -> sval_check sa (FM x n rv s).

Inductive qpred_check : type_map -> qpred -> Prop :=
 | qpred_check_empty: qpred_check nil nil 
 | qpred_check_many: forall sa s t v T Sa, sval_check sa s -> qpred_check T Sa
           -> type_state_elem_same t v  -> qpred_check ((sa,t)::T) ((s,v)::Sa).

Definition pred_check (env:aenv) (T:type_map) (l:cpred*qpred) := cpred_check (fst l) env /\ qpred_check T (snd l).

(*Definition class_bexp (b:bexp) := match b with CB a => Some a | _ => None end.*)

Inductive qmodel : qstate -> qpred -> Prop :=
    model_empty : qmodel nil nil
  | model_many : forall n s l v v' P,  ses_len l = Some n -> match_value n v v' 
               -> qmodel s P -> qmodel ((l,v)::s) (((SV l), v')::P).

Inductive eval_cabexp : stack -> bexp -> Prop :=
    | ceq_asem : forall s x y r1 r2 n1 n2, eval_aexp s x (r1,n1)
               -> eval_aexp s y (r2,n2) -> (r1 = r2) -> n1 = n2 -> eval_cabexp s (CB (CEq x y))
    | clt_asem : forall s x y r1 r2 n1 n2, eval_aexp s x (r1,n1) -> eval_aexp s x (r2,n2)
         -> r1 = r2 -> n1 < n2 -> eval_cabexp s (CB (CLt x y))
    | bneq_asem: forall s e, eval_cabexp s e -> eval_cabexp s (BNeg e).

Definition cmodel (s:stack) (l:cpred) : Prop := Forall (fun b => eval_cabexp s (CB b)) l.

Definition model (s:state) (P:cpred * qpred) := cmodel (fst s) (fst P) /\ qmodel (snd s) (snd P).

Inductive imply (rmax:nat) : cpred * qpred -> cpred * qpred -> Prop :=
  | imply_cpred : forall W W' P, (forall s, cmodel s W -> cmodel s W') -> imply rmax (W,P) (W',P)
  | imply_qpred: forall W P Q, @qpred_equiv rmax P Q -> imply rmax (W,P) (W,Q).

Definition type_check_proof (rmax :nat) (t:atype) (env:aenv) (T T':type_map) (P Q:cpred * qpred) e :=
   pred_check env T P /\  @session_system rmax t env T e T' /\ pred_check env T' Q.

Inductive simple_qpred_elem : qpred_elem -> Prop :=
    simple_qpred_elem_rule : forall l v, simple_qpred_elem (SV l,v).

Definition simple_qpred (Q: qpred) := Forall (fun a => simple_qpred_elem a) Q.

Inductive simp_pred_elem: sval -> state_elem -> (sval * state_elem) -> Prop :=
   | simp_pred_mea: forall x n s va va' r v, @pick_mea n va (r,v)
           -> build_state_ch n v va = Some va' -> simp_pred_elem (FM x n (r,v) (SV s)) va (SV s,va').

(*
Inductive simp_pred : cpred -> qpred -> (cpred * qpred) -> Prop :=
   | simp_pred_empty : forall W, simp_pred W nil (W,nil)
   | simp_pred_many : forall W W' W'' P P' s v a,
            simp_pred W P (W',P') -> simp_pred_elem W' s v (W'',a) -> simp_pred W ((s,v)::P) (W'',a::P').
*)

Inductive triple {rmax:nat} : 
          atype -> aenv -> type_map -> cpred*qpred -> pexp -> cpred*qpred -> Prop :=
      | triple_frame: forall q env T T1 T' l W W' P Q e R, 
                    type_check_proof rmax q env T T1 (W,P) (W',Q) e ->
           fv_pexp env e l -> sub_qubits l (dom_to_ses(dom T)) 
                  -> sub_qubits (dom_to_ses (freeSesQPred R)) (dom_to_ses(dom T'))
         -> dis_qubits (dom_to_ses(dom T)) (dom_to_ses(dom T')) 
              -> triple q env T (W,P) e (W',Q) -> triple q env (T++T') (W,P++R) e (W',Q++R)
      | triple_con_1: forall q env T T1 P P' Q e, type_check_proof rmax q env T T1 P' Q e -> 
            imply rmax P P' -> triple q env T P' e Q -> triple q env T P e Q
      | triple_con_2: forall q env T T1 P Q Q' e, type_check_proof rmax q env T T1 P Q' e -> 
            imply rmax Q' Q -> pred_check env T1 Q -> triple q env T P e Q' -> triple q env T P e Q
      | skip_pf: forall q env T P, triple q env T P PSKIP P

      | let_c_pf: forall q env T T1 P x v e Q,
            type_check_proof rmax q env T T1 P Q (subst_pexp e x v) ->
            triple q env T P (subst_pexp e x v) Q -> triple q env T P (Let x (AE (Num v)) e) Q
      | let_m_pf: forall q env T T1 W P x a e Q,
            type_check_proof rmax q (AEnv.add x (Mo MT) env) T T1 ((CEq (BA x) a)::W,P) ((CEq (BA x) a)::W,Q) e ->
            type_aexp env a (Mo MT,nil) -> ~ AEnv.In x env ->
            triple q (AEnv.add x (Mo MT) env) T ((CEq (BA x) a)::W,P) e ((CEq (BA x) a)::W,Q)
              -> triple q env T (W,P) (Let x (AE a) e) (W,Q)

      | let_q_pf:  forall q env T T1 W P PM x v y n r' v' l e Q,
              type_check_proof rmax q (AEnv.add x (Mo MT) env) ((l, CH) :: T) T1 
                            ((CEq (BA x) (MNum r' v'))::W,PM::P) ((CEq (BA x) (MNum r' v'))::W,Q) e ->
            AEnv.MapsTo y (QT n) env ->  ~ AEnv.In x env ->
            simp_pred_elem (FM x n (r',v') (SV l)) v PM ->
            triple q (AEnv.add x (Mo MT) env) ((l,CH)::T) ((CEq (BA x) (MNum r' v'))::W,PM::P) e ((CEq (BA x) (MNum r' v'))::W,Q)
            -> triple q env (((y,BNum 0,BNum n)::l,CH)::T) (W,(SV ((y,BNum 0,BNum n)::l),v)::P) (Let x (Meas y) e) (W,Q)

      | appu_nor_pf : forall q env W l l1 r b e ra ba, eval_nor rmax env l r b e = Some (ra,ba) ->
                triple q env ([(l++l1,TNor)]) (W,([(SV (l++l1),Nval r b)])) (AppU l e) (W, ([(SV (l++l1),Nval ra ba)]))
      | appu_ch_pf : forall q env W l l1 m b e ba, eval_ch rmax env l m b e = Some ba ->
                triple q env ([(l++l1,CH)]) (W,([(SV (l++l1),Cval m b)])) (AppU l e) (W, ([(SV (l++l1),Cval m ba)]))
      | apph_nor_pf: forall q env W p a r b n, @simp_varia env p a -> ses_len ([a]) = Some n ->
            triple q env ([([a], TNor)]) (W,([(SV ([a]),Nval r b)])) (AppSU (RH p)) (W, ([(SV ([a]),(Hval (eval_to_had n b)))]))

      | apph_had_pf: forall q env W p a b n, @simp_varia env p a -> ses_len ([a]) = Some n ->
            triple q env ([([a], THad)]) (W,([(SV ([a]),Hval b)])) (AppSU (RH p)) (W, ([(SV ([a]),(Nval C1 (eval_to_nor n b)))]))
      | if_c_t : forall q env T T1 P Q b e, type_check_proof rmax q env T T1 P Q e -> simp_bexp b = Some true ->
                 triple q env T P e Q -> triple q env T P (If b e) Q
      | if_c_f : forall q env T P b e, simp_bexp b = Some false ->
                 triple q env T P e P -> triple q env T P (If b e) P
      | if_q : forall q env W W' P P' P'' Q Pa Qa Qa' b e n l l1, type_bexp env b (QT n,l) -> 
                    type_check_proof rmax q env ([(l1,CH)]) ([(l1,CH)]) (W,P'') (W',Q) e -> ses_len l = Some n ->
                   subst_ses_qpred P (l++l1) (Frozen b (SV l) (SV l1)) P' -> resolve_frozen P' P'' ->
                subst_ses_qpred P (l++l1) (Unfrozen n (BNeg b) (SV (l++l1))) Pa ->
                simple_qpred Q -> subst_ses_qpred Q l1 (Unfrozen n b (SV (l++l1))) Qa -> resolve_unfrz (Pa++Qa) Qa' ->
                  triple q env ([(l1,CH)]) (W,P'') e (W',Q) -> triple q env ([(l++l1,CH)]) (W,P) (If b e) (W',Qa')

      | for_pf_f : forall q env T x l h b p P, h <= l -> triple q env T P (For x (Num l) (Num h) b p) P

      | for_pf : forall q env T x l h b p P i, l <= i < h ->
            triple q env T (pred_subst_c P x i) (If (subst_bexp b x i) (subst_pexp p x i)) (pred_subst_c P x (i+1)) ->
            triple q env T (pred_subst_c P x l) (For x (Num l) (Num h) b p) (pred_subst_c P x h)

      | seq_pf: forall q env T T1 T2 P R Q e1 e2,
             type_check_proof rmax q env T T1 P R e1 ->
             type_check_proof rmax q env T1 T2 R Q e2 ->
               triple q env T P e1 R -> triple q env T1 R e1 Q -> triple q env T P (PSeq e1 e2) Q.

Lemma resolve_frozen_simple: forall P a v, resolve_frozen P ([(a,v)]) -> (exists l, a = SV l).
Proof.
  intros. inv H. exists l. easy. exists l1. easy.
Qed.

Lemma env_state_eq_dom: forall tenv s, env_state_eq tenv s -> (dom tenv) = dom s.
Proof.
  intros. induction H; try easy.
  simpl in *. rewrite IHenv_state_eq. easy.
Qed.

Lemma dom_con {A:Type}: forall a (b:list (session*A)), dom (a::b) = (fst a)::(dom b).
Proof.
  intros. unfold dom in *. simpl in *. destruct a; try easy.
Qed.

(*
Lemma triple_proof_type: forall rmax g env T T' P e Q, @triple rmax g env T P e Q 
          -> type_check_proof rmax g env T T' P Q e.
Proof.
  intros. induction H; simpl in *; try easy.
Qed.
*)
Lemma qpred_check_length_same : forall T P, qpred_check T P -> length T = length P.
Proof.
  intros. induction H; try easy. simpl in *. rewrite IHqpred_check. easy.
Qed.

Lemma qmodel_shrink: forall q1 q2 P Q, length q1 = length P -> qmodel (q1++q2) (P ++ Q) -> qmodel q1 P.
Proof.
  intros. remember (q1++q2) as q. remember (P++Q) as C. 
  generalize dependent q1. generalize dependent P. induction H0; intros;simpl in *.
  symmetry in HeqC. symmetry in Heqq. apply app_eq_nil in HeqC as [X1 X2]. apply app_eq_nil in Heqq as [X3 X4]. subst.
  constructor.
  destruct P0. destruct q1. simpl in *. constructor. simpl in *. easy.
  destruct q1. simpl in *. easy. simpl in *. inv HeqC. inv Heqq. apply (model_many n); try easy.
  apply IHqmodel; try easy. lia.
Qed.

Lemma qmodel_shrink_1: forall q1 q2 P Q, length q1 = length P -> qmodel (q1++q2) (P ++ Q) -> qmodel q2 Q.
Proof.
  intros. remember (q1++q2) as q. remember (P++Q) as C. 
  generalize dependent q1. generalize dependent P.
  generalize dependent q2. generalize dependent Q.
  induction H0; intros;simpl in *.
  symmetry in HeqC. symmetry in Heqq. apply app_eq_nil in HeqC as [X1 X2]. apply app_eq_nil in Heqq as [X3 X4]. subst.
  constructor.
  destruct P0. destruct q1. simpl in *. destruct q2. inv Heqq. destruct Q. easy.
  inv HeqC. inv Heqq. apply (model_many n); try easy. simpl in *. easy.
  destruct q1. simpl in *. easy. inv HeqC. inv Heqq. simpl in *.
  apply IHqmodel with (P := P0) (q4 := q1); try easy. lia.
Qed.

Lemma qmodel_combine: forall q1 q2 P Q, qmodel q1 P -> qmodel q2 Q -> qmodel (q1++q2) (P++Q).
Proof.
  intros. induction H. simpl in *. easy.
  simpl in *. apply (model_many n); try easy.  
Qed.

Lemma qmodel_app: forall q P Q, qmodel q (P++Q) -> exists q1 q2, q=q1++q2 /\ length q1 = length P.
Proof.
  intros. remember (P++Q) as Qa. generalize dependent P. generalize dependent Q. induction H; intros;simpl in *.
  exists nil,nil. subst.
  symmetry in HeqQa. apply app_eq_nil in HeqQa as [X1 X2]. subst.
  simpl. easy.
  destruct P0. destruct Q. simpl in *. easy. simpl in *. inv HeqQa.
  specialize (IHqmodel Q nil). simpl in *.
  assert (Q = Q) by easy. apply IHqmodel in H2 as [q1 [q2 [X1 X2]]].
  apply length_zero_iff_nil in X2. subst. simpl in *.
  exists nil. exists ((l,v)::q2). simpl in *. easy.
  inv HeqQa.
  specialize (IHqmodel Q P0). simpl in *.
  assert (P0 ++ Q = P0 ++ Q) by easy.
  apply IHqmodel in H2 as [q1 [q2 [X1 X2]]]. subst.
  exists ((l, v) :: q1), q2. simpl in *. rewrite X2. easy.
Qed.

Lemma simple_qpred_shrink: forall P Q, simple_qpred (P++Q) -> simple_qpred P.
Proof.
  intros. unfold simple_qpred in *.
  remember (P++Q) as A. generalize dependent P. generalize dependent Q. induction H; intros;simpl in *.
  symmetry in HeqA. apply app_eq_nil in HeqA. destruct HeqA;subst.
  constructor. destruct P. simpl in *. constructor.
  inv HeqA. constructor; try easy. apply (IHForall Q). easy.
Qed.

Lemma simple_qpred_imply: forall rmax P Q, imply rmax P Q -> simple_qpred (snd P) -> simple_qpred (snd Q).
Proof.
  intros. induction H. simpl in *. easy.
  simpl in *.
Admitted.

Lemma qpred_state_consist: forall rmax T q P P', env_state_eq T q
      -> qpred_check T P -> qpred_check T P' -> @qpred_equiv rmax P P' -> qmodel q P'.
Proof.
Admitted.

Lemma qpred_check_consist: forall T T' P, simple_qpred P -> qpred_check T P -> qpred_check T' P -> T = T'.
Proof.
  intros. generalize dependent T'. induction H0; intros; simpl in *. inv H1. easy.
  inv H3.
  assert (simple_qpred Sa).
  unfold simple_qpred in * ; intros. inv H.
  apply H6; try easy.
  assert (sa = sa0).
  unfold simple_qpred in *.
  inv H. inv H6. inv H0. inv H8. easy. subst.
  rewrite (IHqpred_check H3 T0); try easy.
  inv H2. inv H10. easy.
  inv H10. easy.
  inv H10. easy.
Qed.

Lemma qpred_equiv_state_eq: forall rmax s P Q, @qpred_equiv rmax P Q -> 
       qmodel s P -> exists s', qmodel s' Q /\ @state_equiv rmax s s'.
Proof.
  intros. generalize dependent s. induction H; intros;simpl in *.
  exists s. split. easy. constructor.
  assert (G := H0).
  apply qmodel_app in H0 as [q1 [q2 [X1 X2]]]. subst.
  exists (q2++q1). split.
  apply qmodel_shrink in G as X3; try easy. apply qmodel_shrink_1 in G as X4; try easy.
  apply qmodel_combine; try easy.
  apply state_comm.
Admitted.

Lemma eval_aexp_not_exists: forall x s a v va, ~ AEnv.In x s -> eval_aexp s a va -> eval_aexp (AEnv.add x v s) a va.
Proof.
  intros. induction H0. constructor.
  assert (x0 <> x). intros R. subst.
  assert (AEnv.In x s). exists (r,n). easy. easy.
  apply AEnv.add_2. lia. easy.
  constructor. constructor; try easy. apply IHeval_aexp. easy.
  apply aplus_sem_2; try easy. apply IHeval_aexp. easy.
  constructor; try easy. apply IHeval_aexp. easy.
  apply amult_sem_2; try easy. apply IHeval_aexp. easy.
Qed.

Lemma eval_cabexp_not_exists: forall x s a v, ~ AEnv.In x s -> eval_cabexp s a -> eval_cabexp (AEnv.add x v s) a.
Proof.
  intros. induction H0; try easy. apply ceq_asem with (r1 := r1) (r2 := r2) (n1 := n1) (n2 := n2); try easy.
  apply eval_aexp_not_exists; try easy.
  apply eval_aexp_not_exists; try easy.
  apply clt_asem with (r1 := r1) (r2 := r2) (n1 := n1) (n2 := n2); try easy.
  apply eval_aexp_not_exists; try easy.
  apply eval_aexp_not_exists; try easy.
  constructor. apply IHeval_cabexp. easy.
Qed.

Lemma pick_mea_exist_same: forall n n0 m ba bl r v, n <= n0 ->
    (forall j : nat, j < m -> fst (bl j) = fst (ba j) /\ (forall i : nat, i < n0 -> snd (bl j) i = snd (ba j) i)) ->
     pick_mea n (Cval m bl) (r, v) -> pick_mea n (Cval m ba) (r, v).
Proof.
  intros. remember (r,v) as V. inv H1. inv H6.
  specialize (H0 i). assert (i < m) by lia. apply H0 in H1.
  destruct H1. destruct (ba i) eqn:eq1. simpl in *. rewrite H7 in H1. simpl in *. subst.
  rewrite H7 in H2. simpl in *.
  assert (a_nat2fb bl0 n = a_nat2fb b n).
  clear H0 eq1 H5 H7. unfold a_nat2fb. induction n; intros;simpl in *. easy.
  rewrite IHn; try lia.
  specialize (H2 n). rewrite H2 ; try lia.
  rewrite H1.
  apply pick_meas with (i := i); try easy.
Qed.

Lemma build_state_ch_exist_same: forall n n0 m ba bl v va, n <= n0 ->
    (forall j : nat, j < m -> fst (bl j) = fst (ba j) /\ (forall i : nat, i < n0 -> snd (bl j) i = snd (ba j) i)) ->
     build_state_ch n v (Cval m bl) = Some va -> 
     (exists vl, build_state_ch n v (Cval m ba) = Some vl /\ match_value (n0 - n) va vl).
Proof.
  intros. unfold build_state_ch in *.
  assert ((to_sum_c m n v bl) = (to_sum_c m n v ba)). clear H1.
  induction m; intros; simpl in *. easy.
  assert ((forall j : nat,
       j < m ->
       fst (bl j) = fst (ba j) /\
       (forall i : nat, i < n0 -> snd (bl j) i = snd (ba j) i))).
  intros. apply H0. lia. apply IHm in H1. rewrite H1.
  assert (a_nat2fb (@snd C rz_val (bl m)) n = a_nat2fb (@snd C rz_val (ba m)) n).
  clear H1 IHm.
  unfold a_nat2fb in *. induction n;intros;simpl in *. easy.
  rewrite IHn; try lia.
  specialize (H0 m). assert (m < S m) by lia. apply H0 in H1. destruct H1.
  rewrite H2; try lia. easy.
  rewrite H2.
  assert ((@fst C rz_val (bl m)) = ((@fst C rz_val (ba m)))).
  specialize (H0 m). assert (m < S m) by lia.
  apply H0 in H3. destruct H3. easy. rewrite H3. easy.
  rewrite H2 in *. remember (to_sum_c m n v ba) as f. clear H2. clear Heqf.
  destruct (build_state_pars m n v f bl) eqn:eq1. inv H1.
  assert (exists pa, build_state_pars m n v f ba = (n1,pa)
        /\ match_value (n0-n) (Cval n1 p) (Cval n1 pa)).
  generalize dependent n1. generalize dependent p.
  induction m;intros;simpl in *; try easy.
  exists (fun i => (C0,allfalse)). split. inv eq1. easy.
  constructor. intros. inv eq1. split. easy. intros. easy.
  assert (a_nat2fb (@snd C rz_val (bl m)) n = a_nat2fb (@snd C rz_val (ba m)) n).
  clear eq1 IHm.
  unfold a_nat2fb in *. induction n;intros;simpl in *. easy.
  rewrite IHn; try lia.
  specialize (H0 m). assert (m < S m) by lia. apply H0 in H1. destruct H1.
  rewrite H2; try lia. easy.
  destruct (build_state_pars m n v f bl) eqn:eq2.
  rewrite H1 in *. bdestruct (a_nat2fb (@snd C rz_val (ba m)) n =? v).
  inv eq1.
  assert ((forall j : nat,
       j < m ->
       fst (bl j) = fst (ba j) /\
       (forall i : nat, i < n0 -> snd (bl j) i = snd (ba j) i))).
  intros. apply H0. lia.
  destruct (IHm H2 p0 n2) as [pa [X1 X2]]; try easy.
  rewrite X1. exists (update pa n2 ((fst (ba m) / f)%C, lshift_fun (snd (ba m)) n)). split. easy.
  inv X2.
  constructor. intros. split; simpl in *.
  bdestruct (j <? n2).
  repeat rewrite update_index_neq; try lia. apply H5. lia.
  assert (j = n2) by lia; subst.
  repeat rewrite update_index_eq. simpl in *. 
  assert (fst (bl m) = fst (ba m)). apply H0. lia. rewrite <- H6. easy.
  intros.
  bdestruct (j <? n2).
  repeat rewrite update_index_neq; try lia. apply H5. lia. easy.
  assert (j = n2) by lia; subst.
  repeat rewrite update_index_eq. simpl in *. 
  unfold lshift_fun. destruct (H0 m); try lia.
  rewrite H8; try easy. lia. apply IHm in eq1.
  destruct eq1 as [pa [X1 X2]]. exists pa.
  rewrite X1. split. easy. easy. intros. apply H0; try easy. lia.
  destruct H1 as [pa [X1 X2]]. rewrite X1.
  exists (Cval n1 pa). split; easy.
Qed.


Lemma eval_to_nor_switch_same: forall n r1 b, (forall i : nat, i < n -> r1 i = b i)
      -> eval_to_had n r1 = eval_to_had n b.
Proof.
  intros. unfold eval_to_had in *. apply functional_extensionality.
  intros. bdestruct (x <? n). rewrite H; try easy. easy.
Qed.

Lemma eval_to_had_switch_same: forall n r1 b, (forall i : nat, i < n -> r1 i = b i)
      -> eval_to_nor n r1 = eval_to_nor n b.
Proof.
  intros. unfold eval_to_nor in *. apply functional_extensionality.
  intros. bdestruct (x <? n). rewrite H; try easy. easy.
Qed.

Lemma qfor_sem_region_1: forall rmax q env e T T1 S S1 S2,
   freeVarsNotCPExp env e -> simple_tenv T -> env_state_eq T (snd S) -> kind_env_stack env (fst S) -> 
     @session_system rmax q env T e T1 -> @qfor_sem rmax env S e S1 -> match_values (snd S) S2
   -> (exists S3, @qfor_sem rmax env (fst S, S2) e (fst S1, S3) /\ match_values (snd S1) S3).
Proof.
  intros. generalize dependent S. generalize dependent S1. generalize dependent S2.
  induction H3; intros;simpl in *; subst; try easy.
- inv H4. exists S2. split. constructor. easy.
- inv H6.
  apply freeVars_pexp_in with (v := v) in H as X1; try easy.
  rewrite simple_env_subst in *; try easy.
  rewrite H2 in *. inv H14.
  destruct (IHsession_system X1 H0 S2 S1 S H4 H5 H15 H7) as [S3 [Y1 Y2]].
  exists S3. split. eapply let_sem_c. apply H2. easy. easy.
  apply simp_aexp_no_eval in H14. rewrite H2 in *. easy.
- inv H6.
  apply type_aexp_mo_no_simp in H1. rewrite H1 in *. easy.
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H8. inv H8. easy.
  apply AEnv.add_3 in H8; try lia.
  apply H with (x0 := x0). simpl.
  apply in_app_iff. right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  specialize (IHsession_system H6 H0 S2 (W, s') (update_cval S x n)).
  unfold update_cval in IHsession_system;simpl in *.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x n (fst S))).
  unfold kind_env_stack. intros. split. intros.
  bdestruct (x0 =? x); subst.
  exists n. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H8; try easy.
  unfold AEnv.In,AEnv.Raw.PX.In in *.
  apply H5 in H8. destruct H8. exists x1. apply AEnv.add_2. lia. easy. lia.
  intros.
  bdestruct (x0 =? x); subst.
  apply AEnv.add_1. easy.
  destruct H8.
  apply AEnv.add_3 in H8; try easy.
  assert (AEnv.In x0 (fst S)). exists x1. easy. apply H5 in H10.
  apply AEnv.add_2. lia. easy. lia.
  destruct S. simpl in *.
  destruct (IHsession_system H4 H8 H15 H7) as [S3 [X3 X4]].
  exists S3. split; try easy.
  apply let_sem_m with (n0 := n) (W0 := W); try easy.
- inv H6; simpl in *. simpl in *. inv H4. inv H19.
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H6. inv H6. easy.
  apply AEnv.add_3 in H6; try lia.
  apply H with (x0 := x0). simpl.
  right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  assert (simple_tenv ((l0, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H6. inv H6.
  specialize (H0 ((y, BNum 0, BNum n0) :: a) CH).
  assert (((y, BNum 0, BNum n0) :: a, CH) = ((y, BNum 0, BNum n0) :: a, CH) \/
     In ((y, BNum 0, BNum n0) :: a, CH) T). left. easy.
  apply H0 in H6.
  inv H6. easy. apply H0 with (b:= b). right. easy.
  inv H7. destruct H12.
  assert (simple_ses ((y, BNum 0, BNum n0) :: l0)).
  unfold simple_tenv in *. eapply H0. simpl. left. easy.
  apply simple_ses_len_exists in H10. destruct H10 as [n X1].
  simpl in H8. rewrite X1 in H8. destruct y0; simpl in H8. simpl in H7.
  subst. inv H8.
  assert (n0 <= n). unfold ses_len in *. simpl in *.
  destruct (get_core_ses l0) eqn:eq2; try easy. inv X1. lia.
  apply build_state_ch_exist_same with (n0 := n) (ba := r2) in H16 as X2; try easy.
  destruct X2 as [vb [X2 X3]].
  apply pick_mea_exist_same with (n0 := n) (ba := r2) in H14 as X4; try easy.
  assert (env_state_eq ((l0, CH) :: T) (snd (AEnv.add x (r, v) W, (l0, va') :: s))).
  constructor. easy. simpl in *.
  destruct (build_state_pars m n0 v (to_sum_c m n0 v bl) bl) eqn:eq1. inv H16. constructor.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (fst (AEnv.add x (r, v) W, (l0, va') :: s))).
  simpl in *.
  unfold kind_env_stack in *. intros. split; intros.
  bdestruct (x0 =? x); subst.
  exists (r, v). apply AEnv.add_1. easy.
  apply AEnv.add_3 in H10; try lia.
  apply H5 in H10. destruct H10.
  exists x1. apply AEnv.add_2; try lia. easy.
  bdestruct (x0 =? x); subst. apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia. apply H5. destruct H10. apply AEnv.add_3 in H10; try lia.
  exists x1. easy.
  assert (match_values
                     (snd (AEnv.add x (r, v) W, (l0, va') :: s))
                     ((l0, vb) :: l')).
  constructor; try easy. split; try easy.
  simpl in *. assert (ses_len l0 = Some (n - n0)).
  unfold ses_len in *. simpl in *.
  destruct (get_core_ses l0) eqn:eq2; try easy. inv X1.
  assert (ses_len_aux l = n0 - 0 + ses_len_aux l - n0) by lia.
  rewrite <- H12. easy. rewrite H12. easy.
  destruct (IHsession_system H4 H6 ((l0, vb) :: l')
         (W', s') (AEnv.add x (r, v) W, (l0, va') :: s) H8 H10 H17 H12) as [Sa [Y1 Y2]]; simpl in Y1.
  exists Sa. split. apply let_sem_q with (W'0 := W') (r0 := r) (v0 := v) (va'0 := vb); try easy. easy.
- destruct S; simpl in *. inv H3. inv H12. inv H6. destruct y; simpl in *.
  destruct H8; subst. destruct (ses_len (l ++ l')) eqn:eq1; try easy.
  inv H6. inv H5. apply app_inv_head_iff in H8; subst.
  apply eval_nor_switch_same with (l1 := l') (n := n0) (b1 := r2) in H17 as X1; try easy.
  destruct X1 as [va [X1 X2]].
  unfold turn_pair_nor in *. destruct va; simpl in *. inv X2.
  exists (((l ++ l', Nval c r0))::l'0). split. apply appu_sem_nor; try easy.
  constructor; try easy. split. easy. simpl in *. rewrite eq1. constructor. easy.
- inv H5; simpl in *. inv H3. inv H14. inv H3. inv H6.
  destruct H7. destruct y; simpl in *; subst.
  destruct (ses_len (l ++ l0)) eqn:eq1;try easy.
  apply app_inv_head_iff in H10; subst. inv H5.
  apply eval_ch_switch_same with (l1 := l0) (n := n0) (b1 := r2) in H12 as X1; try easy.
  destruct X1 as [va [X1 X2]].
  exists ((l ++ l0, Cval m va) :: l'0).
  split. apply appu_sem_ch; try easy. constructor; try easy.
  split; try easy; simpl in *. rewrite eq1. easy.
- inv H5; simpl in *. inv H6. destruct H9. destruct y; simpl in *; subst.
  rewrite H11 in H6. inv H6.
  rewrite eval_to_nor_switch_same with (b := r2); try easy.
  exists (([a0], Hval (eval_to_had n r2)) :: l').
  split. apply appsu_sem_h_nor; try easy. constructor; try easy.
  split; try easy. simpl in *. rewrite H11. constructor. intros. easy.
  inv H3. inv H15.
- inv H5; simpl in *. inv H3. inv H15.
  inv H6. destruct H9. destruct y; simpl in *; subst.
  rewrite H11 in H6. inv H6.
  rewrite eval_to_had_switch_same with (b := r2); try easy.
  exists (([a0], Nval C1 (eval_to_nor n r2)) :: l').
  split. apply appsu_sem_h_had; try easy. constructor; try easy.
  split; try easy. simpl in *. rewrite H11. constructor. intros. easy.
- inv H6.
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *; simpl in *.
  intros. apply H with (x := x); try easy.
  apply in_app_iff. right. easy.
  destruct (IHsession_system H6 H0 S2 S1 S H4 H5 H14 H7) as [Sa [X1 X2]].
  exists Sa. split. constructor; try easy. easy.
  rewrite H2 in *. easy. apply simp_bexp_no_qtype in H10. rewrite H10 in *. easy.
- inv H5. rewrite H2 in *. easy.
  exists (S2). split. apply if_sem_cf; try easy. easy.
  apply simp_bexp_no_qtype in H9. rewrite H9 in *; try easy.
-
Admitted.

Lemma ses_eq_simple: forall l l1, ses_eq l l1 -> simple_ses l -> simple_ses l1.
Proof.
 intros. induction H. easy. inv H0. apply IHses_eq. easy.
 apply IHses_eq. constructor. easy. easy. inv H0. constructor. easy. easy. easy.
 inv H0. inv H8. apply IHses_eq. constructor; try easy.
Qed.

Lemma simple_ses_app_combine: forall l l1, simple_ses l -> simple_ses l1 -> simple_ses (l++l1).
Proof.
  intros. induction H. simpl. easy. constructor; try easy.
Qed.

Lemma proof_soundness: forall e rmax t env s tenv tenv' P Q, 
     @env_state_eq tenv (snd s) -> kind_env_stack env (fst s) ->
      type_check_proof rmax t env tenv tenv' P Q e -> freeVarsNotCPExp env e 
      -> @qstate_wt (snd s) -> simple_tenv tenv ->
    @triple rmax t env tenv P e Q -> model s P -> 
          (exists sa sb, model (fst s,sa) Q  
          /\ @qfor_sem rmax env s e (fst s,sb) /\ @state_equiv rmax sb sa).
Proof.
  intros. generalize dependent s. generalize dependent tenv'. induction H5; intros;simpl in *.
 -
  assert (simple_tenv T).
  unfold simple_tenv in *. intros. apply H4 with (b := b). apply in_app_iff.
  left. easy.
  assert (XX1 := H).
  destruct H as [X1 [X2 X3]].
  apply session_system_local with (T1 := T') in X2 as X4; try easy.
  destruct s;simpl in *.
  apply env_state_eq_app in H8 as [q1 [q2 [X5 [X6 X7]]]].
  apply env_state_eq_same_length in X5 as [X8 X9]; try easy. subst.
  assert (qstate_wt q1).
  unfold qstate_wt in *. intros. apply H10 with (s := s0) (bl := bl). apply in_app_iff.
  left. easy.
  specialize (IHtriple H2 H12 T1 XX1 (s,q1) X8 H9 H).
  unfold model in *; simpl in *. destruct H11 as [Y1 Y2].
  destruct X1 as [Y3 Y4]; simpl in *.
  apply qpred_check_length_same in Y4. rewrite Y4 in X7.
  apply qmodel_shrink in Y2 as Y5; try easy. assert (cmodel s W /\ qmodel q1 P) by easy.
  destruct (IHtriple H8) as [sa [sb [Y6 [Y7 Y8]]]]. destruct Y6.
  exists (sa++q2), (sb++q2). split. split. easy.
  apply qmodel_shrink_1 in Y2 as Y9; try easy.
  apply qmodel_combine; try easy.
  apply env_state_eq_dom in X8. apply env_state_eq_dom in X9.
  rewrite X8 in *. rewrite X9 in *. split.
  apply qfor_sem_local with (l := l) ; try easy.
  apply state_equiv_cong. easy.
  unfold simple_tenv in *. intros. apply H4 with (b := b). apply in_app_iff.
  right. easy.
 -
  specialize (IHtriple H2 H4 T1 H).
  inv H0. destruct s.
  unfold model in *; simpl in *. destruct H8 as [Y1 Y2].
  destruct H as [Y3 [Y4 Y5]]. destruct Y3 as [Y6 Y7].
  specialize (IHtriple (s,q0) H3 H6 H7).
  apply H9 in Y1 as Y3. simpl in *.
  assert (cmodel s W' /\ qmodel q0 P0) by easy.
  destruct (IHtriple H) as [sa [sb [G1 [G2 G3]]]].
  exists sa,sb. easy.
  destruct H8 as [X3 X4].
  destruct H as [Y1 [Y2 Y3]]. destruct Y1 as [Y1 Y4].
  destruct H1 as [Y5 [Y6 Y7]]. destruct Y5 as [Y5 Y8].
  simpl in *.
  apply qpred_state_consist with (T := T) (q := snd s) in H9 as X5; try easy.
  destruct (IHtriple s H3 H6 H7); try easy.
  destruct H as [sb [Y9 [Y10 Y11]]].
  exists x,sb; try easy.
 -
  destruct (IHtriple H2 H4 T1 H s H6 H7 H8 H9) as [sa [sb [X1 [X2 X3]]]].
  inv H0. destruct X1. simpl in *. apply H10 in H0.
  exists sa,sb. easy. destruct H3. destruct X1; simpl in *.
  destruct H3 as [Y1 Y2]. destruct H as [Y3 [Y4 Y5]]. simpl in *.
  apply qpred_equiv_state_eq  with (s:= sa) in H10 as [sc [G1 G2]]; try easy.
  exists sc,sb. split. easy. split. easy. apply state_equiv_trans with (S2 := sa); try easy.
 - 
  destruct s. exists q0,q0. split. easy.
  split. constructor. constructor.
 - 
  apply freeVars_pexp_in with (v := v) in H2 as X1; try easy.
  destruct (IHtriple X1 H4 T1 H s H0 H3 H6 H7) as [sa [sb [X2 [X3 X4]]]].
  exists sa,sb. split. easy.
  split. apply let_sem_c with (n := v); try easy.
  easy. inv H1. inv H9. inv H1. easy. easy.
 -
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H11. inv H11. easy.
  apply AEnv.add_3 in H11; try lia.
  apply H2 with (x0 := x0). simpl.
  apply in_app_iff. right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  destruct s; simpl in *.
  apply kind_env_stack_exist with (s := s) in H0 as X1. destruct X1 as [va X1].
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x va s)).
  unfold kind_env_stack. intros. split. intros.
  bdestruct (x0 =? x); subst.
  exists va. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H11; try easy.
  unfold AEnv.In,AEnv.Raw.PX.In in *.
  apply H7 in H11. destruct H11. exists x1. apply AEnv.add_2. lia. easy. lia.
  intros. destruct H11.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H11. subst.
  apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia.
  apply H7. apply AEnv.add_3 in H11; try lia. exists x1. easy.
  specialize (IHtriple H10 H4 T1 H ((AEnv.add x va s),q0) H6 H11 H8).
  destruct H9 as [X2 X3]. simpl in *.
  assert (cmodel (AEnv.add x va s) (CEq (BA x) a :: W)).
  constructor. 
  apply eval_aexp_not_exists with (x := x) (v := va) in X1; try easy.
  destruct va.
  apply ceq_asem with (s := (AEnv.add x (r, n) s)) (x := BA x) (y := a) (r1 := r) (r2 := r) (n1 := n) (n2 := n) ; try easy.
  apply var_sem. apply AEnv.add_1. easy. intros R. apply H7 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  unfold cmodel in X2.
  assert (~ AEnv.In x s). intros R. apply H7 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  clear H H0 X1 H5 H6 IHtriple H3 H7 H8 X3 H10 H11.
  induction X2. constructor. constructor.
  apply eval_cabexp_not_exists. easy. easy. easy.
  assert (model (AEnv.add x va s, q0) (CEq (BA x) a :: W, P)).
  split. simpl in *. apply H9. easy.
  destruct (IHtriple H12) as [sa [sb [Y1 [Y2 Y3]]]].
  exists sa, sb. split. split. easy. destruct Y1. simpl in *. 
  easy. split. apply let_sem_m with (n := va) (W0 := AEnv.add x va s); try easy. easy. easy.
  unfold freeVarsNotCPExp,freeVarsNotCAExp in *. intros. simpl in *. apply H2 with (x0 := x0); try easy.
  apply in_app_iff. left. easy.
 -
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H12. inv H12. easy.
  apply AEnv.add_3 in H12; try lia.
  apply H2 with (x0 := x0). simpl.
  right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  assert (simple_tenv ((l, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H12. inv H12.
  specialize (H4 ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
     In ((y, BNum 0, BNum n) :: a, CH) T). left. easy.
  apply H4 in H12.
  inv H12. easy. apply H4 with (b:= b). right. easy.
  specialize (IHtriple H11 H12 T1 H).
  destruct s. simpl in *.
  inv H7. destruct H10. simpl in *.
  inv H3.
  destruct H as [X2 [X3 X4]].
  inv X2. simpl in *. inv H3.
  assert (env_state_eq ((l, CH) :: T)
             (snd (AEnv.add x (r', v') s, (l, va') :: l2))).
  constructor; try easy.
  assert (kind_env_stack (AEnv.add x (Mo MT) env)
             (fst (AEnv.add x (r', v') s, (l, va') :: l2))).
  unfold kind_env_stack in *. intros. split; intros.
  bdestruct (x0 =? x); subst.
  exists (r', v'). apply AEnv.add_1. easy.
  apply AEnv.add_3 in H13; try lia.
  apply H8 in H13. destruct H13.
  exists x1. apply AEnv.add_2; try lia. easy.
  bdestruct (x0 =? x); subst. apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia. apply H8. destruct H13. apply AEnv.add_3 in H13; try lia.
  exists x1. easy.
  inv H18. inv H10. inv H26.
  apply mask_state_exists in H22 as Y1. destruct Y1 as [na [p [Y1 Y2]]]; subst.
  rewrite Y1 in H23. inv H23.
  assert (qstate_wt (snd (AEnv.add x (r', v') s, (l, (Cval na p)) :: l2))).
  unfold qstate_wt in *. intros. simpl in *.
  inv H10; try easy. inv H14. easy.
  eapply H9. right. apply H14.
  assert (model (AEnv.add x (r', v') s, (l, Cval na p) :: l2)
             (CEq (BA x) (MNum r' v') :: W, (SV l, Cval na p) :: P)).
  split. simpl.
  constructor. apply ceq_asem with (r1 := r') (r2 := r') (n1 := v') (n2 := v'); try easy.
  constructor. apply AEnv.add_1. easy. constructor.
  unfold cmodel in H7.
  assert (~ AEnv.In x s). intros R. apply H8 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  clear H2 H4 X3 X4 H0 H1 H5 IHtriple H6 H8 H9 H11 H12 H17 Y1 Y2 H H19 H24 H13 H3 H25 H22 H20 H27 H18 H10.
  induction H7. constructor. constructor.
  apply eval_cabexp_not_exists; easy. easy.
  simpl in *.
  assert (exists nb, ses_len l = Some nb).
  unfold ses_len in *.
  destruct (get_core_ses ((y, BNum 0, BNum n) :: l)) eqn:eq1; try easy. simpl in *.
  destruct (get_core_ses l) eqn:eq2; try easy. inv eq1. simpl in *.
  exists (ses_len_aux l1). easy. destruct H14.
  apply model_many with (n := x0); try easy.
  constructor. intros. split. easy. intros. easy.
  destruct (IHtriple ((AEnv.add x (r',v') s, (l,(Cval na p))::l2))
          H3 H13 H10 H14) as [sa [sb [G1 [G2 G3]]]].
  exists sa,sb.
  split. split. easy. simpl in *. inv G1. simpl in *. easy.
  split. 
  assert (n <= n0).
  unfold ses_len in *.
  unfold ses_len in *.
  destruct (get_core_ses ((y, BNum 0, BNum n) :: l)) eqn:eq1; try easy. simpl in *.
  destruct (get_core_ses l) eqn:eq2; try easy. inv eq1. simpl in *.
  inv H20. lia.
  apply let_sem_q with (r := r') (v := v') (va' := (Cval na p)) (W' := (AEnv.add x (r', v') s)); try easy.
  apply pick_mea_exist_same with (n0 := n0) (ba := r2); try easy.
  rewrite build_state_ch_exist_same with (n0 := n0) (bl := bl) in Y1; try easy. easy.
 -
  destruct s. inv H6.
  exists ([(l++l1,Nval ra ba)]),([(l++l1,Nval ra ba)]).
  split. split. easy. simpl.
  unfold simple_tenv in *.
  specialize (H4 (l++l1) TNor). assert (In (l ++ l1, TNor) [(l ++ l1, TNor)]). simpl. left. easy.
  apply H4 in H6. apply simple_ses_len_exists in H6. destruct H6.
  apply model_many with (n:= x); try easy.
  constructor. intros. easy. constructor.
  split. simpl in *. inv H8. inv H13. inv H14.
  apply appu_sem_nor; try easy.
  rewrite eval_nor_switch_same with (b1 := b) (l1 := l1) (n := n); try easy.
  constructor.
 -
  destruct s. inv H6.
  exists ([(l++l1,Cval m ba)]),([(l++l1,Cval m ba)]).
  split. split. easy. simpl.
  unfold simple_tenv in *.
  specialize (H4 (l++l1) CH). assert (In (l ++ l1, CH) [(l ++ l1, CH)]). simpl. left. easy.
  apply H4 in H6. apply simple_ses_len_exists in H6. destruct H6.
  apply model_many with (n:= x); try easy.
  constructor. intros. easy. constructor.
  split. simpl in *. inv H8. inv H13. inv H14.
  apply appu_sem_ch; try easy.
  rewrite eval_ch_switch_same with (b1 := b) (l1 := l1) (n := n); try easy.
  constructor.
 -
  destruct s. inv H7. simpl in *.
  inv H9. inv H15. inv H14.
  exists ([(([a]),Hval (eval_to_had n b))]),([(([a]),Hval (eval_to_had n b))]).
  split. split. easy. simpl.
  apply model_many with (n := n); try easy. constructor. intros. easy. constructor.
  split. rewrite H0 in H13. inv H13.
  rewrite <- eval_to_nor_switch_same with (r1 := r1); try easy.
  constructor; try easy.
  constructor. 
 -
  destruct s. inv H7. simpl in *.
  inv H9. inv H15. inv H14.
  exists ([(([a]),(Nval C1 (eval_to_nor n b)))]),([(([a]),(Nval C1 (eval_to_nor n b)))]).
  split. split. easy. simpl.
  apply model_many with (n := n); try easy. constructor. intros. easy. constructor.
  split. rewrite H0 in H13. inv H13.
  rewrite <- eval_to_had_switch_same with (r1 := r1); try easy.
  constructor; try easy.
  constructor. 
 -
  assert (freeVarsNotCPExp env e) as X1.
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x) (t := t); try easy. simpl. apply in_app_iff. right. easy.
  destruct (IHtriple X1 H4 T1 H s H3 H6 H7 H8) as [sa [sb [X2 [X3 X4]]]].
  exists sa,sb. split. easy.
  split. apply if_sem_ct; try easy. easy.
 -
  destruct s. simpl in *. exists q0,q0.
  split. easy. split. apply if_sem_cf; try easy. apply state_id.
 -
  assert (freeVarsNotCPExp env e) as X1.
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x) (t := t); try easy. simpl. apply in_app_iff. right. easy.
  assert (simple_tenv ([(l1, CH)])).
  unfold simple_tenv in *.
  intros. simpl in *. destruct H16; try easy. 
  inv H16. assert ((l ++ a, CH) = (l++a, CH) \/ False). left. easy.
  apply H4 in H16. apply simple_ses_app_r in H16. easy.
  specialize (IHtriple X1 H16 ([(l1, CH)]) H0).
  inv H15. destruct s. simpl in *.
  destruct H0 as [X2 [X3 X4]]. inv X2. inv H15. simpl in *. subst. inv H24. inv H25.
  inv H12. inv H23. inv H24.
  apply resolve_frozen_simple in H5 as [la Y1]; subst. inv H22.
  inv H18. inv H22. inv H21.
  destruct H12. inv H12. inv H20. inv H27. simpl in *. subst.
  inv H3. inv H25. inv H28. inv H30. inv H6. inv H21. inv H20. inv H24. inv H29; try easy.
  inv H5.
  assert (simple_qpred ([(SV l1, Cval m bl)])).
  constructor. constructor. constructor.

  assert (env_state_eq ([(l1, CH)]) (snd (s, [(l1, Cval m bl)]))).
  simpl in *. constructor. constructor. constructor.
  assert (kind_env_stack_full env (fst (s, [(l1, Cval m bl)]))).
  simpl in *. easy.
  assert (m = (fst (grab_bool f' m0 n0))).
  inv H28. easy. subst.
  assert (qstate_wt
             (snd
                (s, [(l1, Cval (fst (grab_bool f' m0 n0)) bl)]))).
  unfold qstate_wt in *.
  intros. simpl in *. destruct H16; try easy. inv H16.
  apply grab_bool_gt. apply H15 with (s := l ++ s0) (bl := r1). left. easy.
  apply type_bexp_gt in H. rewrite H1 in H26. inv H26. easy.
  assert (model (s, [(l1, Cval (fst (grab_bool f' m0 n0)) bl)])
             (W, [(SV l1, Cval (fst (grab_bool f' m0 n0)) bl)])).
  split. easy. simpl in *. apply model_many with (n := n1); try easy.
  constructor. intros. easy. constructor.
  destruct (IHtriple (s,([(l1,Cval (fst (grab_bool f' m0 n0)) bl)])) H6 H12 H16 H23) as [Wa [sa [sb [Y2 [Y3 Y4]]]]].
  inv X4. simpl in *. inv H29. inv H36. inv H35. inv H8. inv H31. inv H32. inv H33; try easy.
  inv Y2. simpl in *. inv H29. inv H36. inv H35.
  apply state_preserve with (s := (s, [(l0, Cval (fst (grab_bool f' m0 n0)) bl)])) (s' := (Wa,sb)) in X3 as Y5; try easy.
  destruct Y5 as [Y5 Y6]. simpl in *. inv Y5. inv H35. inv H36.
  apply state_equiv_single_ch_same in Y4. destruct Y4;subst.
  inv H9. inv H38. inv H37; try easy.
  inv H7. inv H38. inv H37; try easy.
  inv H10. rewrite H26 in H1. inv H1. rewrite H34 in H27. inv H27.
  apply app_length_same with (n := n) in H30; try easy. destruct H30; subst. 
  rewrite H41 in H34; inv H34.
  exists Wa, ([((l++l0),Cval (fst fc) (snd fc))]), ([((l++l0),Cval (fst fc) (snd fc))]).
  split. split. easy. simpl. apply model_many with (n := n + n1); try easy.
  rewrite ses_len_app_add with (n := n) (n1 := n1); try easy. constructor. intros. easy. constructor.
  split. apply eval_bexp_det with (q1 := [(l ++ l0, Cval m0 f'0)]) in H21; try easy. inv H21.
  apply (if_sem_q env s Wa l l0 n n1 nil nil b e m0 m' r1 f' (Cval (fst (grab_bool f' m0 n)) bl) (Cval m bl1) f'' fc); try easy.
  apply (bexp_eval_same env b n) with (n2 := n2) (bl := bl0); try easy.
  apply (qfor_sem_region rmax q) with (n := n1) (r := r0); try easy.
  constructor. unfold simple_tenv in H4.
  specialize (H4 (l++l0) CH). assert (In (l ++ l0, CH) [(l ++ l0, CH)]). simpl. left. easy.
  apply H4 in H29. apply simple_ses_app_r in H29. easy.
 -
  destruct s. exists s, q0, q0. split. easy.
  split. apply for_sem. assert (h - l = 0) by lia. rewrite H8. apply ForallA_nil.
  constructor.
Qed.

Lemma proof_completeness: forall e rmax t env s s' tenv tenv' P Q, 
     @env_state_eq tenv (snd s) -> kind_env_stack env (fst s) ->
      type_check_proof rmax t env tenv tenv' P Q e -> freeVarsNotCPExp env e -> @qstate_wt (snd s) -> simple_tenv tenv ->
    @qfor_sem rmax env s e s' ->  simple_qpred (snd P) -> model s P -> 
          (exists Q, model s' Q /\ @triple rmax t env tenv P e Q).
Proof.
  intros. generalize dependent P. generalize dependent tenv. generalize dependent tenv'.
  induction H5 using qfor_sem_ind'; intros;simpl in *.
Admitted.






