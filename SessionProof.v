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

Inductive sval := SV (s:session) | Frozen (b:bexp) (s:sval) (s:sval) | Unfrozen (n:nat) (b:bexp) (s:sval) | FM (x:var) (n:nat) (s:sval).

Definition qpred_elem : Type := (sval * state_elem).

Definition cpred := list cbexp.
Definition qpred : Type := list qpred_elem.
Definition fresh (l:nat) := l +1.

Inductive qpred_equiv {rmax:nat} : qpred -> qpred -> Prop :=
     | qpred_id : forall S, qpred_equiv S S
     | qpred_empty : forall v S, qpred_equiv ((SV nil,v)::S) S
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
              | FM y n s => FM y n (sval_subst_c s x v)
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
         | FM x n s => freeSesSV s
  end.

Definition freeSesQPred (l:qpred) := List.fold_right (fun b a => freeSesSV (fst b)++a) nil l.

Definition freeSesPred (a:cpred * qpred) := (freeSesQPred (snd a)).

Inductive subst_ses_sval : sval -> session -> sval -> sval -> Prop :=
   subst_ses_svt : forall x v, subst_ses_sval (SV x) x v v
   | subst_ses_svf : forall x y v, x <> y -> subst_ses_sval (SV y) x v v
   | subst_ses_unf : forall x v s n b v', subst_ses_sval s x v v' -> subst_ses_sval (Unfrozen n b s) x v (Unfrozen n b v')
   | subst_ses_fm : forall x v s y n v', subst_ses_sval s x v v' -> subst_ses_sval (FM y n s) x v (FM y n v').

Inductive subst_ses_qpred : qpred -> session -> sval -> qpred -> Prop :=
   subst_ses_empty: forall x v, subst_ses_qpred nil x v nil
 | subst_ses_many: forall a b x v a' l l', subst_ses_sval a x v a' -> subst_ses_qpred l x v l'
                -> subst_ses_qpred ((a,b)::l) x v ((a',b)::l').

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
 | sval_check_fm: forall sa x n s, sval_check sa s -> sval_check sa (FM x n s).

Inductive qpred_check : type_map -> qpred -> Prop :=
 | qpred_check_empty: qpred_check nil nil 
 | qpred_check_many: forall sa s t v T Sa, sval_check sa s -> qpred_check T Sa
           -> type_state_elem_same t v  -> qpred_check ((sa,t)::T) ((s,v)::Sa).

Definition pred_check (env:aenv) (T:type_map) (l:cpred*qpred) := cpred_check (fst l) env /\ qpred_check T (snd l).

(*Definition class_bexp (b:bexp) := match b with CB a => Some a | _ => None end.*)

Inductive match_value : nat -> state_elem -> state_elem -> Prop :=
   match_nval : forall n p r1 r2, (forall i, i < n -> r1 i = r2 i) -> match_value n (Nval p r1) (Nval p r2)
 | match_hval: forall n r1 r2, (forall i, i < n -> r1 i = r2 i) -> match_value n (Hval r1) (Hval r2)
 | match_cval: forall n m r1 r2, (forall j, j < m -> fst (r1 j) = fst (r2 j) /\
               (forall i, i < n -> (snd (r1 j)) i = (snd (r2 j)) i)) -> match_value n (Cval m r1) (Cval m r2).

Inductive qmodel : qstate -> qpred -> Prop :=
    model_empty : qmodel nil nil
  | model_many : forall n s l v v' P,  ses_len l = Some n -> match_value n v v' -> qmodel s P -> qmodel ((l,v)::s) (((SV l), v')::P).

Inductive eval_cabexp : stack -> bexp -> Prop :=
    | ceq_asem : forall s x y r1 r2 n1 n2, eval_aexp s x (r1,n1)
               -> eval_aexp s y (r2,n2) -> (r1 = r2) -> n1 = n2 -> eval_cabexp s (CB (CEq x y))
    | clt_asem : forall s x y r1 r2 n1 n2, eval_aexp s x (r1,n1) -> eval_aexp s x (r2,n2) -> r1 = r2 -> n1 < n2 -> eval_cabexp s (CB (CLt x y))
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

Inductive simp_pred_elem: cpred -> sval -> state_elem -> cpred * (sval * state_elem) -> Prop :=
   | simp_pred_id :forall W s v, simp_pred_elem W (SV s) v (W,(SV s,v))
   | simp_pred_mea: forall W x n s va va' r v, @pick_mea n va (r,v)
           -> build_state_ch n v va = Some va' -> simp_pred_elem W (FM x n (SV s)) va ((CEq (BA x) (MNum r v))::W, (SV s,va')).


Inductive simp_pred : cpred -> qpred -> (cpred * qpred) -> Prop :=
   | simp_pred_empty : forall W, simp_pred W nil (W,nil)
   | simp_pred_many : forall W W' W'' P P' s v a,
            simp_pred W P (W',P') -> simp_pred_elem W' s v (W'',a) -> simp_pred W ((s,v)::P) (W'',a::P').


Inductive triple {rmax:nat} : 
          atype -> aenv -> type_map -> cpred*qpred -> pexp -> cpred*qpred -> Prop :=
      | triple_frame: forall q env T T1 T' l W W' P Q e R, type_check_proof rmax q env T T1 (W,P) (W',Q) e ->
           fv_pexp env e l -> sub_qubits l (dom_to_ses(dom T)) -> sub_qubits (dom_to_ses (freeSesQPred R)) (dom_to_ses(dom T'))
         -> dis_qubits (dom_to_ses(dom T)) (dom_to_ses(dom T')) -> triple q env T (W,P) e (W',Q) -> triple q env (T++T') (W,P++R) e (W',Q++R)
      | triple_con_1: forall q env T T1 T' P P' Q e, type_check_proof rmax q env T' T1 P' Q e -> 
            imply rmax P P' -> env_equiv T T' -> triple q env T' P' e Q -> triple q env T P e Q
      | triple_con_2: forall q env T T' T1 P Q Q' e, type_check_proof rmax q env T T' P Q' e -> 
            imply rmax Q' Q -> env_equiv T' T1 -> pred_check env T1 Q  -> triple q env T P e Q' -> triple q env T P e Q
      | skip_pf: forall q env T P, triple q env T P PSKIP P

      | let_c_pf: forall q env T T1 P x v e Q,
            type_check_proof rmax q env T T1 P Q (subst_pexp e x v) ->
            triple q env T P (subst_pexp e x v) Q -> triple q env T P (Let x (AE (Num v)) e) Q
      | let_m_pf: forall q env T T1 W P x a e Q,
            type_check_proof rmax q (AEnv.add x (Mo MT) env) T T1 ((CEq (BA x) a)::W,P) Q e ->
            type_aexp env a (Mo MT,nil) -> ~ AEnv.In x env ->
            triple q (AEnv.add x (Mo MT) env) T ((CEq (BA x) a)::W,P) e Q -> triple q env T (W,P) (Let x (AE a) e) Q

      | let_q_pf:  forall q env T T1 W P P' x v y n l e Q,
              type_check_proof rmax q (AEnv.add x (Mo MT) env) ((l, CH) :: T) T1 P' Q e ->
            AEnv.MapsTo y (QT n) env ->  ~ AEnv.In x env ->
            simp_pred W ((FM x n (SV l),v)::P) P' ->
            triple q (AEnv.add x (Mo MT) env) ((l,CH)::T) P' e Q
            -> triple q env (((y,BNum 0,BNum n)::l,CH)::T) (W,(SV ((y,BNum 0,BNum n)::l),v)::P) (Let x (Meas y) e) Q.
(*
      | apph_pf: forall q env T x n l b, type_vari env x (QT n,l) -> find_type T l (Some (l,TNor)) ->
            triple q env T ([SEq (SV l) (Nval (C1) b)]) (AppSU (RH x)) ([SEq (SV l) (Hval (fun i => (update allfalse 0 (b i))))])
      | appu_pf : forall q env T l l1 m b e ba,  find_type T l (Some (l++l1,CH)) ->
                eval_ch rmax env l m b e = Some ba ->
                triple q env T ([SEq (SV (l++l1)) (Cval m b)]) (AppU l e) ([SEq (SV (l++l1)) (Cval m ba)]).
      | dis_pf : forall q env T x n l l1 n' m f m' acc, type_vari env x (QT n,l) -> find_type T l (Some (l++l1,CH)) ->
                 ses_len l1 = Some n' -> dis_sem n n' m m f nil (m',acc) -> 
                triple q env T ([SEq (SV (l++l1)) (Cval m f)]) (Diffuse x) ([SEq (SV (l++l1)) (Cval m' acc)])

      | for_pf : forall q env T x l h b p P i, l <= i < h ->
            triple q env T (cpred_subst_c P x i) (If (subst_bexp b x i) (subst_pexp p x i)) (cpred_subst_c P x (i+1)) ->
            triple q env T (cpred_subst_c P x l) (For x (Num l) (Num h) b p) (cpred_subst_c P x h)
      | if_c_1 : forall q env T P Q b e, simp_bexp b = Some true ->
                 triple q env T P e Q -> triple q env T P (If b e) Q
      | if_c_2 : forall q env T P b e, simp_bexp b = Some false ->
                 triple q env T P e P -> triple q env T P (If b e) P
      | if_q : forall q env T T' P P' Pa Q Q' Qa b e n l l1, type_bexp env b (QT n,l) -> find_type T l (Some (l++l1,CH)) ->
                  up_type T l1 CH T' -> subst_ses_cpred P (l++l1) (Frozen b (SV l) (SV l1)) P' -> pred_check q env ([(l1,CH)]) Q' ->
                subst_ses_cpred P (l++l1) (Unfrozen n (BNeg b) (SV (l++l1))) Pa ->
                subst_ses_cpred Q' l1 (Unfrozen n b (SV (l++l1))) Qa ->
                  triple q env T' P' e (Q++Q') -> triple q env T P (If b e) (Pa++Qa)
      | seq_pf: forall q env tenv tenv' tenv'' P R Q e1 e2,
             @session_system rmax q env tenv e1 tenv' -> up_types tenv tenv' tenv'' -> pred_check q env tenv'' R ->
             triple q env tenv P e1 R -> triple q env tenv'' R e1 Q -> triple q env tenv P (PSeq e1 e2) Q.
*)

Lemma env_equiv_sub: forall l s s', @env_equiv s s' -> 
          sub_qubits l (dom_to_ses (dom s)) -> sub_qubits l (dom_to_ses (dom s')).
Proof.
Admitted.

Lemma env_equiv_dis: forall (s1 s s' : type_map), @env_equiv s s' -> 
          dis_qubits (dom_to_ses (dom s)) (dom_to_ses (dom s1)) 
       -> dis_qubits (dom_to_ses (dom s')) (dom_to_ses (dom s1)).
Proof.
Admitted.

Lemma env_state_eq_dom: forall tenv s, env_state_eq tenv s -> (dom tenv) = dom s.
Proof.
  intros. induction H; try easy.
  unfold dom in *. simpl in *.
  destruct (split l1) eqn:eq1.
  destruct (split l2) eqn:eq2. simpl in *; subst. easy.
Qed.

Lemma session_system_local: forall rmax t env e l T T' T1, 
 fv_pexp env e l -> sub_qubits l (dom_to_ses (dom T)) -> dis_qubits (dom_to_ses (dom T)) (dom_to_ses (dom T1)) ->
    @session_system rmax t env T e T' -> @session_system rmax t env (T++T1) e (T'++T1).
Proof.
  intros.
  induction H2; simpl in *.
  apply env_equiv_sub with (s' := T2) in H0; try easy.
  apply env_equiv_dis with (s' := T2) in H1; try easy.
  specialize (IHsession_system H H0 H1).
  apply env_equiv_cong with (S3 := T1) in H2.
  apply env_equiv_ses with (T5 := ((T2 ++ T1))); try easy.
  constructor.
Admitted.

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

Lemma qpred_state_consist: forall rmax T T' q q' P P', env_equiv T T' -> @state_equiv rmax q q' 
         -> env_state_eq T q -> env_state_eq T' q' -> qpred_check T P -> qpred_check T' P' -> @qpred_equiv rmax P P'
         -> qmodel q P -> qmodel q' P'.
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

Lemma qpred_equiv_state_eq: forall rmax s P Q, @qpred_equiv rmax P Q -> qmodel s P -> exists s', qmodel s' Q /\ @state_equiv rmax s s'.
Proof.
  intros. generalize dependent s. induction H; intros;simpl in *.
  exists s. split. easy. constructor.
  inv H0. exists s0. split. easy. apply state_empty.
  assert (G := H0).
  apply qmodel_app in H0 as [q1 [q2 [X1 X2]]]. subst.
  exists (q2++q1). split.
  apply qmodel_shrink in G as X3; try easy. apply qmodel_shrink_1 in G as X4; try easy.
  apply qmodel_combine; try easy.
  apply state_comm.
Admitted.

Definition kind_env_stack_full (env:aenv) (s:stack) : Prop :=
  forall x, AEnv.MapsTo x (Mo MT) env <-> AEnv.In x s.

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

Lemma simp_pred_simple: forall W P Q, simp_pred W P Q -> simple_qpred (snd Q).
Proof.
  intros. induction H; unfold simple_qpred in *; intros;simpl in *.
  constructor.
  constructor. inv H0. constructor. constructor. easy.
Qed. 

Lemma simple_qpred_simp: forall W P, simple_qpred P -> simp_pred W P (W,P).
Proof.
  intros. induction H. constructor. destruct x.
  apply simp_pred_many with (W' := W); try easy.
  inv H. constructor.
Qed.

Lemma simp_pred_elem_same : forall W s v P Q, simp_pred_elem W s v P -> simp_pred_elem W s v Q -> P = Q.
Proof.
  intros. generalize dependent Q.
  induction H; intros; simpl in *.
  inv H0. easy.
  inv H1.
Admitted.

Lemma simp_pred_same: forall W P Q Q', simp_pred W P Q -> simp_pred W P Q' -> Q = Q'.
Proof.
  intros. generalize dependent Q'.
  induction H; intros;simpl in *. inv H0. easy.
  inv H1. apply IHsimp_pred in H7. inv H7.
  apply simp_pred_elem_same with (P := (W''0,a0)) in H0; try easy.
  inv H0. easy.
Qed.

Lemma pick_mea_exist_same: forall n n0 m ba bl r v, n <= n0 ->
    (forall j : nat, j < m -> fst (bl j) = fst (ba j) /\ (forall i : nat, i < n0 -> snd (bl j) i = snd (ba j) i)) ->
     pick_mea n (Cval m ba) (r, v) -> pick_mea n (Cval m bl) (r, v).
Proof.
  intros. remember (r,v) as V. inv H1. inv H6.
  specialize (H0 i). assert (i < m) by lia. apply H0 in H1.
  destruct H1. destruct (bl i) eqn:eq1. simpl in *. rewrite H7 in H1. simpl in *. subst.
  rewrite H7 in H2. simpl in *.
  assert (a_nat2fb bl0 n = a_nat2fb b n).
  clear H0 eq1 H5 H7. unfold a_nat2fb. induction n; intros;simpl in *. easy.
  rewrite IHn; try lia.
  specialize (H2 n). rewrite H2 ; try lia.
  rewrite H1.
  apply pick_meas with (i := i); try easy.
Qed.

Lemma build_state_ch_exist_same: forall n n0 m ba bl v, n <= n0 ->
    (forall j : nat, j < m -> fst (bl j) = fst (ba j) /\ (forall i : nat, i < n0 -> snd (bl j) i = snd (ba j) i)) ->
     build_state_ch n v (Cval m ba) = build_state_ch n v (Cval m bl).
Proof.
  intros. unfold build_state_ch.
  assert ((to_sum_c m n v ba) = (to_sum_c m n v bl)).
  induction m; intros; simpl in *. easy.
  assert ((forall j : nat,
       j < m ->
       fst (bl j) = fst (ba j) /\
       (forall i : nat, i < n0 -> snd (bl j) i = snd (ba j) i))).
  intros. apply H0. lia. apply IHm in H1.
  assert (a_nat2fb (@snd C rz_val (ba m)) n = a_nat2fb (@snd C rz_val (bl m)) n).
  clear H1 IHm.
  unfold a_nat2fb in *. induction n;intros;simpl in *. easy.
  rewrite IHn; try lia.
  specialize (H0 m). assert (m < S m) by lia. apply H0 in H1. destruct H1.
  rewrite H2; try lia. easy.
  rewrite H2. rewrite H1.
  assert ((@fst C rz_val (ba m)) = ((@fst C rz_val (bl m)))).
  specialize (H0 m). assert (m < S m) by lia.
  apply H0 in H3. destruct H3. easy. rewrite H3. easy.
  rewrite H1. remember (to_sum_c m n v bl) as f. clear H1. clear Heqf.
  assert (build_state_pars m n v f ba = build_state_pars m n v f bl).
  induction m; intros;simpl in *. easy.
  assert ((forall j : nat,
       j < m ->
       fst (bl j) = fst (ba j) /\
       (forall i : nat, i < n0 -> snd (bl j) i = snd (ba j) i))).
  intros. apply H0. lia. apply IHm in H1.
  assert (a_nat2fb (@snd C rz_val (ba m)) n = a_nat2fb (@snd C rz_val (bl m)) n).
  clear H1 IHm.
  unfold a_nat2fb in *. induction n;intros;simpl in *. easy.
  rewrite IHn; try lia.
  specialize (H0 m). assert (m < S m) by lia. apply H0 in H1. destruct H1.
  rewrite H2; try lia. easy.
  rewrite H2.
Admitted.

Lemma proof_soundness: forall e rmax t env s tenv tenv' P Q, 
     @env_state_eq tenv (snd s) -> kind_env_stack_full env (fst s) ->
      type_check_proof rmax t env tenv tenv' P Q e -> freeVarsNotCPExp env e -> @qstate_wt (snd s) -> simple_tenv tenv ->
    @triple rmax t env tenv P e Q -> simple_qpred (snd P) -> model s P -> 
          (exists W sa sb, model (W,sa) Q  /\ @qfor_sem rmax env s e (W,sb) /\ @state_equiv rmax sb sa).
Proof.
  intros. generalize dependent s. generalize dependent tenv'. induction H5; intros;simpl in *.
 -
  assert (simple_tenv T).
  unfold simple_tenv in *. intros. apply H4 with (b := b). apply in_app_iff.
  left. easy.
  assert (XX1 := H).
  destruct H as [X1 [X2 X3]].
  apply session_system_local with (l := l) (T1 := T') in X2 as X4; try easy.
  destruct s;simpl in *.
  apply env_state_eq_app in H9 as [q1 [q2 [X5 [X6 X7]]]].
  apply env_state_eq_same_length in X5 as [X8 X9]; try easy. subst.
  assert (qstate_wt q1).
  unfold qstate_wt in *. intros. apply H11 with (s := s0) (bl := bl). apply in_app_iff.
  left. easy.
  apply simple_qpred_shrink in H6 as X10.
  specialize (IHtriple H2 H13 X10 T1 XX1 (s,q1) X8 H10 H).
  unfold model in *; simpl in *. destruct H12 as [Y1 Y2].
  destruct X1 as [Y3 Y4]; simpl in *.
  apply qpred_check_length_same in Y4. rewrite Y4 in X7.
  apply qmodel_shrink in Y2 as Y5; try easy. assert (cmodel s W /\ qmodel q1 P) by easy.
  destruct (IHtriple H9) as [Wa [sa [sb [Y6 [Y7 Y8]]]]]. destruct Y6.
  exists Wa, (sa++q2), (sb++q2). split. split. easy.
  apply qmodel_shrink_1 in Y2 as Y9; try easy.
  apply qmodel_combine; try easy.
  apply env_state_eq_dom in X8. apply env_state_eq_dom in X9.
  rewrite X8 in *. rewrite X9 in *. split.
  apply qfor_sem_local with (l := l) ; try easy.
  apply state_equiv_add. easy.
 -
  apply env_equiv_simple_type in H1 as X1; try easy.
  apply simple_qpred_imply with (rmax := rmax) (Q := P') in H6 as X2; try easy.
  specialize (IHtriple H2 X1 X2 T1 H).
  inv H0. destruct s.
  unfold model in *; simpl in *. destruct H10 as [Y1 Y2].
  destruct H as [Y3 [Y4 Y5]]. destruct Y3 as [Y6 Y7].
  destruct H3 as [Y8 Y9]. destruct Y8 as [Y10 Y11]. simpl in *.
  apply (qpred_check_consist T T' P0 X2) in Y11 as Y12; try easy; subst.
  specialize (IHtriple (s,q0) H7 H8 H9).
  apply H11 in Y1 as Y3. simpl in *.
  assert (cmodel s W' /\ qmodel q0 P0) by easy.
  destruct (IHtriple H) as [Wa [sa [sb [G1 [G2 G3]]]]].
  exists Wa,sa,sb. easy.
  assert (X5 := H1).
  apply env_state_eq_trans with (r := rmax) (S := snd s) in H1 as [sa [X6 X7]]; try easy.
  destruct s. destruct H10 as [X8 X9].
  destruct H as [Y1 [Y2 Y3]]. destruct Y1 as [Y1 Y4].
  destruct H3 as [Y5 [Y6 Y7]]. destruct Y5 as [Y5 Y8].
  simpl in *.
  apply qpred_state_consist with (rmax:=rmax) (q := q0) (q' := sa) (P := P0) (P' := Q0) in X5 as G1; try easy.
  apply qstate_wt_eq in X6 as G2; try easy.
  assert (model (s,sa) (W,Q0)).
  split. easy. easy.
  destruct (IHtriple (s,sa) X7 H8 G2 H) as [Wa [sb [sb' [G3 [G4 G5]]]]].
  exists Wa,sb,sb'. split. easy. split.
  apply state_eq_sem with (f' := sa); try easy. easy.
 -
  destruct (IHtriple H2 H4 H6 T' H s H8 H9 H10 H11) as [Wa [sa [sb [X1 [X2 X3]]]]].
  inv H0. destruct X1. simpl in *. apply H12 in H0.
  exists Wa,sa,sb. easy. destruct H3. destruct X1; simpl in *.
  apply qpred_equiv_state_eq  with (s:= sa) in H12 as [sc [G1 G2]]; try easy.
  exists Wa,sc,sb. split. easy. split. easy. apply state_equiv_trans with (S2 := sa); try easy.
 - 
  destruct s. exists s,q0,q0. split. easy.
  split. constructor. constructor.
 - 
  apply freeVars_pexp_in with (v := v) in H2 as X1; try easy.
  destruct (IHtriple X1 H4 H6 T1 H s H0 H3 H7 H8) as [Wa [sa [sb [X2 [X3 X4]]]]].
  exists Wa,sa,sb. split. easy.
  split. apply let_sem_c with (n := v); try easy.
  easy.
 -
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H12. inv H12. easy.
  apply AEnv.add_3 in H12; try lia.
  apply H2 with (x0 := x0). simpl.
  apply in_app_iff. right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  destruct s; simpl in *.
  apply kind_env_stack_exist with (s := s) in H0 as X1. destruct X1 as [va X1].
  assert (kind_env_stack_full (AEnv.add x (Mo MT) env) (AEnv.add x va s)).
  unfold kind_env_stack_full. intros. split. intros.
  bdestruct (x0 =? x); subst.
  exists va. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H12; try easy.
  unfold AEnv.In,AEnv.Raw.PX.In in *.
  apply H8 in H12. destruct H12. exists x1. apply AEnv.add_2. lia. easy. lia.
  intros. destruct H12.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H12. subst.
  apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia.
  apply H8. apply AEnv.add_3 in H12; try lia. exists x1. easy.
  specialize (IHtriple H11 H4 H6 T1 H ((AEnv.add x va s),q0) H7 H12 H9).
  destruct H10 as [X2 X3]. simpl in *.
  assert (cmodel (AEnv.add x va s) (CEq (BA x) a :: W)).
  constructor. 
  apply eval_aexp_not_exists with (x := x) (v := va) in X1; try easy.
  destruct va.
  apply ceq_asem with (s := (AEnv.add x (r, n) s)) (x := BA x) (y := a) (r1 := r) (r2 := r) (n1 := n) (n2 := n) ; try easy.
  apply var_sem. apply AEnv.add_1. easy. intros R. apply H8 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  unfold cmodel in X2.
  assert (~ AEnv.In x s). intros R. apply H8 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  clear H H0 X1 H5 H6 IHtriple H3 H7 H8 H9 X3 H11 H12.
  induction X2. constructor. constructor.
  apply eval_cabexp_not_exists. easy. easy. easy.
  assert (model (AEnv.add x va s, q0) (CEq (BA x) a :: W, P)).
  split. simpl in *. apply H10. easy.
  destruct (IHtriple H13) as [Wa [sa [sb [Y1 [Y2 Y3]]]]].
  exists Wa, sa, sb. split. easy. split. apply let_sem_m with (n := va); try easy. easy.
  unfold SessionKind.kind_env_stack, kind_env_stack_full in *. intros. apply H8. easy.
  unfold freeVarsNotCPExp,freeVarsNotCAExp in *. intros. simpl in *. apply H2 with (x0 := x0); try easy.
  apply in_app_iff. left. easy.
 -
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H13. inv H13. easy.
  apply AEnv.add_3 in H13; try lia.
  apply H2 with (x0 := x0). simpl.
  right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  assert (simple_tenv ((l, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H13. inv H13.
  specialize (H4 ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
     In ((y, BNum 0, BNum n) :: a, CH) T). left. easy.
  apply H4 in H13.
  inv H13. easy. apply H4 with (b:= b). right. easy.
  apply simp_pred_simple in H3 as X1. inv H6. inv H3.
  apply simple_qpred_simp with (W := W) in H17 as X2; try easy.
  specialize (IHtriple H12 H13 X1 T1 H).
  apply simp_pred_same with (Q := (W', P'0)) in X2; try easy. inv X2.
  destruct H as [X2 [X3 X4]].
  destruct s. destruct H11. simpl in *. inv H21.
  inv H8. inv H21. inv H3. inv H22.
  specialize (IHtriple ((AEnv.add x (r,v0) s, (l,va')::l2))).
  assert (X5 := H19).
  apply mask_state_exists in H19 as [na [pa [Y1 Y2]]].
  rewrite H24 in Y1. inv Y1.
  assert (env_state_eq ((l, CH) :: T)
             (snd (AEnv.add x (r, v0) s, (l, Cval na pa) :: l2))).
  constructor; try easy. constructor.
  assert (kind_env_stack_full (AEnv.add x (Mo MT) env)
             (fst (AEnv.add x (r, v0) s, (l, Cval na pa) :: l2))).
  unfold kind_env_stack_full in *. intros. split.
  intros. bdestruct (x0 =? x); subst. exists (r,v0). apply AEnv.add_1. easy.
  apply AEnv.add_3 in H6; try lia. apply H9 in H6. destruct H6.
  exists x1. apply AEnv.add_2. lia. easy.
  intros. bdestruct (x0 =? x); subst. apply AEnv.add_1. easy. destruct H6.
  apply AEnv.add_3 in H6; try lia. assert (AEnv.In x0 s). exists x1. easy. apply H9 in H11.
  apply AEnv.add_2. lia. easy.
  assert (qstate_wt (snd (AEnv.add x (r, v0) s, (l, Cval na pa) :: l2))).
  unfold qstate_wt in *. intros. simpl in *. destruct H8. inv H8. lia. apply (H10 s0 m0 bl0). right. easy.
  assert (model (AEnv.add x (r, v0) s, (l, Cval na pa) :: l2)
             (CEq (BA x) (MNum r v0) :: W, (SV l, Cval na pa) :: P)).
  split. simpl.
  constructor. apply ceq_asem with (r1 := r) (r2 := r) (n1 := v0) (n2 := v0); try easy.
  constructor. apply AEnv.add_1. easy. constructor.
  unfold cmodel in H.
  assert (~ AEnv.In x s). intros R. apply H9 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  clear X2 X3 X4 X5 H0 H1 H5 X1 IHtriple H7 H9 H10 H12 H13 H16 H17 H20 H24 Y2 H18 H15 H23 H14 H3 H6 H8.
  induction H. constructor. constructor.
  apply eval_cabexp_not_exists. easy. easy. easy.
  simpl in *.
  assert (exists nb, ses_len l = Some nb).
  unfold ses_len in *.
  destruct (get_core_ses ((y, BNum 0, BNum n) :: l)) eqn:eq1; try easy. simpl in *.
  destruct (get_core_ses l) eqn:eq2; try easy. inv eq1. simpl in *.
  exists (ses_len_aux l1). easy. destruct H11.
  apply model_many with (n := x0); try easy.
  constructor. intros. split. easy. intros. easy.
  destruct (IHtriple H3 H6 H8 H11) as [Wa [sa [sb [G1 [G2 G3]]]]].
  exists Wa,sa,sb.
  split. easy.
  split. 
  assert (n <= n0).
  unfold ses_len in *.
  unfold ses_len in *.
  destruct (get_core_ses ((y, BNum 0, BNum n) :: l)) eqn:eq1; try easy. simpl in *.
  destruct (get_core_ses l) eqn:eq2; try easy. inv eq1. simpl in *.
  inv H15. lia.
  apply let_sem_q with (r0 := r) (v := v0) (va' := Cval na pa); try easy.
  apply pick_mea_exist_same with (n0 := n0) (ba := r2); try easy.
  rewrite build_state_ch_exist_same with (n0 := n0) (bl := bl) in H24; try easy. easy.
Qed.

