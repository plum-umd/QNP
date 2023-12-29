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
Require Import QafnySyntax.
Require Import LocusDef.
Require Import LocusKind.
Require Import LocusType.
Require Import LocusSem.
Require Import LocusTypeProof.
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
Definition locus :Set := (var * nat * nat).
Definition atpred_elem :Type := (list locus * se_type).
Definition atpred := list atpred_elem.
*)

(*
TODO: define apply operation with few different applications:
1: switching: mimicing the locus position switching equivalence relation.
2. masking: mimicing the partial measurement.
3. oracle function application using oracle semantics.
4. if conditional as entanglement.
5. H/QFT state prepreation.
*)

(*
Inductive sval := ST (x:state_elem) | SV (s:locus)
               | Mask (y:sval) (u:nat) (z:aexp) | AppA (x:exp) (y:sval)
               | FSL (e:sval) (l:locus) (s:nat)
               | SSL (e:sval) (a:sval) (b:bexp) (l1:locus) (l2:locus).
*)

Inductive sval := SV (s:locus) | Frozen (b:bexp) (s:sval) (s:sval) 
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
(*
     | qpred_ses_eq: forall s s' v S, ses_eq s s' -> qpred_equiv ((SV s,v)::S) ((SV s',v)::S)

     | qpred_sub: forall x v n u a, ses_len x = Some n -> @state_same rmax n v u -> qpred_equiv ((SV x,v)::a) ((SV x,u)::a)

     | qpred_mut: forall l1 l2 n a n1 b n2 v u S, ses_len l1 = Some n -> ses_len ([a]) = Some n1 -> ses_len ([b]) = Some n2 ->
            mut_state n n1 n2 v u -> qpred_equiv ((SV (l1++(a::b::l2)),v)::S) ((SV (l1++(b::a::l2)),u)::S)
*)
     | qpred_merge: forall x n v y u a vu, ses_len x = Some n -> 
                       @times_state rmax n v u vu -> qpred_equiv ((SV x,v)::((SV y,u)::a)) ((SV (x++y),vu)::a)
     | qpred_split: forall x n y v v1 v2 a, ses_len x = Some n -> 
                  @split_state rmax n v (v1,v2) -> qpred_equiv ((SV (x++y),v)::a) ((SV x,v1)::(SV y,v2)::a).

Axiom qpred_equiv_cong: forall rmax a P a1 P', @qpred_equiv rmax (a::P) (a1::P')
         -> @qpred_equiv rmax ([a]) ([a1]) /\ @qpred_equiv rmax P P'.

Fixpoint sval_subst_c t x v :=
  match t with SV s => SV (subst_locus s x v)
              | Frozen b s s' => Frozen (subst_bexp b x v) (sval_subst_c s x v) (sval_subst_c s' x v)
              | Unfrozen n b s => Unfrozen n (subst_bexp b x v) (sval_subst_c s x v)
              | FM y n rv s => FM y n rv (sval_subst_c s x v)
  end.

Definition qelem_subst_c (t: qpred_elem) x v := (sval_subst_c (fst t) x v,snd t).

Definition pred_subst_c (t: cpred * qpred) x v :=
    (List.map (fun a => subst_cbexp a x v) (fst t), List.map (fun a => qelem_subst_c a x v) (snd t)).


Definition sublist (l:list var) (env:aenv) := Forall (fun b => AEnv.In b env) l.

Fixpoint freeSesSV (a:sval) := match a with SV s => [s]
         | Frozen b s s' => freeSesSV s'
         | Unfrozen n b s => freeSesSV s
         | FM x n rv s => freeSesSV s
  end.

Definition freeSesQPred (l:qpred) := List.fold_right (fun b a => freeSesSV (fst b)++a) nil l.

Definition freeSesPred (a:cpred * qpred) := (freeSesQPred (snd a)).

Inductive subst_ses_sval : sval -> locus -> sval -> sval -> Prop :=
   subst_ses_svt : forall x v, subst_ses_sval (SV x) x v v
   | subst_ses_svf : forall x y v, x <> y -> subst_ses_sval (SV y) x v v
   | subst_ses_unf : forall x v s n b v', subst_ses_sval s x v v' -> subst_ses_sval (Unfrozen n b s) x v (Unfrozen n b v')
   | subst_ses_fm : forall x v s y n rv v', subst_ses_sval s x v v' -> subst_ses_sval (FM y n rv s) x v (FM y n rv v').

Inductive subst_ses_qpred : qpred -> locus -> sval -> qpred -> Prop :=
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
   | resolve_unfrz_many_2 : forall l l1 q m f f' fc b n n1, ses_len l = Some n -> ses_len l1 = Some n1 ->
          eval_bexp ([(l++l1,Cval m f)]) b ([(l++l1,Cval m f')]) -> assem_bool n n1 m f' q fc ->
       resolve_unfrz ((Unfrozen n (BNeg b) (SV (l++l1)),Cval m f)::[((Unfrozen n b (SV (l++l1)),q))]) ([(SV (l++l1),fc)]).

Fixpoint ses_in (s:locus) (l:list locus) :=
  match l with nil => False
       | (a::xl) => ((ses_eq a s) \/ (ses_in s xl))
  end.

Fixpoint ses_sublist (s:list locus) (l:list locus) :=
  match s with nil => True
       | (a::xl) => ((ses_in a l) \/ (ses_sublist xl l))
  end.

Definition cpred_check (l:cpred) (env:aenv) := Forall (fun b => sublist (freeVarsCBexp b) env) l.

Inductive sval_check : locus -> sval -> Prop :=
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
    | clt_asem : forall s x y r1 r2 n1 n2, eval_aexp s x (r1,n1) -> eval_aexp s y (r2,n2)
         -> r1 = r2 -> n1 < n2 -> eval_cabexp s (CB (CLt x y))
    | bneq_asem: forall s e, eval_cabexp s e -> eval_cabexp s (BNeg e).

Definition cmodel (s:stack) (l:cpred) : Prop := Forall (fun b => eval_cabexp s (CB b)) l.

Definition model (s:state) (P:cpred * qpred) := cmodel (fst s) (fst P) /\ qmodel (snd s) (snd P).

Inductive imply (rmax:nat) : cpred * qpred -> cpred * qpred -> Prop :=
  | imply_cpred : forall W W' P, (forall s, cmodel s W -> cmodel s W') -> imply rmax (W,P) (W',P)
  | imply_qpred: forall W P Q, @qpred_equiv rmax P Q -> imply rmax (W,P) (W,Q).

Definition type_check_proof (rmax :nat) (t:atype) (env:aenv) (T T':type_map) (P Q:cpred * qpred) e :=
   pred_check env T P /\  @locus_system rmax t env T e T' /\ pred_check env T' Q.

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
      | triple_frame: forall q env T T1 T' W W' P Q e R, 
                    type_check_proof rmax q env T T1 (W,P) (W',Q) e ->
(*           fv_pexp env e l -> sub_qubits l (dom_to_ses(dom T)) 
                  -> sub_qubits (dom_to_ses (freeSesQPred R)) (dom_to_ses(dom T'))
         -> dis_qubits (dom_to_ses(dom T)) (dom_to_ses(dom T')) 
*)
              triple q env T (W,P) e (W',Q) -> triple q env (T++T') (W,P++R) e (W',Q++R)
      | triple_con_1: forall q env T T1 P P' Q e, type_check_proof rmax q env T T1 P' Q e -> 
            imply rmax P P' -> triple q env T P' e Q -> triple q env T P e Q
      | triple_con_2: forall q env T T1 P Q Q' e, type_check_proof rmax q env T T1 P Q' e -> 
            imply rmax Q' Q -> pred_check env T1 Q -> triple q env T P e Q' -> triple q env T P e Q
      | skip_pf: forall q env T P, triple q env T P PSKIP P

      | let_c_pf: forall q env T T1 P x a v e Q,
             ~ AEnv.In x env ->
            simp_aexp a = Some v ->
            type_check_proof rmax q env T T1 P Q (subst_pexp e x v) ->
            triple q env T P (subst_pexp e x v) Q -> triple q env T P (Let x a e) Q
      | let_m_pf: forall q env T T1 W P x a e Q,
            type_check_proof rmax q (AEnv.add x (Mo MT) env) T T1 ((CEq (BA x) a)::W,P) ((CEq (BA x) a)::W,Q) e ->
            type_aexp env a (Mo MT,nil) -> ~ AEnv.In x env ->
            triple q (AEnv.add x (Mo MT) env) T ((CEq (BA x) a)::W,P) e ((CEq (BA x) a)::W,Q)
              -> triple q env T (W,P) (Let x (AE a) e) (W,Q)

      | let_q_pf:  forall env T T1 W P PM x v y n r' v' l e Q,
              type_check_proof rmax CT (AEnv.add x (Mo MT) env) ((l, CH) :: T) T1 
                            ((CEq (BA x) (MNum r' v'))::W,PM::P) ((CEq (BA x) (MNum r' v'))::W,Q) e ->
            AEnv.MapsTo y (QT n) env ->  ~ AEnv.In x env ->
            simp_pred_elem (FM x n (r',v') (SV l)) v PM ->
            triple CT (AEnv.add x (Mo MT) env) ((l,CH)::T) ((CEq (BA x) (MNum r' v'))::W,PM::P) e ((CEq (BA x) (MNum r' v'))::W,Q)
            -> triple CT env (((y,BNum 0,BNum n)::l,CH)::T) (W,(SV ((y,BNum 0,BNum n)::l),v)::P) (Let x (Meas y) e) (W,Q)

      | appu_nor_pf : forall q env W l r b e ra ba, eval_nor rmax env l r b e = Some (ra,ba) ->
                triple q env ([(l,TNor)]) (W,([(SV (l),Nval r b)])) (AppU l e) (W, ([(SV (l),Nval ra ba)]))
      | appu_ch_pf : forall q env W l l1 m b e ba, eval_ch rmax env l m b e = Some ba ->
                triple q env ([(l++l1,CH)]) (W,([(SV (l++l1),Cval m b)])) (AppU l e) (W, ([(SV (l++l1),Cval m ba)]))
      | apph_nor_pf: forall q env W p a r b n, @simp_varia env p a -> ses_len ([a]) = Some n ->
            triple q env ([([a], TNor)]) (W,([(SV ([a]),Nval r b)])) (AppSU (RH p)) (W, ([(SV ([a]),(Hval (eval_to_had n b)))]))

      | apph_had_pf: forall q env W p a b n, @simp_varia env p a -> ses_len ([a]) = Some n ->
            triple q env ([([a], THad)]) (W,([(SV ([a]),Hval b)])) (AppSU (RH p)) (W, ([(SV ([a]),(Nval C1 (eval_to_nor n b)))]))
      | if_c_t : forall q env T T1 P Q b e, type_check_proof rmax q env T T1 P Q e -> simp_bexp b = Some true ->
                 triple q env T P e Q -> triple q env T P (If b e) Q
      | if_c_f : forall q env T P b e, simp_bexp b = Some false -> triple q env T P (If b e) P
      | if_q : forall q env W W' P P' P'' Q Pa Qa Qa' b e n l l1, type_bexp env b (QT n,l) -> 
                    type_check_proof rmax MT env ([(l1,CH)]) ([(l1,CH)]) (W,P'') (W',Q) e -> ses_len l = Some n ->
                   subst_ses_qpred P (l++l1) (Frozen b (SV l) (SV l1)) P' -> resolve_frozen P' P'' ->
                subst_ses_qpred P (l++l1) (Unfrozen n (BNeg b) (SV (l++l1))) Pa ->
                simple_qpred Q -> subst_ses_qpred Q l1 (Unfrozen n b (SV (l++l1))) Qa -> resolve_unfrz (Pa++Qa) Qa' ->
                  triple MT env ([(l1,CH)]) (W,P'') e (W',Q) -> triple q env ([(l++l1,CH)]) (W,P) (If b e) (W',Qa')

      | for_pf_f : forall q env T x l h b p P, h <= l -> triple q env T P (For x (Num l) (Num h) b p) P

      | for_pf : forall q env T x l h b p P, ~ AEnv.In x env -> l < h ->
            (forall i, l <= i < h -> type_check_proof rmax q env (subst_type_map T x i) (subst_type_map T x (i+1))
              (pred_subst_c P x i) (pred_subst_c P x (i+1)) (If (subst_bexp b x i) (subst_pexp p x i))) ->
           (forall i, l <= i < h -> 
            triple q env (subst_type_map T x i) (pred_subst_c P x i)
                     (If (subst_bexp b x i) (subst_pexp p x i)) (pred_subst_c P x (i+1))) ->
            triple q env (subst_type_map T x l) (pred_subst_c P x l) (For x (Num l) (Num h) b p) (pred_subst_c P x h)

      | seq_pf: forall q env T T1 T2 P R Q e1 e2,
             type_check_proof rmax q env T T1 P R e1 ->
             type_check_proof rmax q env T1 T2 R Q e2 ->
               triple q env T P e1 R -> triple q env T1 R e2 Q -> triple q env T P (PSeq e1 e2) Q.


Lemma resolve_frozen_simple: forall P a v, resolve_frozen P ([(a,v)]) -> (exists l, a = SV l).
Proof.
  intros. inv H. exists l. easy. exists l1. easy.
Qed.

Lemma env_state_eq_dom: forall tenv s, env_state_eq tenv s -> (dom tenv) = dom s.
Proof.
  intros. induction H; try easy.
  simpl in *. rewrite IHenv_state_eq. easy.
Qed.

Lemma dom_con {A:Type}: forall a (b:list (locus*A)), dom (a::b) = (fst a)::(dom b).
Proof.
  intros. unfold dom in *. simpl in *. destruct a; try easy.
Qed.

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

Lemma simple_qpred_shrink_l: forall P Q, simple_qpred (P++Q) -> simple_qpred P.
Proof.
  intros. unfold simple_qpred in *.
  remember (P++Q) as A. generalize dependent P. generalize dependent Q. induction H; intros;simpl in *.
  symmetry in HeqA. apply app_eq_nil in HeqA. destruct HeqA;subst.
  constructor. destruct P. simpl in *. constructor.
  inv HeqA. constructor; try easy. apply (IHForall Q). easy.
Qed.

Lemma simple_qpred_shrink_r: forall P Q, simple_qpred (P++Q) -> simple_qpred Q.
Proof.
  intros. unfold simple_qpred in *.
  remember (P++Q) as A. generalize dependent P. generalize dependent Q. induction H; intros;simpl in *.
  symmetry in HeqA. apply app_eq_nil in HeqA. destruct HeqA;subst.
  constructor. destruct P. simpl in *; subst.
  constructor; try easy. inv HeqA. eapply IHForall. easy.
Qed.

Lemma simple_qpred_combine: forall P Q, simple_qpred P -> simple_qpred Q ->  simple_qpred (P++Q).
Proof.
  intros. induction P; intros; simpl in *. easy.
  inv H. constructor; try easy. apply IHP. easy.
Qed.

Definition singleTon (P: qpred) := exists s v, P = ([(s,v)]).

Lemma qpred_equiv_single_same: forall rmax P P', @qpred_equiv rmax P P' -> singleTon P -> singleTon P' -> P = P'.
Proof.
  intros. induction H; try easy.
  unfold singleTon in *. destruct H0 as [s1 [v1 X1]]. destruct H1 as [s2 [v2 X2]].
  destruct a1. simpl in *. subst. inv X2. easy.
  simpl in *. inv X1. apply app_eq_nil in H1. destruct H1; subst. simpl in *. easy.
  unfold singleTon in *. destruct H0 as [s1 [v1 X1]]. destruct H1 as [s2 [v2 X2]].
  inv X1. inv X2. easy.
  unfold singleTon in *. destruct H0 as [s1 [v1 X1]]. destruct H1 as [s2 [v2 X2]].
  inv X1.
  unfold singleTon in *. destruct H0 as [sa [va X1]]. destruct H1 as [sv [vb X2]].
  inv X2.
Qed.

Lemma qpred_state_consist: forall rmax T q P P', env_state_eq T q -> qmodel q P 
      -> qpred_check T P -> qpred_check T P' -> @qpred_equiv rmax P P' -> qmodel q P'.
Proof.
  induction T; intros; simpl in *; try easy.
  inv H. inv H2. constructor.
  inv H. inv H1. inv H0. inv H2.
  apply qpred_equiv_cong in H3. destruct H3 as [A1 A2].
  apply qpred_equiv_single_same in A1 as X1; try easy. inv X1.
  apply IHT with (q := l2) in A2; try easy.
  apply (model_many n); try easy.
  unfold singleTon in *. exists (SV s), v. easy.
  exists s0,v0. easy.
Qed.

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

Lemma pred_check_eq_app: forall T T1 S, simple_qpred S -> qpred_check (T++T1) S
      -> exists b1 b2, S = b1 ++ b2 /\ length b1 = length T /\ qpred_check T b1 /\ qpred_check T1 b2.
Proof.
  induction T;intros; intros; simpl in *; try easy.
  exists nil,S. simpl in *. split; try easy; try constructor. easy.
  split; try constructor. easy.
  inv H0. inv H. inv H2. inv H3.
  apply IHT in H4; try easy.
  destruct H4 as [b1 [b2 [X1 [X2 [X3 X4]]]]]; subst.
  exists ((SV l, v) :: b1),b2. split; try easy.
  split. simpl. rewrite X2. easy.
  split. constructor. constructor. easy.
  easy. easy.
Qed.

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

Lemma build_state_ch_exist_same: forall n n0 m ba bl v na bl', n <= n0 ->
    (forall j : nat, j < m -> fst (bl j) = fst (ba j) /\ (forall i : nat, i < n0 -> snd (bl j) i = snd (ba j) i)) ->
     build_state_ch n v (Cval m bl) = Some (Cval na bl') -> 
     (exists ba', build_state_ch n v (Cval m ba) = Some (Cval na ba') 
           /\ match_value (n0 - n) ((Cval na bl')) (Cval na ba')).
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
  assert (exists pa, build_state_pars m n v f ba = (na,pa)
        /\ match_value (n0-n) (Cval na bl') (Cval na pa)).
  generalize dependent na. generalize dependent bl'.
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
  destruct (IHm H2 p n1) as [pa [X1 X2]]; try easy.
  rewrite X1. exists (update pa n1 ((fst (ba m) / f)%C, lshift_fun (snd (ba m)) n)). split. easy.
  inv X2.
  constructor. intros. split; simpl in *.
  bdestruct (j <? n1).
  repeat rewrite update_index_neq; try lia. apply H5. lia.
  assert (j = n1) by lia; subst.
  repeat rewrite update_index_eq. simpl in *. 
  assert (fst (bl m) = fst (ba m)). apply H0. lia. rewrite <- H6. easy.
  intros.
  bdestruct (j <? n1).
  repeat rewrite update_index_neq; try lia. apply H5. lia. easy.
  assert (j = n1) by lia; subst.
  repeat rewrite update_index_eq. simpl in *. 
  unfold lshift_fun. destruct (H0 m); try lia.
  rewrite H8; try easy. lia. apply IHm in eq1.
  destruct eq1 as [pa [X1 X2]]. exists pa.
  rewrite X1. split. easy. easy. intros. apply H0; try easy. lia.
  destruct H1 as [pa [X1 X2]]. rewrite X1.
  exists pa. split; easy.
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

Lemma eval_eq_bool_same: forall m n size r bl v,
  size < n ->
  (forall j : nat,
     j < m ->
     fst (r j) = fst (bl j) /\
     (forall i : nat, i < n -> snd (r j) i = snd (bl j) i)) ->
    match_value n (Cval m (eval_eq_bool r m size v)) (Cval m (eval_eq_bool bl m size v)).
Proof.
  induction m; intros; constructor; intros; simpl in *; try easy.
  assert (forall j : nat,
     j < m ->
     fst (r j) = fst (bl j) /\
     (forall i : nat, i < n -> snd (r j) i = snd (bl j) i)).
  intros. apply H0. lia. specialize (IHm n size r bl v H H2).
  inv IHm. split.
  bdestruct (j =? m); subst. repeat rewrite update_index_eq.
  simpl in *. specialize (H0 m). assert (m < S m) by lia.
  apply H0 in H1. easy.
  repeat rewrite update_index_neq; try lia.
  specialize (H5 j). assert (j < m) by lia.
  apply H5 in H4. easy.
  intros.
  bdestruct (j =? m); subst. repeat rewrite update_index_eq.
  simpl in *. specialize (H0 m). assert (m < S m) by lia.
  apply H0 in H1.
  destruct H1. repeat rewrite H6; try lia.
  assert (a_nat2fb (@snd C rz_val (r m)) size = (a_nat2fb (@snd C rz_val (bl m)) size)).
  unfold a_nat2fb.
  clear H0 H1 H2 H5 H3 H4. induction size; simpl; try easy.
  rewrite IHsize; try lia. rewrite H6; try lia. easy.
  rewrite H7.
  bdestruct (i =? size); subst.
  repeat rewrite update_index_eq. easy.
  repeat rewrite update_index_neq; try lia.
  rewrite H6; try lia. easy.
  repeat rewrite update_index_neq; try lia.
  assert (j < m) by lia. apply H5 in H6.
  destruct H6. rewrite H7; try lia. easy.
Qed.

Lemma eval_lt_bool_same: forall m n size r bl v,
  size < n ->
  (forall j : nat,
     j < m ->
     fst (r j) = fst (bl j) /\
     (forall i : nat, i < n -> snd (r j) i = snd (bl j) i)) ->
    match_value n (Cval m (eval_lt_bool r m size v)) (Cval m (eval_lt_bool bl m size v)).
Proof.
  induction m; intros; constructor; intros; simpl in *; try easy.
  assert (forall j : nat,
     j < m ->
     fst (r j) = fst (bl j) /\
     (forall i : nat, i < n -> snd (r j) i = snd (bl j) i)).
  intros. apply H0. lia. specialize (IHm n size r bl v H H2).
  inv IHm. split.
  bdestruct (j =? m); subst. repeat rewrite update_index_eq.
  simpl in *. specialize (H0 m). assert (m < S m) by lia.
  apply H0 in H1. easy.
  repeat rewrite update_index_neq; try lia.
  specialize (H5 j). assert (j < m) by lia.
  apply H5 in H4. easy.
  intros.
  bdestruct (j =? m); subst. repeat rewrite update_index_eq.
  simpl in *. specialize (H0 m). assert (m < S m) by lia.
  apply H0 in H1.
  destruct H1. repeat rewrite H6; try lia.
  assert (a_nat2fb (@snd C rz_val (r m)) size = (a_nat2fb (@snd C rz_val (bl m)) size)).
  unfold a_nat2fb.
  clear H0 H1 H2 H5 H3 H4. induction size; simpl; try easy.
  rewrite IHsize; try lia. rewrite H6; try lia. easy.
  rewrite H7.
  bdestruct (i =? size); subst.
  repeat rewrite update_index_eq. easy.
  repeat rewrite update_index_neq; try lia.
  rewrite H6; try lia. easy.
  repeat rewrite update_index_neq; try lia.
  assert (j < m) by lia. apply H5 in H6.
  destruct H6. rewrite H7; try lia. easy.
Qed.

Lemma eval_rlt_bool_same: forall m n size r bl v,
  size < n ->
  (forall j : nat,
     j < m ->
     fst (r j) = fst (bl j) /\
     (forall i : nat, i < n -> snd (r j) i = snd (bl j) i)) ->
    match_value n (Cval m (eval_rlt_bool r m size v)) (Cval m (eval_rlt_bool bl m size v)).
Proof.
  induction m; intros; constructor; intros; simpl in *; try easy.
  assert (forall j : nat,
     j < m ->
     fst (r j) = fst (bl j) /\
     (forall i : nat, i < n -> snd (r j) i = snd (bl j) i)).
  intros. apply H0. lia. specialize (IHm n size r bl v H H2).
  inv IHm. split.
  bdestruct (j =? m); subst. repeat rewrite update_index_eq.
  simpl in *. specialize (H0 m). assert (m < S m) by lia.
  apply H0 in H1. easy.
  repeat rewrite update_index_neq; try lia.
  specialize (H5 j). assert (j < m) by lia.
  apply H5 in H4. easy.
  intros.
  bdestruct (j =? m); subst. repeat rewrite update_index_eq.
  simpl in *. specialize (H0 m). assert (m < S m) by lia.
  apply H0 in H1.
  destruct H1. repeat rewrite H6; try lia.
  assert (a_nat2fb (@snd C rz_val (r m)) size = (a_nat2fb (@snd C rz_val (bl m)) size)).
  unfold a_nat2fb.
  clear H0 H1 H2 H5 H3 H4. induction size; simpl; try easy.
  rewrite IHsize; try lia. rewrite H6; try lia. easy.
  rewrite H7.
  bdestruct (i =? size); subst.
  repeat rewrite update_index_eq. easy.
  repeat rewrite update_index_neq; try lia.
  rewrite H6; try lia. easy.
  repeat rewrite update_index_neq; try lia.
  assert (j < m) by lia. apply H5 in H6.
  destruct H6. rewrite H7; try lia. easy.
Qed.

Lemma bexp_eval_same: forall b env n n2 l l1 m r bl v s, type_bexp env b (QT n, l) ->
   ses_len (l ++ l1) = Some n2 ->
   (forall j : nat,
      j < m ->
      fst (r j) = fst (bl j) /\
      (forall i : nat, i < n2 -> snd (r j) i = snd (bl j) i)) ->
   eval_bexp ((l ++ l1, Cval m r)::s) b ((l ++ l1, v)::s) ->
   (exists v', eval_bexp ((l ++ l1, Cval m bl)::s) b ((l ++ l1, v')::s) /\ match_value n2 v v').
Proof.
  induction b;intros;simpl in *; try easy.
  apply type_bexp_ses_len in H as X1.
  apply ses_len_app_sub with (n := n) in H0 as X2; try easy.
  inv H. inv H2; simpl in *.
  exists (Cval m (eval_eq_bool bl m m0 b)).
  split. constructor.
  apply ses_len_app_small with (l1 := l1) (n1 := n2) in X1 as X3; try easy.
  apply eval_eq_bool_same; try lia; easy.
  inv H2; simpl in *.
  exists (Cval m (eval_eq_bool bl m m0 b)).
  split. constructor.
  apply ses_len_app_small with (l1 := l1) (n1 := n2) in X1 as X3; try easy.
  apply eval_eq_bool_same; try lia; easy.
  apply type_bexp_ses_len in H as X1.
  apply ses_len_app_sub with (n := n) in H0 as X2; try easy.
  inv H. inv H2; simpl in *.
  exists (Cval m (eval_lt_bool bl m m0 b)).
  split. constructor.
  apply ses_len_app_small with (l1 := l1) (n1 := n2) in X1 as X3; try easy.
  apply eval_lt_bool_same; try lia; easy.
  inv H2; simpl in *.
  exists (Cval m (eval_rlt_bool bl m m0 b)).
  split. constructor.
  apply ses_len_app_small with (l1 := l1) (n1 := n2) in X1 as X3; try easy.
  apply eval_rlt_bool_same; try lia; easy.
  apply type_bexp_ses_len in H as X1.
  apply ses_len_app_sub with (n := n) in H0 as X2; try easy.
  inv H. inv H2; simpl in *.
  exists (Cval m bl).
  split. constructor. constructor; try easy.
Qed.

Lemma grab_bool_same_fst: forall m n n1 r bl, 0 < n <= n1 ->
      (forall j : nat,
      j < m ->
      fst (r j) = fst (bl j) /\
      (forall i : nat, i < n1 -> snd (r j) i = snd (bl j) i)) ->
      (fst (grab_bool r m n)) = (fst (grab_bool bl m n)).
Proof.
  unfold grab_bool in *; induction m; intros; simpl in *; try easy.
  destruct (H0 m) ; try lia. rewrite H2; try lia.
  assert ((@snd C (forall _ : nat, bool) (bl m) (Init.Nat.sub n (S O))
     = @snd C rz_val (bl m) (Init.Nat.sub n (S O)))) by easy.
  destruct (snd (bl m) (n - 1)) eqn:eq1. rewrite <- H3 in *.
  destruct (grab_bool_elem r m (n - 1)) eqn:eq2.
  destruct (grab_bool_elem bl m (n - 1)) eqn:eq3.
  assert (fst (grab_bool_elem r m (n - 1)) = fst (grab_bool_elem bl m (n - 1))).
  erewrite IHm. easy. apply H. intros. apply H0. lia. rewrite eq2 in H4. rewrite eq3 in H4.
  simpl in *. rewrite H4. easy.
  rewrite <- H3. erewrite IHm. easy. apply H. intros. apply H0. lia.
Qed.

Lemma grab_bool_same_fst_lt: forall m n r, 
      (fst (grab_bool r m n)) <= m.
Proof.
  unfold grab_bool. induction m;intros;simpl in *; try easy.
  destruct (snd (r m) (n - 1)).
  destruct (grab_bool_elem r m (n - 1)) eqn:eq1.
  specialize (IHm n r). rewrite eq1 in IHm. simpl in *. lia.
  specialize (IHm n r). lia.
Qed.

Lemma grab_bool_gt_case: forall m n r j, (fst (grab_bool_elem r m n)) <= j 
     -> (snd (grab_bool_elem r m n)) j = (C0,allfalse).
Proof.
  induction m; intros; simpl in *; try easy.
  destruct (snd (r m) n) eqn:eq1. destruct (grab_bool_elem r m n) eqn:eq2.
  simpl in *. rewrite update_index_neq by lia. replace p with (snd (grab_bool_elem r m n)).
  rewrite IHm; try easy. rewrite eq2. simpl. lia. rewrite eq2. easy.
  rewrite IHm. easy. lia.
Qed.

Lemma grab_bool_same: forall m n n1 r bl, 0 < n <= n1 ->
      (forall j : nat,
      j < m ->
      fst (r j) = fst (bl j) /\
      (forall i : nat, i < n1 -> snd (r j) i = snd (bl j) i))
   ->  match_value n1 (Cval (fst (grab_bool r m n)) (snd (grab_bool r m n)))
               (Cval (fst (grab_bool bl m n)) (snd (grab_bool bl m n))).
Proof.
  intros.
  rewrite grab_bool_same_fst with (n1 := n1) (bl := bl) in *; try easy.
  specialize (grab_bool_same_fst_lt m n bl) as X3.
  unfold grab_bool in *.
  induction m; intros; constructor; intros;simpl in *; try easy.
  assert ((forall j : nat,
       j < m ->
       fst (r j) = fst (bl j) /\
       (forall i : nat, i < n1 -> snd (r j) i = snd (bl j) i))).
  intros. apply H0. lia. specialize (IHm H2). simpl in *.
  destruct (H0 m); try lia. rewrite H4 in *; try lia.
  assert ((@snd C (forall _ : nat, bool) (bl m) (Init.Nat.sub n (S O))
     = @snd C rz_val (bl m) (Init.Nat.sub n (S O)))) by easy.
  destruct (snd (bl m) (n - 1)) eqn:eq1.
  rewrite <- H5 in *.
  destruct (grab_bool_elem r m (n - 1)) eqn:eq2.
  destruct (grab_bool_elem bl m (n - 1)) eqn:eq3.
  simpl in *.
  assert (n0 = n2).
  replace n0 with (fst (grab_bool r m n)).
  rewrite grab_bool_same_fst with (n1 := n1) (bl := bl); try easy.
  unfold grab_bool in *. rewrite eq3. simpl. easy.
  unfold grab_bool. rewrite eq2. easy.
  subst.
  assert (n2 <= m) by lia. apply IHm in H6. inv H6.
  bdestruct (j =? n2); subst. repeat rewrite update_index_eq.
  apply H0. lia.
  repeat rewrite update_index_neq; try lia.
  apply H9. lia.
  rewrite <- H5 in *.
  destruct (grab_bool_elem r m (n - 1)) eqn:eq2.
  destruct (grab_bool_elem bl m (n - 1)) eqn:eq3.
  simpl in *.
  bdestruct (n2 =? S m); subst.
  specialize (grab_bool_same_fst_lt m n bl) as X1. unfold grab_bool in *.
  rewrite eq3 in *. simpl in *. lia.
  assert (n2 <= m) by lia.
  apply IHm in H7. inv H7. apply H10. lia.
Qed.

Lemma mut_state_same: forall m pos n n1 r bl fc, 0 < n ->
      (forall j : nat,
      j < m ->
      fst (r j) = fst (bl j) /\
      (forall i : nat, i < pos + n + n1 -> snd (r j) i = snd (bl j) i))
   ->  mut_state pos n n1 (Cval (fst (grab_bool r m n)) (snd (grab_bool r m n))) fc
    -> (exists fca, mut_state pos n n1 (Cval (fst (grab_bool bl m n)) (snd (grab_bool bl m n))) fca
           /\ match_value (n+n1) fc fca).
Proof.
  intros. inv H1.
  exists ((Cval (fst (grab_bool bl m n))
       (mut_fch_state pos n n1 (snd (grab_bool bl m n))))).
  split.
  apply fch_mut_state.
  assert (0 < n <= pos + n + n1) by lia.
  specialize (grab_bool_same m n (pos+n+n1) r bl H1 H0) as X1.
  inv X1. constructor. intros. apply H4 in H2 as [X2 X3].
  unfold mut_fch_state in *. simpl in *. split. apply X2.
  intros. unfold mut_nor_aux in *.
  bdestruct (i <? pos). apply X3. lia.
  bdestruct (pos <=? i); simpl in *; try lia.
  bdestruct (i <? pos + n1); simpl in *.
  apply X3. lia.
  bdestruct (pos + n1 <=? i); simpl in *; try lia.
  bdestruct (i <? pos + n1 + n); simpl in *; try lia.
  apply X3. lia.
Qed.

Lemma assem_bool_same: forall m m1 n n1 f f' r r' fc,
      (forall j : nat,
      j < m ->
      fst (f j) = fst (f' j) /\
      (forall i : nat, i < n + n1 -> snd (f j) i = snd (f' j) i)) ->
      (forall j : nat,
      j < m1 ->
      fst (r j) = fst (r' j) /\
      (forall i : nat, i < n1 -> snd (r j) i = snd (r' j) i)) ->
      assem_bool n n1 m f (Cval m1 r) fc ->
      (exists fca, assem_bool n n1 m f' (Cval m1 r') fca
           /\ match_value (n+n1) fc fca).
Proof.
  induction m; intros; simpl in *; try easy. inv H1.
  exists (Cval 0 (fun _ : nat => (C0, allfalse))).
  split; try constructor. intros. split; try easy.
  inv H1. apply IHm with (f' := f') (r' := r') in H6 as X1; try easy.
  destruct X1 as [fca [X1 X2]]. inv X2.
  replace (cut_n (@snd C rz_val (f m)) n) with (cut_n (@snd C rz_val (f' m)) n) in H8.
  apply find_basis_elems_same with (r' := r') in H8; try easy.
  destruct H8 as [fv' [X2 X3]].
  exists (Cval (S m') (update r2 m' (f' m))).
  split. apply assem_bool_many_1 with (fv := fv'); try easy.
  constructor. intros.
  bdestruct (j =? m'); subst.
  repeat rewrite update_index_eq.
  assert (m < S m) by lia. destruct (H m H2).
  split. rewrite H3. easy. intros. rewrite H4. easy. easy.
  repeat rewrite update_index_neq; try lia.
  apply H5; try lia.
  assert (m < S m) by lia. destruct (H m H1).
  unfold cut_n in *. apply functional_extensionality.
  intros. bdestruct (x <? n). rewrite H3; try easy. lia.
  easy.
  intros. apply H. lia.
  replace (cut_n (@snd C rz_val (f m)) n) with (cut_n (@snd C rz_val (f' m)) n) in *.
  apply IHm with (f' := f') (r' := r') in H5 as X1; try easy.
  destruct X1 as [fca [X1 X2]]. inv X2.
  apply find_basis_elems_same with (r' := r') in H8; try easy.
  destruct H8 as [fv' [X2 X3]].
  inv X3.
  apply (assem_list_same mv m' n n1 
   (cut_n (snd (f' m)) n) fv fv' acc r2 ma fa) in H3 as Y1; try easy.
  destruct Y1 as [fva [Y1 Y2]].
  exists (Cval ma fva).
  split. apply assem_bool_many_2 with (m' := m') (acc := r2) (mv := mv) (fv := fv'); try easy.
  easy.
  intros. apply H. lia.
  unfold cut_n. apply functional_extensionality. intros.
  bdestruct (x <? n). 
  assert (m < S m) by lia. apply H in H2.
  destruct H2. rewrite H3. easy. lia.
  easy.
Qed.

Lemma match_value_shrink: forall n n1 a b, n <= n1 -> match_value n1 a b -> match_value n a b.
Proof.
  intros. induction H0. constructor. intros. apply H0. lia.
  constructor. intros. apply H0. lia. constructor.
  intros. apply H0 in H1. destruct H1. split; try easy.
  intros. apply H2. lia.
Qed.

Lemma simp_aexp_no_subst: forall a v x va, simp_aexp a = Some v -> subst_aexp a x va = a.
Proof.
  induction a; intros; simpl in *; try easy.
  destruct (simp_aexp a1) eqn:eq1; try easy.
  destruct (simp_aexp a2) eqn:eq2; try easy.
  rewrite IHa1 with (v := n); try easy.
  rewrite IHa2 with (v := n0); try easy.
  destruct (simp_aexp a1) eqn:eq1; try easy.
  destruct (simp_aexp a2) eqn:eq2; try easy.
  rewrite IHa1 with (v := n); try easy.
  rewrite IHa2 with (v := n0); try easy.
Qed.

Lemma simple_ses_app_combine: forall l l1, simple_ses l -> simple_ses l1 -> simple_ses (l++l1).
Proof.
  intros. induction H. simpl. easy. constructor; try easy.
Qed.

Definition add_tenv (T:type_map) (l:locus) := 
    match T with ((la,CH)::ta) => Some ((la++l,CH)::ta) | _ => None end.

Lemma subst_type_map_empty: forall T x v, subst_type_map T x v = nil -> T = nil.
Proof.
  induction T; intros; simpl in *; try easy. destruct a. inv H.
Qed.

Lemma subst_locus_simple: forall s l1 i v, simple_ses l1
          -> subst_locus (s ++ l1) i v = subst_locus s i v ++ l1.
Proof.
  induction s; intros; simpl in *. rewrite simple_ses_subst; try easy.
  rewrite IHs. easy. easy.
Qed.

Definition single_tenv (T:type_map) := match T with ((l,CH)::ta) => True | _ => False end.

Lemma state_equiv_single: forall rmax sa l m b,
   @state_equiv rmax sa ([(l,Cval m b)]) -> sa = ([(l,Cval m b)]).
Proof.
  intros. remember ([(l, Cval m b)]) as sb. induction H; subst; try easy.
  destruct a2. simpl in *. subst. rewrite app_nil_r. easy.
  simpl in *. inv Heqsb. apply app_eq_nil in H1. destruct H1; subst. simpl in *. easy.
  inv Heqsb. inv H. easy.
  apply app_eq_nil in H2. destruct H2; subst. simpl in *. easy.
  inv Heqsb. inv H0.
Qed.

Lemma type_system_not_var: forall e rmax q env T T1 x a,
   @locus_system rmax q env T (Let x a e) T1 -> ~ AEnv.In x env.
Proof.
 intros. remember (Let x a e) as ea. generalize dependent a.
 generalize dependent e. induction H; intros; subst; simpl in *; try easy.
 eapply IHlocus_system. easy. inv Heqea. easy.
 inv Heqea. easy. inv Heqea. easy.
Qed.

Lemma qpred_check_split: forall T P P', qpred_check T (P++P')
   -> exists T1 T2, T = T1 ++ T2 /\ qpred_check T1 P /\ qpred_check T2 P'.
Proof.
  intros. remember (P++P') as A. generalize dependent P. generalize dependent P'.
  induction H; intros; simpl in *; try easy.
  symmetry in HeqA.
  apply app_eq_nil in HeqA. destruct HeqA; subst.
  exists nil,nil. simpl in *. split; try easy; try constructor.
  constructor. constructor.
  destruct P. simpl in *; subst.
  specialize (IHqpred_check Sa nil). simpl in *.
  assert (Sa = Sa) by easy. apply IHqpred_check in H2.
  destruct H2 as [T1 [T2 [X1 [X2 X3]]]]; subst.
  inv X2. simpl in *. exists nil, ((sa,t)::T2).
  split; try easy. split; constructor; try easy.
  inv HeqA. assert (P++P' = P++P') by easy.
  apply IHqpred_check in H2.
  destruct H2 as [T1 [T2 [X1 [X2 X3]]]]; subst.
  exists ((sa,t)::T1),T2. split; try easy.
  split; try constructor; try easy.
Qed.

Lemma qpred_check_shrink_r: forall T T' P P', qpred_check (T++T') (P++P') -> length T = length P
           -> qpred_check T' P'.
Proof.
  intros. remember (T++T') as Ta. remember (P ++ P') as Pa.
 generalize dependent P. generalize dependent P'.
 generalize dependent T. generalize dependent T'.
 induction H; intros; simpl in *; try easy.
 symmetry in HeqTa. symmetry in HeqPa.
 apply app_eq_nil in HeqTa.
 apply app_eq_nil in HeqPa.
 destruct HeqTa; subst.
 destruct HeqPa;subst.
 constructor.
 destruct T0. simpl in *.
 symmetry in H2.
 apply length_zero_iff_nil in H2; subst.
 simpl in *. subst. constructor; try easy.
 inv HeqTa. inv HeqPa. simpl in *. destruct P. simpl in *. lia.
 simpl in *. inv H2. inv H4. apply IHqpred_check with (T := T0) (P0 := P); try easy.
Qed.

Lemma qpred_check_combine: forall T T' P P', qpred_check T P -> qpred_check T' P' ->
                 qpred_check (T++T') (P++P').
Proof.
  intros. generalize dependent T'. generalize dependent P'.
  induction H; intros; simpl in *; try easy.
  constructor; try easy.
  apply IHqpred_check. easy.
Qed.

Lemma sval_check_same: forall s sa v, sval_check s v -> sval_check sa v -> s = sa.
Proof.
  intros. generalize dependent sa. induction H; intros; simpl in *; try easy.
  inv H0. easy. inv H0. apply IHsval_check in H3. easy.
  inv H0. apply IHsval_check in H3. easy.
  inv H0. apply IHsval_check in H3. easy.
Qed.

Lemma qpred_check_same: forall T T1 P, qpred_check T P -> qpred_check T1 P -> T = T1.
Proof.
  intros. generalize dependent T1. induction H; intros; simpl in *; try easy.
  inv H0. easy. inv H2.
  apply IHqpred_check in H8; subst.
  apply sval_check_same with (s := sa0) in H; try easy; subst.
  inv H9; inv H1; try easy.
Qed.

Lemma simp_aexp_no_free: forall a v, simp_aexp a = Some v -> freeVarsAExp a = nil.
Proof.
  induction a; intros; simpl in *; try easy.
  destruct (simp_aexp a1) eqn:eq1; try easy.
  destruct (simp_aexp a2) eqn:eq2; try easy.
  rewrite IHa1 with (v := n); try easy.
  rewrite IHa2 with (v := n0); try easy.
  destruct (simp_aexp a1) eqn:eq1; try easy.
  destruct (simp_aexp a2) eqn:eq2; try easy.
  rewrite IHa1 with (v := n); try easy.
  rewrite IHa2 with (v := n0); try easy.
Qed.

Lemma eval_aexp_check: forall env s a v,
  kind_env_stack env s -> eval_aexp s a v -> sublist (freeVarsAExp a) env.
Proof.
  intros. induction H0; intros; simpl in *; try easy.
  unfold sublist. constructor.
  assert (AEnv.In x s). exists (r,n). easy. apply H in H1. exists (Mo MT). easy.
  constructor. constructor.
  apply simp_aexp_no_free in H1. rewrite H1.
  rewrite app_nil_r. apply IHeval_aexp. easy.
  apply simp_aexp_no_free in H1. rewrite H1.
  rewrite app_nil_l. apply IHeval_aexp. easy.
  apply simp_aexp_no_free in H1. rewrite H1.
  rewrite app_nil_r. apply IHeval_aexp. easy.
  apply simp_aexp_no_free in H1. rewrite H1.
  rewrite app_nil_l. apply IHeval_aexp. easy.
Qed.

Lemma sublist_combine: forall l1 l2 env, sublist l1 env -> sublist l2 env -> sublist (l1 ++ l2) env.
Proof.
  induction l1; intros; try easy.
  inv H. rewrite <- app_comm_cons.
  constructor; try easy. apply IHl1; try easy.
Qed.

Lemma cmodel_check: forall env s W, kind_env_stack env s -> cmodel s W -> cpred_check W env.
Proof.
  intros. induction H0.
  constructor.
  constructor; try easy.
  clear H1 IHForall.
  inv H0; simpl in *.
  apply eval_aexp_check with (env := env) in H2; try easy.
  apply eval_aexp_check with (env := env) in H3; try easy.
  apply sublist_combine; try easy.
  apply eval_aexp_check with (env := env) in H2; try easy.
  apply eval_aexp_check with (env := env) in H3; try easy.
  apply sublist_combine; try easy.
Qed.

Lemma locus_system_skip : forall rmax q env T T',
    @locus_system rmax q env T PSKIP T' -> T = T'.
Proof.
  intros. remember PSKIP as e. induction H; try easy.
  apply IHlocus_system in Heqe; subst.
  easy.
Qed.

Lemma proof_soundness: forall e rmax t env s tenv tenv' P Q, 
     @env_state_eq tenv (snd s) -> kind_env_stack env (fst s) ->
      type_check_proof rmax t env tenv tenv' P Q e -> freeVarsNotCPExp env e 
      -> simple_tenv tenv ->
    @triple rmax t env tenv P e Q -> model s P -> 
          (exists sa, model (fst s,sa) Q  
          /\ @qfor_sem rmax env s e (fst s,sa) /\ env_state_eq tenv' sa).
Proof.
  intros. generalize dependent s. generalize dependent tenv'.
  induction H4; intros;simpl in *.
- assert (simple_tenv T).
  unfold simple_tenv in *. intros. apply H3 with (b := b). apply in_app_iff.
  left. easy.
  assert (XX1 := H).
  destruct H as [X1 [X2 X3]].
  inv H1. destruct H8. inv H8.
  apply qpred_check_split in H10 as Y1.
  destruct Y1 as [Ta [Tb [Y1 [Y2 Y3]]]]; subst.
  simpl in *. destruct s; simpl in *.
  apply env_state_eq_app in H0 as [q1 [q2 [X5 [X6 X7]]]].
  apply env_state_eq_same_length in X5 as [X8 X9]; try easy. subst.
  inv X3; simpl in *.
  apply qpred_check_same with (T := T1) in Y2; try easy; subst.
  specialize (IHtriple H2 H7 Ta XX1 (s, q1) X8 H5).
  unfold model in *; simpl in *. destruct H6 as [Y1 Y2].
  destruct X1 as [G1 G2]; simpl in *.
  apply qpred_check_length_same in G2. rewrite G2 in X7.
  apply qmodel_shrink in Y2 as Y5; try easy. assert (cmodel s W /\ qmodel q1 P) by easy.
  destruct (IHtriple H6) as [sa [Y6 [Y7 Y8]]]. destruct Y6.
  inv H. apply qpred_check_shrink_r in H14 as G3.
  apply qpred_check_same with (T := Tb) in G3; try easy ; subst.
  exists (sa++q2). split. split. easy.
  apply qmodel_shrink_1 in Y2 as Y9; try easy.
  apply qmodel_combine; try easy. split.
  apply qfor_sem_local with (s1 := q2) in Y7; try easy.
  apply env_state_eq_app_join; try easy. easy.
 -
  apply IHtriple; try easy.
  destruct H1 as [X1 [X2 X3]].
  destruct H as [Y1 [Y2 Y3]].
  split; try easy. 
  destruct H1 as [X1 [X2 X3]].
  destruct H as [Y1 [Y2 Y3]].
  inv H7. destruct s; simpl in *.
  destruct P. destruct P'. simpl in *.
  inv X1. inv Y1. simpl in *.
  inv H0. split; try easy. apply H12; easy.
  split; try easy. simpl in *.  
  apply qpred_state_consist with (rmax := rmax) (T := T) (P := q1); try easy.
 -
  destruct (IHtriple H2 H3 T1 H s H6 H7 H8) as [sa [X1 [X2 X3]]].
  destruct s; simpl in *.
  inv H1. destruct H5 as [Y1 [Y2 Y3]]. inv Y3.
  apply qpred_check_same with (T := tenv') in H10; try easy; subst.
  exists sa.
  split.
  inv H0; simpl in *. inv X1. split; simpl in *; try easy.
  apply H10; try easy.
  inv X1. split; simpl in * ; try easy.
  apply qpred_state_consist with (rmax := rmax) (T := T1) (P := P0); try easy.
  destruct H as [G1 [G2 G3]]. inv G3. easy.
  split; try easy.
 -
  destruct s. exists q0. split. easy.
  split. constructor.
  destruct H1 as [X1 [X2 X3]].
  apply locus_system_skip in X2; subst. easy.
 - 
  apply freeVars_pexp_in with (v := v) in H2 as X1; try easy.
  destruct H5 as [Y1 [Y2 Y3]].
  destruct (IHtriple X1 H3 T1 H1 s H6 H7 H8) as [sa [X2 [X3 X4]]].
  destruct H1 as [G1 [G2 G3]].
  inv G3. inv Y3.
  apply qpred_check_same with (T := tenv') in H5; try easy; subst.
  exists sa. split. easy.
  split. apply let_sem_c with (n := v); try easy.
  easy.
 -
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H10. inv H10. easy.
  apply AEnv.add_3 in H10; try lia.
  apply H2 with (x0 := x0). simpl.
  apply in_app_iff. right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  destruct s; simpl in *.
  apply kind_env_stack_exist with (s := s) in H0 as X1; try easy. destruct X1 as [va X1].
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x va s)).
  unfold kind_env_stack. intros. split. intros.
  bdestruct (x0 =? x); subst.
  exists va. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H10; try easy.
  unfold AEnv.In,AEnv.Raw.PX.In in *.
  apply H7 in H10. destruct H10. exists x1. apply AEnv.add_2. lia. easy. lia.
  intros. destruct H10.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H10. subst.
  apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia.
  apply H7. apply AEnv.add_3 in H10; try lia. exists x1. easy.
  specialize (IHtriple H9 H3 T1 H ((AEnv.add x va s),q0) H6 H10).
  destruct H8 as [X2 X3]. simpl in *.
  assert (cmodel (AEnv.add x va s) (CEq (BA x) a :: W)).
  constructor. 
  apply eval_aexp_not_exists with (x := x) (v := va) in X1; try easy.
  destruct va.
  apply ceq_asem with (s := (AEnv.add x (r, n) s)) (x := BA x)
              (y := a) (r1 := r) (r2 := r) (n1 := n) (n2 := n) ; try easy.
  apply var_sem. apply AEnv.add_1. easy. intros R.
  apply H7 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  unfold cmodel in X2.
  assert (~ AEnv.In x s). intros R. apply H7 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  clear H H0 H2 H1 X1 H4 H5 IHtriple H6 H7 X3 H9 H10.
  induction X2. constructor. constructor.
  apply eval_cabexp_not_exists. easy. easy. easy.
  assert (model (AEnv.add x va s, q0) (CEq (BA x) a :: W, P)).
  split. simpl in *. apply H8. easy.
  destruct (IHtriple H11) as [sa [Y1 [Y2 Y3]]].
  exists sa. split. split. easy. destruct Y1. simpl in *. 
  easy. split. apply let_sem_m with (n := va) (W0 := AEnv.add x va s); try easy.
  destruct H as [A1 [A2 A3]].
  destruct H5 as [G1 [G2 G3]]. destruct A3. destruct G3. simpl in *.
  apply qpred_check_same with (T := tenv') in H5; try easy; subst.
  easy.
  unfold freeVarsNotCPExp,freeVarsNotCAExp in *. intros. simpl in *. apply H2 with (x0 := x0); try easy.
  apply in_app_iff. left. easy.
 -
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H11. inv H11. easy.
  apply AEnv.add_3 in H11; try lia.
  apply H2 with (x0 := x0). simpl.
  right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  assert (simple_tenv ((l, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H11. inv H11.
  specialize (H3 ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
     In ((y, BNum 0, BNum n) :: a, CH) T). left. easy.
  apply H3 in H11.
  inv H11. easy. apply H3 with (b:= b). right. easy.
  specialize (IHtriple H10 H11 T1 H).
  destruct s. simpl in *.
  inv H6. destruct H13. simpl in *.
  inv H4.
  destruct H as [X2 [X3 X4]].
  inv X2. simpl in *. inv H4.
  inv H9. inv H14. simpl in *; subst.
  assert (simple_ses l).
  unfold simple_tenv in H4.
  assert (In ((y, BNum 0, BNum n) :: l,CH) (((y, BNum 0, BNum n) :: l, CH) :: T)).
  simpl. left. easy. apply H3 in H9. inv H9. easy.
  apply ses_len_simple in H9. destruct H9 as [na X1].
  assert (n0 = n+na).
  unfold ses_len in *. simpl in *.
  destruct (get_core_ses l) eqn:eq1. inv H19. inv X1. lia. easy. subst.
  inv H7. inv H27. inv H20.
  apply pick_mea_exist_same with (n0 := n+na)
            (ba := bl) in H21 as Y3; try easy; try lia.
  assert (Y1 := H22).
  inv H22. destruct (build_state_pars m n v' (to_sum_c m n v' r2) r2) eqn:eq1. inv H9.
  apply build_state_ch_exist_same with (n0 := n+na) (ba := bl) in Y1; try easy; try lia.
  destruct Y1 as [bl' [Y1 Y2]].
  assert (env_state_eq ((l, CH) :: T)
             (snd (AEnv.add x (r', v') s, (l, (Cval n0 bl')) :: s0))).
  constructor; try easy. constructor.
  assert (kind_env_stack (AEnv.add x (Mo MT) env)
             (fst (AEnv.add x (r', v') s, (l, (Cval n0 bl')) :: s0))).
  unfold kind_env_stack in *. intros. split; intros.
  bdestruct (x0 =? x); subst.
  exists (r', v'). apply AEnv.add_1. easy.
  apply AEnv.add_3 in H9; try lia.
  apply H8 in H9. destruct H9.
  exists x1. apply AEnv.add_2; try lia. easy.
  bdestruct (x0 =? x); subst. apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia. apply H8. destruct H9. apply AEnv.add_3 in H9; try lia.
  exists x1. easy.
  apply mask_state_exists in Y3 as Y4. destruct Y4 as [n01 [p1 [Y4 Y5]]].
  rewrite Y1 in Y4. inv Y4.
  assert (model (AEnv.add x (r', v') s, (l, Cval n01 p1) :: s0)
             (CEq (BA x) (MNum r' v') :: W, (SV l, Cval n01 p) :: P)).
  split. simpl.
  constructor. apply ceq_asem with (r1 := r') (r2 := r') (n1 := v') (n2 := v'); try easy.
  constructor. apply AEnv.add_1. easy. constructor.
  unfold cmodel in H4.
  assert (~ AEnv.In x s). intros R. apply H8 in R.
  assert (AEnv.In x env). exists (Mo MT). easy. easy.
  clear H H2 H3 X3 X4 H0 H1 IHtriple H5 H6 H8
    H10 H11 H12 H13 H21 Y3 Y5 H18 H23 H24 H19 H25 X1 H15 H17 H7 H9 Y1 Y2.
  induction H4. constructor. constructor.
  apply eval_cabexp_not_exists; easy. easy.
  apply model_many with (n := na); try easy.
  constructor. intros. inv Y2. apply H22 in H14.
  split. easy. intros. destruct H14. rewrite H20. easy. lia.
  destruct (IHtriple (AEnv.add x (r', v') s, (l, Cval n01 p1) :: s0)
          H7 H9 H14) as [sa [G1 [G2 G3]]].
  exists sa.
  split. split. easy. simpl in *. inv G1. simpl in *. easy.
  split. 
  apply let_sem_q with (r := r') (v := v')
        (va' := (Cval n01 p1)) (W' := (AEnv.add x (r', v') s)); try easy.
  inv H13. inv X4. simpl in *.
  apply qpred_check_same with (T := tenv') in H22; try easy; subst.
  easy.
  intros. apply H17 in H7. destruct H7. split; try easy.
  intros; rewrite H9. easy. easy.
  intros. apply H17 in H7. destruct H7. split; try easy.
  intros; rewrite H9. easy. easy.
 -
  destruct s. inv H5. inv H7. inv H13.  simpl in *. inv H12. 
  apply eval_nor_switch_same with (b1 := r1) (l1 := nil) (n := n) in H; try easy.
  destruct H as [va [X1 X2]]. destruct va.
  exists ([(l,Nval c r0)]).
  split. split. easy. simpl.
  apply model_many with (n:= n); try easy.
  inv X2.
  constructor. intros. rewrite H7. easy. easy. constructor.
  split.
  apply appu_sem_nor; try easy.
  destruct H1 as [Y1 [Y2 Y3]].
  inv Y3. inv H1. inv H13. inv H12. inv H14. constructor. 1-2:constructor.
  rewrite app_nil_r. easy. intros. rewrite H9. easy. easy.
 -
  destruct s. inv H5.
  inv H7. inv H13. inv H12. simpl in *; subst.
  apply eval_ch_switch_same with (l1 := l1) (n := n) (b1 := r1) in H as X1; try easy.
  destruct X1 as [va [X1 X2]].
  exists ([(l++l1,Cval m va)]).
  split. split. easy.   apply model_many with (n:= n); try easy.
  inv X2. constructor. intros. apply H8 in H5. destruct H5. split; try easy.
  intros. rewrite H7; easy.
  constructor.
  split.
  apply appu_sem_ch; try easy.
  destruct H1 as [Y1 [Y2 Y3]].
  inv Y3. inv H5. inv H14. inv H13. inv H15.
  constructor. 1-2:constructor.
  intros. apply H9 in H5.
  destruct H5; try easy. split; try easy.
  intros. rewrite H7; easy.
 -
  destruct s. inv H6. simpl in *.
  inv H8. inv H14. inv H13.
  exists ([(([a]),Hval (eval_to_had n b))]).
  split. split. easy. simpl.
  apply model_many with (n := n); try easy. constructor. intros. easy. constructor.
  split. rewrite H0 in H12. inv H12.
  rewrite <- eval_to_nor_switch_same with (r1 := r1); try easy.
  constructor; try easy.
  destruct H1 as [Y1 [Y2 Y3]]. inv Y3.
  inv H6. inv H15. inv H14. inv H16.
  constructor. 1-2:constructor. 
 -
  destruct s. inv H6. simpl in *.
  inv H8. inv H14. inv H13.
  exists ([(([a]),(Nval C1 (eval_to_nor n b)))]).
  split. split. easy. simpl.
  apply model_many with (n := n); try easy. constructor. intros. easy. constructor.
  split. rewrite H0 in H12. inv H12.
  rewrite <- eval_to_had_switch_same with (r1 := r1); try easy.
  constructor; try easy.
  destruct H1 as [Y1 [Y2 Y3]]. inv Y3.
  inv H6. inv H15. inv H14. inv H16.
  constructor. 1-2:constructor. 
 -
  assert (freeVarsNotCPExp env e) as X1.
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x) (t := t); try easy. simpl. apply in_app_iff. right. easy.
  destruct (IHtriple X1 H3 T1 H s H5 H6 H7) as [sa [X2 [X3 X4]]].
  exists sa. split. easy.
  split. apply if_sem_ct; try easy.
  destruct H1 as [Y1 [Y2 Y3]]. inv Y3.
  destruct H as [G1 [G2 G3]]. inv G3.
  apply qpred_check_same with (T := tenv') in H9; try easy; subst.
  easy.
 -
  destruct s. simpl in *. exists q0.
  split. easy. split. apply if_sem_cf; try easy.
  destruct H1 as [G1 [G2 G3]]. inv G1. inv G3.
  apply qpred_check_same with (T := tenv') in H6; try easy; subst.
  easy.
 -
  assert (freeVarsNotCPExp env e) as X1.
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x) (t := t); try easy. simpl. apply in_app_iff. right. easy.
  assert (simple_tenv ([(l1, CH)])).
  unfold simple_tenv in *.
  intros. simpl in *. destruct H15; try easy. 
  inv H15. assert ((l ++ a, CH) = (l++a, CH) \/ False). left. easy.
  apply H3 in H15. apply simple_ses_app_r in H15. easy.
  specialize (IHtriple X1 H15 ([(l1, CH)]) H0).
  inv H14. destruct s. simpl in *.
  destruct H0 as [X2 [X3 X4]]. inv X2. inv H14. simpl in *. subst. inv H24. inv H23.
  inv H12. inv H23. inv H22.
  inv H17. inv H23. inv H22.
  inv H4. inv H25. inv H24; try easy.
  inv H5.
  rewrite H1 in H25. inv H25.
  assert (n0 = n1 + n2) as U1. apply ses_len_app_add with (l := l) (n := n1) in H26; try easy.
  rewrite H19 in H26. inv H26. easy. subst.
  apply bexp_eval_same with (env := env) (n := n1) 
         (n2 := n1 + n2) (bl := bl0) in H18 as Y1; try easy.
  destruct Y1 as [va [Y1 Y2]]. inv Y2.
  apply type_bexp_gt in H as A1.
  apply mut_state_same with (bl := r0) in H27 as Y3; try easy.
  destruct Y3 as [fca [Y3 Y4]].
  inv Y4.
  assert (env_state_eq ([(l1, CH)]) (snd (s, [(l1, Cval m r3)]))).
  simpl in *. constructor. constructor. constructor.
  assert (kind_env_stack env (fst (s, [(l1, Cval m r3)]))).
  simpl in *. easy.
  assert (m = (fst (grab_bool f' m0 n1))).
  inv H27. easy. subst.
  assert (model (s, [(l1, Cval (fst (grab_bool f' m0 n1)) r3)])
             (W, [(SV l1, Cval (fst (grab_bool f' m0 n1)) bl)])).
  split. easy. simpl in *. apply model_many with (n := n2); try easy.
  constructor. intros. apply H22 in H12. split; try easy.
  intros. destruct H12. rewrite H23. easy. lia. constructor.
  destruct (IHtriple (s,([(l1,Cval (fst (grab_bool f' m0 n1)) r3)])) 
          H4 H5 H12) as [sa [A2 [A3 A4]]]; simpl in *.
  inv X4. simpl in *. inv H23. inv H32. inv H31.
  inv H7. inv H28. inv H6. inv H25. inv H29. inv H33. inv H32; try easy.
  inv H8. inv H30. inv H29; try easy. inv H9.
  apply app_length_same with (n := n1) in H23 as A5; try easy.
  destruct A5; subst.
  inv A2; simpl in *. inv H8. inv H38. inv H37.
  apply eval_bexp_det with (q1 := ([(l ++ l0, Cval m0 f'0)])) in H18 as A5; try easy.
  inv A5. rewrite H26 in *. rewrite H33 in *. inv H34; subst. inv H32; subst.
  clear H1 H6 H23 H29 H30 H31.
  apply assem_bool_same with (f' := r0) (r' := r1) in H36 as A5; try easy.
  destruct A5 as [fca [A5 A6]].
  exists ([(l++l0, fca)]).
  split. constructor; try easy. apply model_many with (n := n1+n); try easy.
  apply assem_bool_cval in H36 as A7. destruct A7 as [ma [fa A7]]; subst.
  apply assem_bool_cval in A5 as A7. destruct A7 as [mb [fb A7]]; subst.
  inv A6. constructor. intros. apply H8 in H1. destruct H1.
  rewrite H1; split; try easy. intros. rewrite H6. easy. easy.
  constructor.
  apply assem_bool_cval in H36 as A7. destruct A7 as [ma [fa A7]]; subst.
  apply assem_bool_cval in A5 as A7. destruct A7 as [mb [fb A7]]; subst.
  split. apply if_sem_q with (n0 := n1) (n' := n) (f'0 := r0)
                (fc := (Cval (fst (grab_bool f' m0 n1)) r3)) (fc' := Cval m r1); try easy.
  destruct H11 as [G1 [G2 G3]].
  inv G3. inv H6. inv H28. inv H29. inv H24.
  constructor. 1-2:constructor.
  intros. apply H25 in H1. destruct H1. rewrite H1. split; try easy.
  intros. rewrite H6; easy.
  intros. apply H20 in H4. destruct H4. rewrite H4; split; try easy.
  intros. rewrite H5; try easy.
 -
  destruct s. exists q0. split. easy.
  split. apply for_sem. assert (h - l = 0) by lia. rewrite H6. apply ForallA_nil.
  destruct H1 as [G1 [G2 G3]]. simpl in *.
  inv G1. inv G3.
  apply qpred_check_same with (T := tenv') in H6; try easy; subst. 
  easy.
 -
  assert (forall i, freeVarsNotCPExp env (If (subst_bexp b x i) (subst_pexp p x i))).
  intros.
  unfold freeVarsNotCPExp in *.
  intros;simpl in *.
  apply H2 with (x0 := x0); try easy.
  bdestruct (x0 =? x); subst. assert (AEnv.In x env). exists (Mo t). easy. easy.
  apply in_app_iff in H10. destruct H10.
  apply freeVarsBExp_subst in H10.
  apply in_app_iff. left. apply list_sub_not_in; try easy.
  apply in_app_iff. right. apply freeVarsPExp_subst in H10.
  apply list_sub_not_in; try easy.
  specialize (simple_tenv_subst_right T x l H3) as X1.
  remember (h - l) as na. assert (h = l + na) by lia. rewrite H11 in *.
  assert (tenv' = (subst_type_map T x (l+na))).
  assert (0 <= na-1) by lia.
  destruct H6 as [G1 [G2 G3]].
  destruct (H1 (l+na-1)) as [Y1 [Y2 Y3]]. lia.
  replace ((l + na - 1 + 1)) with (l+na) in * by lia.
  inv G3. inv Y3.
  apply qpred_check_same with (T := tenv') in H14; try easy; subst.
  rewrite H12 in *. 
  clear H11 H12 Heqna H H2 H3 H6.
  assert (exists sa : qstate,
  model (fst s, sa) (pred_subst_c P x (l + na)) /\
  ForallA rmax (@qfor_sem) na env s l x b p (fst s, sa)
    /\ env_state_eq (subst_type_map T x (l+na)) sa).
  induction na;intros; simpl in *; try easy.
  exists (snd s). replace (l+0) with l in * by lia.
  split; try easy.
  split. destruct s; simpl in *. apply ForallA_nil. easy.
  destruct na; subst; simpl in *; try easy. 
  assert (l <= l < l + 1) by lia.
  specialize (H10 l). specialize (X1 l). specialize (H1 l).
  specialize (H1 H).
  destruct (H5 l H H10 X1 (subst_type_map T x (l + 1)) H1 s H7 H8 H9) as [sa [Y1 [Y2 Y3]]].
  exists sa. split; try easy. split; try easy.
  apply ForallA_cons with (s' := s). constructor.
  replace (l+0) with l by lia. easy.
  assert (l < l + S na) by lia.
  assert ((forall i : nat,
        l <= i < l + S na ->
        @triple rmax q env (subst_type_map T x i) (pred_subst_c P x i)
          (If (subst_bexp b x i) (subst_pexp p x i)) (pred_subst_c P x (i + 1)))).
  intros. apply H4. lia.
  assert ((forall i : nat,
        l <= i < l + S na ->
        freeVarsNotCPExp env (If (subst_bexp b x i) (subst_pexp p x i)) ->
        simple_tenv (subst_type_map T x i) ->
        forall tenv' : type_map,
        type_check_proof rmax q env (subst_type_map T x i) tenv'
          (pred_subst_c P x i) (pred_subst_c P x (i + 1))
          (If (subst_bexp b x i) (subst_pexp p x i)) ->
        forall s : stack * qstate,
        env_state_eq (subst_type_map T x i) (snd s) ->
        kind_env_stack env (fst s) ->
        model s (pred_subst_c P x i) ->
        exists sa : qstate,
          model (fst s, sa) (pred_subst_c P x (i + 1)) /\
          @qfor_sem rmax env s (If (subst_bexp b x i) (subst_pexp p x i)) (fst s, sa) /\
          env_state_eq tenv' sa)).
  intros. apply H5; try easy; try lia.
  assert ((forall i : nat,
        l <= i < l + S na ->
        type_check_proof rmax q env (subst_type_map T x i)
          (subst_type_map T x (i + 1)) (pred_subst_c P x i)
          (pred_subst_c P x (i + 1)) (If (subst_bexp b x i) (subst_pexp p x i))) ).
  intros. apply H1. lia.
  destruct (IHna H H6 H2 H3) as [sa [Y1 [Y2 Y3]]]. clear H H6 H2 H3 IHna.
  assert (l <= l + S na < l + S (S na)) by lia.
  specialize (H1 (l + S na)).
  specialize (H10 (l + S na)).
  specialize (X1 (l + S na)).
  specialize (H5 (l + S na) H H10 X1 (subst_type_map T x (l + S na + 1))
        (H1 H) (fst s, sa) Y3 H8 Y1).
  destruct H5 as [sb [G1 [G2 G3]]].
  replace (l + S na + 1) with (l + S (S na)) in * by lia.
  exists sb. split; try easy.
  split. apply ForallA_cons with (s' := (fst s, sa)); try easy. easy.
  destruct H as [sa [Y1 [Y2 Y3]]].
  exists sa. split; try easy. split. constructor.
  replace (l+na-l) with na by lia.
  easy. easy.
- assert (freeVarsNotCPExp env e1).
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x); try easy.
  simpl in *. apply in_app_iff. left. easy.
  assert (freeVarsNotCPExp env e2).
  unfold freeVarsNotCPExp in *.
  intros. apply H2 with (x := x); try easy.
  simpl in *. apply in_app_iff. right. easy.
  destruct (IHtriple1 H7 H3 T1 H s H4 H5 H6) as [sa [A1 [A2 A3]]].
  destruct H as [X1 [X2 X3]].
  apply simple_tenv_ses_system in X2 as X4; try easy.
  destruct (IHtriple2 H8 X4 T2 H0 (fst s, sa) A3 H5 A1) as [sb [G1 [G2 G3]]].
  exists sb. split; try easy.
  split. apply seq_sem with (s1 := (fst s, sa)); try easy.
  destruct H0 as [X5 [X6 X7]]. destruct X7.
  destruct H1 as [G4 [G5 G6]]. inv G6.
  apply qpred_check_same with (T := tenv') in H0; try easy; subst. easy. 
Qed.

Lemma eval_aexp_equal: forall m m' v x, AEnv.Equal m m' -> eval_aexp m x v -> eval_aexp m' x v.
Proof.
  intros. induction H0. constructor.
  Check AEnv.equal_1.
  apply aenv_mapsto_equal with (s2 := m') in H0; try easy.
  constructor. constructor. apply IHeval_aexp. easy. easy.
  apply aplus_sem_2; try easy. apply IHeval_aexp.
  easy.
  constructor. apply IHeval_aexp. easy. easy.
  apply amult_sem_2; try easy. apply IHeval_aexp.
  easy.
Qed.

Lemma cmodel_equal: forall m m' W, AEnv.Equal m m' -> cmodel m W -> cmodel m' W.
Proof.
  intros. induction H0; intros; simpl in *. constructor.
  constructor. inv H0.
  apply eval_aexp_equal with (m' := m') in H3; try easy.
  apply eval_aexp_equal with (m' := m') in H4; try easy.
  apply ceq_asem with (r1 := r2) (r2 := r2) (n1 := n2) (n2 := n2); try easy.
  apply eval_aexp_equal with (m' := m') in H3; try easy.
  apply eval_aexp_equal with (m' := m') in H4; try easy.
  apply clt_asem with (r1 := r2) (r2 := r2) (n1 := n1) (n2 := n2); try easy.
  easy.
Qed.

Lemma eval_aexp_in_list: forall s a n env, eval_aexp s a n -> kind_env_stack env s ->
       sublist (freeVarsAExp a) env.
Proof.
  intros. induction H; simpl in *.
  assert (AEnv.In x s). exists (r,n). easy. apply H0 in H1.
  constructor. exists (Mo MT). easy. constructor.
  constructor. apply sublist_combine. apply IHeval_aexp. easy.
  apply simp_aexp_empty in H1. rewrite H1. constructor.
  apply sublist_combine.
  apply simp_aexp_empty in H1. rewrite H1. constructor.
  apply IHeval_aexp. easy.
  apply sublist_combine. apply IHeval_aexp. easy.
  apply simp_aexp_empty in H1. rewrite H1. constructor.
  apply sublist_combine.
  apply simp_aexp_empty in H1. rewrite H1. constructor.
  apply IHeval_aexp. easy.
Qed.

Lemma sublist_add: forall l env x v, sublist l env -> sublist l (AEnv.add x v env).
Proof.
  intros. induction H. constructor.
  constructor. bdestruct (x0 =? x); subst.
  exists v. apply AEnv.add_1. easy.
  destruct H. exists x1.
  apply AEnv.add_2. lia. easy.
  apply IHForall.
Qed.

Lemma sublist_app_l: forall l l1 env, sublist (l++l1) env -> sublist l env.
Proof.
  induction l; intros; simpl in *; try easy.
  constructor. inv H. constructor; try easy.
  eapply IHl. apply H3.
Qed.

Lemma sublist_app_r: forall l l1 env, sublist (l++l1) env -> sublist l1 env.
Proof.
  induction l; intros; simpl in *; try easy.
  inv H. apply IHl. easy.
Qed.

Lemma subst_aexp_not_in_eq: forall a i env l, ~ AEnv.In (elt:=ktype) i env
   -> sublist (freeVarsAExp a) env -> subst_aexp a i l  = a.
Proof.
  intros. induction a; intros; simpl in *.
  bdestruct (i =? x); subst. inv H0. easy.
  easy. easy. easy.
  rewrite IHa1; try easy. rewrite IHa2; try easy.
  apply sublist_app_r in H0; easy.
  apply sublist_app_l in H0; easy.
  rewrite IHa1; try easy. rewrite IHa2; try easy.
  apply sublist_app_r in H0; easy.
  apply sublist_app_l in H0; easy.
Qed.

Lemma subst_cbexp_not_in_eq: forall a i env l, ~ AEnv.In (elt:=ktype) i env
   -> sublist (freeVarsCBexp a) env -> subst_cbexp a i l  = a.
Proof.
  intros. induction a; intros; simpl in *.
  rewrite subst_aexp_not_in_eq with (env := env); try easy.
  rewrite subst_aexp_not_in_eq with (env := env); try easy.
  apply sublist_app_r in H0; easy.
  apply sublist_app_l in H0; easy.
  rewrite subst_aexp_not_in_eq with (env := env); try easy.
  rewrite subst_aexp_not_in_eq with (env := env); try easy.
  apply sublist_app_r in H0; easy.
  apply sublist_app_l in H0; easy.
Qed.

Lemma cpred_check_subst_eq: forall c env i l, ~ AEnv.In (elt:=ktype) i env
   -> cpred_check c (env:aenv) -> List.map (fun a => subst_cbexp a i l) c = c.
Proof.
  intros. induction H0. constructor.
  simpl in *.
  rewrite subst_cbexp_not_in_eq with (env := env); try easy.
  rewrite IHForall. easy.
Qed.

Lemma subst_range_twice_same: forall s i l, subst_range (subst_range s i l) i l = subst_range s i l.
Proof.
  intros. unfold subst_range in *.
  destruct s. destruct p.
  unfold subst_bound in *.
  destruct b eqn:eq1; try easy.
  destruct b0 eqn:eq2; try easy.
  bdestruct (i =? v1); subst; try easy.
  bdestruct (v1 =? v0); subst;try easy.
  bdestruct (v1 =? v0); subst;try easy.
  bdestruct (i =? v1); subst; try easy.
  bdestruct (i =? v0); subst; try easy.
  bdestruct (i =? v0); subst; try easy.
  bdestruct (i =? v0); subst; try easy.
  bdestruct (i =? v0); subst; try easy.
  destruct b0 eqn:eq2; try easy.
  bdestruct (i =? v0); subst; try easy.
  bdestruct (i =? v0); subst; try easy.
Qed.

Lemma subst_locus_twice_same: forall s i l, subst_locus (subst_locus s i l) i l = subst_locus s i l.
Proof.
  induction s; intros;simpl in *; try easy.
  rewrite subst_range_twice_same. rewrite IHs. easy.
Qed.

Lemma qpred_check_subst_eq: forall P T T' i l, T' = (subst_type_map T i l) -> 
  qpred_check T' P -> simple_qpred P
  -> List.map (fun a => qelem_subst_c a i l) P = P.
Proof.
  intros. generalize dependent T. induction H0; intros; subst; simpl in *; try easy.
  inv H1. destruct T0; simpl in *; try easy.
  destruct p. inv H3. inv H6.
  assert (qelem_subst_c (SV l1, v) i l = (SV l1, v)).
  unfold qelem_subst_c. simpl. inv H.
  rewrite subst_locus_twice_same.
  easy. rewrite H1.
  rewrite IHqpred_check with (T := T0); try easy.
Qed.

Lemma pred_check_subst_eq: forall P env T i l, ~ AEnv.In (elt:=ktype) i env 
  -> pred_check env (subst_type_map T i l) P -> simple_qpred (snd P) -> pred_subst_c P i l = P.
Proof.
  intros. inv H0.
  unfold pred_subst_c. rewrite cpred_check_subst_eq with (env := env); try easy.
  rewrite qpred_check_subst_eq with (T := T) (T' := subst_type_map T i l); try easy.
  destruct P; easy.
Qed.

Lemma simple_qpred_all: forall P i l, simple_qpred (List.map (fun a => qelem_subst_c a i l) P) ->
      (forall v, simple_qpred (List.map (fun a => qelem_subst_c a i v) P)).
Proof.
  induction P; intros; simpl in *; try easy.
  inv H. inv H2. destruct a; simpl in *.
  destruct s; try easy. simpl in *. 
  constructor. constructor.
  apply IHP with (l := l); easy.
Qed.

(* The assumption about the existence of loop invariant. *)
Axiom invariant_exists: forall rmax q env P Q T b e i l s s',
  pred_check env (subst_type_map T i l) (pred_subst_c P i l) -> model s' Q ->
  kind_env_stack env (fst s) -> env_state_eq (subst_type_map T i l) (snd s) -> 
  @triple rmax q env (subst_type_map T i l) (pred_subst_c P i l)
            (If (subst_bexp b i l) (subst_pexp e i l)) Q ->
  @qfor_sem rmax env s (If (subst_bexp b i l) (subst_pexp e i l)) s' -> 
  @locus_system rmax q env (subst_type_map T i l) (If (subst_bexp b i l) (subst_pexp e i l)) (subst_type_map T i (l + 1))
  -> Q = (pred_subst_c P i (l+1)).


Lemma proof_completeness: forall e rmax t env s s' T T' P, 
     @env_state_eq T (snd s) -> kind_env_stack env (fst s) -> freeVarsNotCPExp env e ->
      @locus_system rmax t env T e T' -> pred_check env T P -> simple_tenv T ->
       @qfor_sem rmax env s e s' ->  simple_qpred (snd P) -> model s P -> 
          (exists Q,simple_qpred Q /\ qpred_check T' Q /\  qmodel (snd s') Q /\ @triple rmax t env T P e (fst P, Q)).
Proof.
  intros. generalize dependent P. generalize dependent s. generalize dependent s'.
  induction H2; intros;simpl in *; try easy.
- destruct s0 ; simpl in *. apply env_state_eq_app in H as X1.
  destruct X1 as [q1 [q2 [X1 [X2 X3]]]]; subst.
  apply env_state_eq_same_length in X1 as [X4 X5].
  apply simple_tenv_app_l in H4 as X6.
  apply type_sem_local with (q := q) (T := T) (T' := T') in H5 as X7; try easy.
  destruct X7 as [sa [X7 [X8 X9]]].
  destruct s'. inv H7. simpl in *. subst.
  inv H3. apply pred_check_eq_app in H10 as [P1 [P2 [Y1 [Y2 [Y3 Y4]]]]]; subst; try easy.
  destruct P; simpl in *; subst.
  rewrite <- X3 in Y2. symmetry in Y2.
  apply qmodel_shrink in H9 as Y5; try easy.
  apply qmodel_shrink in H9 as Y6; try easy.
  apply qmodel_shrink_1 in H9 as Y7; try easy.
  apply simple_qpred_shrink_l in H6 as Y8.
  apply IHlocus_system with (P := (c,P1)) in X8; try easy.
  destruct X8 as [Q [G1 [G2 [G3 G4]]]].
  exists (Q++P2). simpl in *.
  split. apply simple_qpred_combine; try easy.
  apply simple_qpred_shrink_r in H6. easy.
  split. apply qpred_check_combine; easy.
  split. apply qmodel_combine; try easy.
  apply triple_frame with (T2 := T'); try easy.
  rewrite X3. easy.
- inv H. destruct s; simpl in *. subst. inv H3. destruct P; simpl in *. inv H7.
  inv H2. simpl in *.
  assert (forall rmax env s s', @qfor_sem rmax env s PSKIP s' -> snd s = nil -> fst s = fst s' /\ snd s' = nil).
  intros. remember PSKIP as e. induction H2; try easy.
  apply H2 in H5; try easy. destruct H5;simpl in *; subst.
  exists nil. simpl in *. split; constructor. constructor. simpl in *; try easy. constructor.
  destruct s'; simpl in *; subst; constructor.
  constructor.
- rewrite simple_env_subst in *; try easy.
  apply freeVars_pexp_in with (v := v) in H1 as X1; try easy.
  inv H6. rewrite H0 in H16. inv H16. apply IHlocus_system with (P := P) in H17; try easy.
  destruct H17 as [Q [Y1 [Y2 [Y3 Y4]]]].
  exists Q. split; try easy. split; try easy. split; try easy.
  apply let_c_pf with (T1 := T') (v := n); try easy.
  split; try easy. split; try easy. inv H7. split; try easy.
  apply simp_aexp_no_eval in H16. rewrite H16 in *. easy.
- inv H6. apply type_aexp_mo_no_simp in H. rewrite H in *. easy.
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H10. inv H10. easy.
  apply AEnv.add_3 in H10; try lia.
  apply H1 with (x0 := x0). simpl.
  apply in_app_iff. right.
  simpl in *.
  apply list_sub_not_in; try easy. easy.
  unfold update_cval in *. destruct s; simpl in *.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (fst (AEnv.add x n s, q0))).
  unfold kind_env_stack. split. intros.
  bdestruct (x0 =? x); subst.
  exists n. apply AEnv.add_1. easy.
  apply AEnv.add_3 in H10; try easy.
  apply H5 in H10. destruct H10.
  exists x1. apply AEnv.add_2. lia. easy. lia.
  intros.
  bdestruct (x0 =? x); subst.
  apply AEnv.add_1. easy.
  destruct H10.
  apply AEnv.add_3 in H10; try easy.
  assert (AEnv.In x0 s). exists x1. easy.
  apply H5 in H12.
  apply AEnv.add_2. lia. easy. lia.
  apply type_preserve with (q := q) (T := T) (T' := T') in H17 as Y1; try easy.
  destruct Y1 as [Y1 [Y2 Y3]].
  destruct P as [Pw Pa]. simpl in *.
  assert (cpred_check (CEq (BA x) a :: Pw) (AEnv.add x (Mo MT) env)) as Y4.
  constructor. simpl.
  apply eval_aexp_in_list with (env := env) in H16; try easy.
  constructor. exists (Mo MT). apply AEnv.add_1. easy.
  apply sublist_add. easy.
  inv H7. simpl in *. unfold cpred_check in H11.
  clear H9.
  induction H11. constructor. constructor. apply sublist_add. easy. easy.
  apply IHlocus_system with (P := ((CEq (BA x) a)::Pw,Pa)) in H17; try easy.
  destruct H17 as [Q [A1 [A2 [A3 A4]]]]; subst.
  exists Q. split; try easy. split; try easy.
  split; try easy. apply let_m_pf with (T1 := T'); try easy.
  split; try easy. split; try easy. simpl in *. inv H7. easy.
  inv H7. constructor; try easy.
  simpl in *. inv H9. constructor; try easy.
  simpl. constructor.
  apply ceq_asem with (r1 := fst n) (n1 := snd n) (r2 := fst n) (n2 := snd n); try easy.
  constructor. destruct n. simpl in *. apply AEnv.add_1. easy.
  apply eval_aexp_not_exists; try easy.
  intros R. apply H5 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  destruct n; try easy.
  clear Y4 H7; simpl in *. induction H11. constructor.
  constructor. apply eval_cabexp_not_exists.
  intros R. apply H5 in R. assert (AEnv.In x env). exists (Mo MT). easy. easy.
  easy. easy.
- inv H6; try easy.
  assert (freeVarsNotCPExp (AEnv.add x (Mo MT) env) e).
  unfold freeVarsNotCPExp in *. 
  intros.
  bdestruct (x0 =? x); subst.
  apply aenv_mapsto_add1 in H10. inv H10. easy.
  apply AEnv.add_3 in H10; try lia.
  apply H1 with (x0 := x0). simpl.
  right.
  apply list_sub_not_in; try easy. easy.
  assert (simple_tenv ((l, CH) :: T)).
  unfold simple_tenv in *. intros. simpl in *.
  destruct H10. inv H10.
  specialize (H4 ((y, BNum 0, BNum n) :: a) CH).
  assert (((y, BNum 0, BNum n) :: a, CH) = ((y, BNum 0, BNum n) :: a, CH) \/
     In ((y, BNum 0, BNum n) :: a, CH) T). left. easy.
  apply H4 in H10.
  inv H10. easy. apply H4 with (b:= b). right. easy.
  inv H3.
  assert (env_state_eq ((l0, CH) :: T) ((l0, va')::s0)).
  constructor; try easy.
  inv H23. inv H18. destruct (build_state_pars m n0 v (to_sum_c m n0 v bl) bl) eqn:eq1.
  inv H11. constructor.
  assert (kind_env_stack (AEnv.add x (Mo MT) env) (AEnv.add x (r, v) W)).
  unfold kind_env_stack in *. intros. split; intros.
  bdestruct (x0 =? x); subst.
  exists (r, v). apply AEnv.add_1. easy.
  apply AEnv.add_3 in H11; try lia.
  apply H5 in H11. destruct H11.
  exists x1. apply AEnv.add_2; try lia. easy.
  bdestruct (x0 =? x); subst. apply AEnv.add_1. easy.
  apply AEnv.add_2; try lia. apply H5. destruct H11. apply AEnv.add_3 in H11; try lia.
  exists x1. easy.
  destruct P. inv H7. simpl in *. inv H15. inv H8. inv H17. inv H21.
  inv H23. inv H9. inv H8. inv H26.
  replace ((y, BNum 0, BNum n0) :: l0) with ([(y, BNum 0, BNum n0)]++ l0) in H22; try easy.
  assert (ses_len ([(y, BNum 0, BNum n0)]) = Some n0).
  unfold ses_len; simpl in *. replace (n0-0+0) with n0 by lia. easy.
  apply ses_len_app_sub with (n := n0) in H22 as Y2; try easy.
  assert (n0 <= n) as Y3.
  unfold ses_len in *. simpl in *.
  destruct (get_core_ses l0) eqn:eq1; try easy.
  inv H22. inv Y2. lia.
  apply pick_mea_exist_same with (n0 := n) (ba := r2) in H16 as Y4; try easy.
  inv H3. inv H29.
  apply build_state_ch_exist_same with (n0 := n) (ba := r2) in H18 as Y5; try easy.
  destruct Y5 as [r3 [Y5 Y6]].
  specialize (simp_pred_mea x n0 l0 (Cval m r2) (Cval m0 r3) r v Y4 Y5) as X1.
  apply (IHlocus_system H6 H10) with
       (P := ((CEq (BA x) (MNum r v))::c,(SV l0, Cval m0 r3)::Sa)) in H19 as X2; try easy.
  destruct X2 as [Q [X2 [X3 [X4 X5]]]];subst.
  exists Q. split; try easy. split; try easy. split; try easy.
  apply let_q_pf with (T1 := T') (PM := (SV l0, Cval m0 r3)) (r' := r) (v' := v); try easy.
  split. constructor. constructor; try easy. simpl. constructor; try easy.
  exists (Mo MT). apply AEnv.add_1. easy.
  clear H7 X5.
  induction H12. constructor. constructor.
  apply sublist_add. easy. easy.
  constructor; try easy; try constructor.
  split; try easy.
  constructor; try easy.
  constructor; try easy. simpl. constructor.
  exists (Mo MT). apply AEnv.add_1. easy. constructor.
  clear H7 X5.
  induction H12. constructor. constructor.
  apply sublist_add. easy. easy.
  constructor; try easy. constructor.
  constructor;try easy.
  constructor; try easy. simpl. constructor.
  exists (Mo MT). apply AEnv.add_1. easy. constructor.
  clear H7.
  induction H12. constructor. constructor.
  apply sublist_add. easy. easy.
  constructor; try easy; constructor.
  constructor; try easy; try constructor.
  split. constructor; try easy. simpl.
  apply ceq_asem with (r1 := r) (r2 := r) (n1 := v) (n2 := v); try easy.
  constructor; try easy. apply AEnv.add_1; try easy.
  constructor. simpl in *.
  clear H12. induction H7. constructor.
  constructor; try easy. apply eval_cabexp_not_exists; try easy.
  intros. intros R. apply H5 in R.
  assert (AEnv.In x env). exists (Mo MT). easy. easy.
  apply model_many with (n := (n - n0)); try easy.
- destruct s. inv H2. inv H13. inv H14. simpl in *; subst.
  inv H5. destruct P. inv H6. inv H5. simpl in *; subst. inv H13.
  inv H14. inv H7. inv H9. inv H8. inv H11. inv H6. inv H14.
  apply eval_nor_switch_same with (l1 := nil) (n := n0) (b1 := r0) in H16 as X1; try easy.
  destruct X1 as [va [Y1 Y2]]; subst.
  destruct va;inv Y2; simpl in *.
  exists ([(SV l0, Nval c0 r1)]); try easy.
  split. constructor; try constructor.
  split. constructor; try constructor.
  split. apply model_many with (n := n0); try easy.
  constructor. easy. apply appu_nor_pf; try easy.
  rewrite app_nil_r. easy.
- destruct s. simpl in *. inv H2. inv H13. inv H14.
  destruct P; inv H6. inv H8. inv H10. inv H16. simpl in *; subst.
  inv H15. inv H5; try easy.
  apply app_inv_head_iff in H12; subst.
  apply eval_ch_switch_same with (l1 := l') (n := n0) (b1 := r2) in H20; try easy.
  destruct H20 as [va [X1 X2]]. inv X2.
  exists ([(SV (l ++ l'), Cval m va)]).
  split. constructor; try constructor.
  split. constructor; try constructor.
  split. apply model_many with (n := n0); try easy.
  constructor; try easy. constructor.
  apply appu_ch_pf; try easy. 
- destruct s. inv H2. inv H13. inv H14. simpl in *; subst.
  inv H5. destruct P. inv H6. inv H5. simpl in *; subst. inv H13.
  inv H14. inv H7. inv H9. inv H8. inv H11. inv H6. inv H14.
  rewrite H17 in H12. inv H12.
  exists ([(SV ([a]), Hval (eval_to_had n0 r0))]); try easy.
  split. constructor; try constructor.
  split. constructor; try constructor.
  split. apply model_many with (n := n0); try easy.
  constructor. intros.
  rewrite eval_to_nor_switch_same with (b := r0); try easy.
  apply apph_nor_pf; try easy.
- destruct s. inv H2. inv H13. inv H14. simpl in *; subst.
  inv H5. destruct P. inv H6. inv H5. simpl in *; subst. inv H13.
  inv H14. inv H7. inv H9. inv H8. inv H11. inv H6. inv H14.
  rewrite H16 in H12. inv H12.
  exists ([(SV ([a]), Nval C1 (eval_to_nor n0 bl0))]); try easy.
  split. constructor; try constructor.
  split. constructor; try constructor.
  split. apply model_many with (n := n0); try easy.
  constructor. intros.
  rewrite eval_to_had_switch_same with (b := bl0); try easy.
  apply apph_had_pf; try easy.
- inv H6; try easy.
  assert (freeVarsNotCPExp env e) as X1.
  unfold freeVarsNotCPExp in *.
  intros. apply H1 with (x := x) (t := t); try easy. simpl. apply in_app_iff. right. easy.
  apply (IHlocus_system X1 H4) with (P := P) in H16; try easy.
  destruct H16 as [Q [Y1 [Y2 [Y3 Y4]]]].
  exists Q. repeat split; try easy. apply if_c_t with (T1 := T'); try easy.
  inv H7. repeat split; try easy. rewrite H0 in *. easy.
  apply simp_bexp_no_qtype in H12. rewrite H12 in *. easy.
- inv H5. rewrite H0 in *. easy.
  destruct P; simpl in *. exists q0.
  inv H6. inv H8. repeat split; try easy.
  apply if_c_f; easy.
  apply simp_bexp_no_qtype in H11. rewrite H11 in *. easy.
- assert (freeVarsNotCPExp env e) as X1.
  unfold freeVarsNotCPExp in *.
  intros. apply H1 with (x := x) (t := t); try easy. simpl. apply in_app_iff. right. easy.
  assert (simple_tenv ([(l1, CH)])).
  unfold simple_tenv in *.
  intros. simpl in *. destruct H9; try easy. 
  inv H9. assert ((l ++ a, CH) = (l++a, CH) \/ False). left. easy.
  apply H4 in H9. apply simple_ses_app_r in H9. easy.
  inv H5. apply simp_bexp_no_qtype in H. rewrite H in *. easy.
  apply simp_bexp_no_qtype in H. rewrite H in *. easy.
  destruct P. inv H6. inv H10. inv H21. simpl in *; subst.
  inv H7. inv H11. inv H22. inv H17.
  apply type_bexp_ses_len in H as X2.
  apply type_bexp_only with (t := (QT n0, l0)) in H; try easy. inv H.
  inv H8. inv H6. inv H23. apply app_inv_head_iff in H11; subst.
  assert (n0 = n + n') as U1. apply ses_len_app_add with (l := l) (n := n) in H14; try easy.
  rewrite H14 in *. inv H17. easy. subst.
  inv H22.
  apply bexp_eval_same with (env := env) (n := n) 
         (n2 := n + n') (bl := bl) in H13 as Y1; try easy.
  destruct Y1 as [va [Y1 Y2]]. inv Y2.
  apply type_bexp_gt in H12 as A1.
  apply mut_state_same with (bl := r2) in H15 as Y3; try easy.
  destruct Y3 as [fca [Y3 Y4]].
  inv H15. inv Y4.
  assert (env_state_eq ([(l1, CH)])
       ([(l1,
         Cval (fst (grab_bool f' m0 n))
           (mut_fch_state 0 n n' (snd (grab_bool f' m0 n))))])).
  constructor; try constructor.
  apply type_preserve with (q := MT) (T := ([(l1, CH)])) (T' := ([(l1, CH)])) in H18 as A2; try easy.
  destruct A2 as [A2 [A3 A4]]. inv A4. inv H11. simpl in *.
  assert (env_state_eq ([(l1, CH)]) ([(l1, (Cval (fst (grab_bool f' m0 n)) r0))])).
  constructor; try constructor.
  assert (subst_ses_qpred ([(SV (l ++ l1), Cval m0 bl)]) 
       (l++l1) (Frozen b (SV l) (SV l1)) ([(Frozen b (SV l) (SV l1),Cval m0 bl)])).
  constructor; try constructor.
  assert (resolve_frozen ([(Frozen b (SV l) (SV l1),Cval m0 bl)])
    ([(SV l1, (Cval (fst (grab_bool f' m0 n)) r0))])).
  apply resolve_frozen_many_2 with (f' := r2) (n := n) (n1 := n'); try easy.
  apply IHlocus_system with (P := (c,([(SV l1, Cval (fst (grab_bool f' m0 n)) r0)])))
     in H18 as Y4; try easy.
  destruct Y4 as [Q [Y4 [Y5 [Y6 Y7]]]].
  inv Y5. inv H27. inv H28. inv Y4. inv H23. inv H25.
  assert (subst_ses_qpred ([(SV (l ++ l0), Cval m0 bl)]) (l++l0)
    (Unfrozen n (BNeg b) (SV (l++l0))) ([((Unfrozen n (BNeg b) (SV (l++l0))),Cval m0 bl)])) as A4.
  constructor; try constructor.
  inv H24. inv Y6. inv H28.
  apply assem_bool_same with (f' := r2) (r' := bl0) in H20 as G1; try easy.
  destruct G1 as [fca [G1 G2]].
  assert (subst_ses_qpred ([(SV l0, Cval m bl0)]) l0 (Unfrozen n b (SV (l++l0)))
           ([((Unfrozen n b (SV (l++l0))),Cval m bl0)])).
  constructor; try constructor.
  assert (resolve_unfrz ([(Unfrozen n (BNeg b) (SV (l ++ l0)), Cval m0 bl)]
      ++[((Unfrozen n b (SV (l++l0))),Cval m bl0)]) ([((SV (l++l0)),fca)])).
  apply resolve_unfrz_many_2 with (f' := r2) (n1 := n'); try easy.
  exists ([(SV (l ++ l0), fca)]).
  split; try constructor. constructor. constructor.
  constructor;try constructor. inv G1; constructor.
  split; try constructor. apply model_many with (n := n + n'); try easy.
  apply if_q with (n1 := n) (P' := [(Frozen b (SV l) (SV l0), Cval m0 bl)]) 
    (P'' := [(SV l0, Cval (fst (grab_bool f' m0 n)) r0)])
   (Q := [(SV l0, Cval m bl0)]) (Pa := [(Unfrozen n (BNeg b) (SV (l ++ l0)), Cval m0 bl)])
   (Qa := [(Unfrozen n b (SV (l ++ l0)), Cval m bl0)]) ; try easy.
  split; try constructor; try easy. constructor; try constructor.
  constructor; try constructor. simpl in *. easy.
  1-4:constructor. 1-2:constructor.
  intros. apply H23 in H21. split; try easy. destruct H21. intros.
  rewrite H22; try easy.
  rewrite H14 in *. inv H25. easy.
  constructor; try constructor. simpl in *. easy.
  1-4:constructor. 1-2:constructor.
  constructor; try easy.
  apply model_many with (n := n'); try easy; try constructor.
  intros. apply H15 in H21. split; try easy. 
  intros. destruct H21.
  unfold mut_fch_state; simpl in *.
  rewrite H23. easy. lia.
- assert (freeVarsNotCPExp env e1).
  unfold freeVarsNotCPExp in *.
  intros. apply H1 with (x := x); try easy.
  simpl in *. apply in_app_iff. left. easy.
  assert (freeVarsNotCPExp env e2).
  unfold freeVarsNotCPExp in *.
  intros. apply H1 with (x := x); try easy.
  simpl in *. apply in_app_iff. right. easy.
  inv H5.
  destruct (IHlocus_system1 H2 H4 s1 s H H0 H13 P H3 H6 H7) as [R [A1 [A2 [A3 A4]]]].
  apply type_preserve with (q := q) (T := T) (T' := T1) in H13 as [X1 [X2 X3]]; try easy.
  apply simple_tenv_ses_system in H2_ as X4; try easy.
  apply kind_env_stack_equal with (env := env) in X2 as X5; try easy.
  assert (pred_check env T1 (fst P, R)).
  constructor. inv H3. simpl in *; try easy. easy.
  destruct (IHlocus_system2 H8 X4 s' s1 X3 X5 H15 (fst P, R) H5 A1) as [Q [G1 [G2 [G3 G4]]]].
  split. simpl in *. apply cmodel_equal with (m := fst s); try easy.
  inv H7. easy. inv H7. easy.
  exists Q. split; try easy. split; try easy. split; try easy.
  apply seq_pf with (T3 := T1) (T4 := T2) (R0 := (fst P, R)); try easy.
  split;try easy. split; try easy. inv H3. constructor; try easy.
- inv H5. assert (h -l = 0) by lia. rewrite H5 in *. inv H16. inv H7. inv H3.
  exists (snd P). split; try easy. split; try easy. split; try easy.
  destruct P; apply for_pf_f. easy.
- inv H7. 
  assert (forall v, freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v))) as X1.
  intros.
  unfold freeVarsNotCPExp in *.
  intros;simpl in *.
  apply H1 with (x := x); try easy.
  bdestruct (x =? i); subst. assert (AEnv.In i env). exists (Mo t). easy. easy.
  apply in_app_iff in H7. destruct H7.
  apply freeVarsBExp_subst in H7.
  apply in_app_iff. left. apply list_sub_not_in; try easy.
  apply in_app_iff. right. apply freeVarsPExp_subst in H7.
  apply list_sub_not_in; try easy.
  specialize (simple_tenv_subst_right T i l H4) as X2.
  remember (h-l) as na.
  assert (h = l + na) by lia. rewrite H7 in *. clear H7 Heqna.
  assert ((forall v, l <= v < l+na -> type_check_proof rmax q env (subst_type_map T i v) (subst_type_map T i (v+1))
              (pred_subst_c P i v) (pred_subst_c P i (v+1)) (If (subst_bexp b i v) (subst_pexp e i v)))
          /\ (forall v, l <= v < l+na -> 
            @triple rmax q env (subst_type_map T i v) (pred_subst_c P i v)
                     (If (subst_bexp b i v) (subst_pexp e i v)) (pred_subst_c P i (v+1)))
          /\ qmodel (snd s') (snd (pred_subst_c P i (l+na)))). 
  clear H1 H4.
  generalize dependent s'.
  induction na; intros; simpl in *; try easy.
  split. intros. lia.
  split. intros. lia.
  replace (l+0) with l by lia.
  inv H19.
  rewrite <- pred_check_subst_eq with (env := env) (T := T) (i := i) (l := l) in H10; try easy.
  inv H10. easy. inv H19.
  destruct na. simpl in *. inv H4.
  replace (l + 0) with l in * by lia.
  assert (l <= l < l+1) by lia.
  specialize (X1 l). specialize (X2 l).
  assert (simple_qpred (snd ((pred_subst_c P i l)))).
  rewrite pred_check_subst_eq with (env := env) (T := T) (i := i) (l := l); try easy.
  destruct P as [c P]; subst; assert (X3 := H10); inv H10; simpl in *.
  rewrite <- pred_check_subst_eq with (env := env) (T := T) (i := i) (l := l) in X3; try easy.
  assert (X4 := H8).
  rewrite <- pred_check_subst_eq with (env := env) (T := T) (i := i) (l := l) in H8; try easy.
  inv X4. simpl in *.
  destruct (H3 l H1 X1 X2 s' s'0 H5 H6 H7 (pred_subst_c (c,P) i l) H8 H4 X3) as [Q [Y1 [Y2 [Y3 Y4]]]].
  simpl in *.
  apply H2 in H1 as Y5; try easy.
  rewrite cpred_check_subst_eq with (env := env) (i := i) (l := l) in Y4; try easy.
  apply type_preserve with (q := q) (T := (subst_type_map T i l))
   (T' := (subst_type_map T i (l+1))) in H7 as Y6; try easy.
  destruct Y6 as [Y6 [Y7 Y8]].
  apply cmodel_equal with (m' := (fst s')) in H11 as Y9; try easy.
  apply (invariant_exists rmax q env (c, P) (c,Q) T b e i l s'0 s' H8) in Y4 as Y10; try easy.
  inv Y10.
  split. intros. assert (v = l) by lia; subst.
  split; try easy. split. rewrite <- H15; try easy. simpl.
  inv H8; try easy. simpl. inv H8; try easy.
  split; try easy. split. simpl. rewrite <- H15. rewrite <- H15. easy.
  simpl. easy.
  split; intros; try easy.
  rewrite <- H15 in *.
  assert (v = l) by lia; subst.
  assert ((c, map (fun a : qpred_elem => qelem_subst_c a i (l + 1)) P) = (pred_subst_c (c, P) i (l + 1))).
  unfold pred_subst_c. simpl in *.
  rewrite <- H15. easy. rewrite <- H16. easy.
  assert (l < l + S na) by lia.
  assert ((forall v : nat,
        l <= v < l + S na ->
        @locus_system rmax q env (subst_type_map T i v)
          (If (subst_bexp b i v) (subst_pexp e i v))
          (subst_type_map T i (v + 1)))).
  intros. apply H2. lia.
  assert ((forall v : nat,
        l <= v < l + S na ->
        freeVarsNotCPExp env (If (subst_bexp b i v) (subst_pexp e i v)) ->
        simple_tenv (subst_type_map T i v) ->
        forall (s' : state) (s : stack * qstate),
        env_state_eq (subst_type_map T i v) (snd s) ->
        kind_env_stack env (fst s) ->
        @qfor_sem rmax env s (If (subst_bexp b i v) (subst_pexp e i v)) s' ->
        forall P : cpred * qpred,
        pred_check env (subst_type_map T i v) P ->
        simple_qpred (snd P) ->
        model s P ->
        exists Q : qpred,
          simple_qpred Q /\
          qpred_check (subst_type_map T i (v + 1)) Q /\
          qmodel (snd s') Q /\
          @triple rmax q env (subst_type_map T i v) P
            (If (subst_bexp b i v) (subst_pexp e i v)) 
            (fst P, Q))).
  intros. apply H3 with (s := s0); try easy. lia.
  specialize (IHna H1 H11 H12 s'0 H4).
  destruct IHna as [Y1 [Y2 Y3]]. clear H11. clear H12.
  assert (l <= l + S na < l + S (S na)) by lia.
  apply type_preserves with (q := q) (T := T) in H4 as Y4; try easy.
  destruct Y4 as [Y4 Y5].
  apply kind_env_stack_equal with (env := env) in Y4 as Y6; try easy.
  assert (A1 := Y1).
  assert (l <= l + na < l + S na) by lia.
  specialize (A1 (l+na) H12).
  destruct A1 as [A1 [A2 A3]].
  replace (l + na + 1) with (l + S na) in * by lia.
  apply Y1 in H12. destruct H12 as [G1 [G2 G3]].
  replace ((l + na + 1)) with (l + S na) in * by lia.
  specialize (H3 (l+S na) H11 (X1 (l+S na)) (X2 (l+ S na)) s' s'0 Y5 Y6 H7).
  destruct P as [c P]. inv H8. simpl in *.
  apply H3 in A3.
  destruct A3 as [Q [A3 [A4 [A5 A6]]]].
  replace (l + S na + 1) with (l + S (S na)) in * by lia.
  assert (l <= l + S na < l+S (S na)) as Y7 by lia.
  apply H2 in Y7.
  apply (invariant_exists rmax q env (c,P)
           (fst (pred_subst_c (c, P) i (l + S na)), Q) T b e i (l+S na) s'0 s') in H7 as A7; try easy.
  unfold pred_subst_c in A7; simpl in *. inv A7.
  replace (l + S na + 1) with (l + S (S na)) in * by lia.
  split. intros.
  bdestruct (v =? l + (S na)); subst.
  unfold pred_subst_c; simpl in *.
  split; constructor; simpl; try easy.
  rewrite cpred_check_subst_eq with (env := env); try easy.
  inv G3. easy.
  apply H2; try lia.
  split; simpl.
  rewrite cpred_check_subst_eq with (env := env) (i := i); try easy.
  replace (l + S na + 1) with (l + S (S na)) by lia. easy.
  apply Y1; try easy. lia.
  split. intros.
  bdestruct (v =? l + (S na)); subst.
  replace ((l + S na + 1)) with (l + S (S na)) in * by lia.
  rewrite cpred_check_subst_eq with (env := env) (i := i) in A6; try easy.
  replace (pred_subst_c (c, P) i (l + S (S na)))
    with (c, map (fun a : qpred_elem => qelem_subst_c a i (l + S (S na))) P).
  easy.
  unfold pred_subst_c. simpl.
  rewrite cpred_check_subst_eq with (env := env) (i := i); try easy.
  apply Y2; try easy. lia.
  easy.
  unfold pred_subst_c; constructor; simpl.
  rewrite cpred_check_subst_eq with (env := env) (i := i); try easy.
  apply type_preserve with (q := q) (T := (subst_type_map T i (l + S na)))
        (T' := (subst_type_map T i (l + S (S na)))) in H7; try easy.
  destruct H7 as [Y8 [Y9 Y10]].
  replace (l + S na + 1) with (l + S (S na)) in * by lia.
  unfold pred_subst_c; simpl.
  inv H10.
  apply cmodel_equal with (m := fst s'0); try easy.
  apply cmodel_equal with (m := fst s); try easy.
  replace (l + S na + 1) with (l + S (S na)) in * by lia. easy.
  easy.
  apply simple_qpred_all with (l := l).
  simpl.
  rewrite qpred_check_subst_eq with (T := T) (T' := subst_type_map T i l); try easy.
  unfold pred_subst_c in *; simpl in *.
  constructor; try easy.
  rewrite cpred_check_subst_eq with (env := env); try easy. simpl.
  apply cmodel_equal with (m := fst s); try easy. inv H10; try easy.
  intros. apply H2; try easy. lia.
  destruct H7 as [G1 [G2 G3]].
  rewrite <- pred_check_subst_eq with (P := P) (env := env) (T := T) (i := i) (l := l); try easy.
  exists (snd (pred_subst_c P i (l + na))).
  split.
  unfold pred_subst_c; simpl.
  apply simple_qpred_all with (l := l).
  rewrite qpred_check_subst_eq with (T := T) (T' := subst_type_map T i l); try easy.
  inv H8. easy.
  split.
  assert (l <= l + na - 1 < l + na) by lia.
  apply G1 in H7.
  replace (l + na - 1 + 1) with (l + na) in * by lia.
  destruct H7 as [Y1 [Y2 Y3]].
  inv Y3. easy.
  split; try easy.
  replace ((@pair cpred qpred (@fst cpred qpred (pred_subst_c P i l))
     (@snd (list cbexp) (list (prod sval state_elem))
        (pred_subst_c P i (Init.Nat.add l na)))))
     with (pred_subst_c P i (l + na)).
  apply for_pf; try easy.
  unfold pred_subst_c; simpl.
  inv H8.
  rewrite cpred_check_subst_eq with (env := env); try easy.
  rewrite cpred_check_subst_eq with (env := env); try easy.
Qed.
