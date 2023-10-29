Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import OQASM.
Require Import OQASMProof.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import QWhileSyntax.
Require Import SessionDef.
Require Import SessionKind.
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


(* This is the semantics for basic gate set of the language. *)

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

Definition eval_to_had (n:nat) (b:rz_val) := (fun i => if i <? n then (update allfalse 0 (b i)) else allfalse).

Definition eval_to_nor (n:nat) (b:nat -> rz_val) := (fun i => if i <? n then b i 0 else false).

Lemma type_exp_exists_oqasm: forall env e n l, type_exp env e (QT n,l) 
   -> (exists e', compile_exp_to_oqasm e = Some e').
Proof.
  intros. induction H; simpl in *; try repeat eauto.
  destruct IHtype_exp. rewrite H3. exists (OQASM.CU (x,v) x0). auto.
  destruct IHtype_exp1, IHtype_exp2. rewrite H3. rewrite H2.
  exists (x; x0)%exp. auto.
Qed.

Definition all_nor_mode (f:posi -> val) := forall x n, right_mode_val OQASM.Nor (f (x,n)).

Lemma compile_range_state_nor: forall n s i x b f, all_nor_mode f
        -> all_nor_mode (compile_range_state n s i x b f).
Proof.
  intros. induction n;simpl in *. easy.
  unfold all_nor_mode in *. intros.
  bdestruct (posi_eq (x, s + n) (x0, n0)).
  inv H0. rewrite eupdate_index_eq. constructor.
  rewrite eupdate_index_neq; try easy.
Qed.

Lemma compile_ses_state'_nor: forall l i b,
           all_nor_mode (compile_ses_state' i l b).
Proof.
  induction l;intros;simpl in *.
  unfold all_nor_mode. intros. constructor.
  destruct a. destruct p. destruct b1. easy. destruct b0. easy.
  apply compile_range_state_nor.
  apply IHl.
Qed.

Lemma turn_oqasm_range_exists: forall n rmax st i x f r b, all_nor_mode f ->
         exists v t, turn_oqasm_range rmax n st i x f r b = Some (v,t).
Proof.
  intros.
  induction n;simpl in *.
  exists r,b. easy.
  destruct IHn as [v [t X1]]. rewrite X1.
  destruct (f (x, st + n)) eqn:eq1.
  exists (n_rotate rmax r0 v), (update t (i + n) b0). easy.
  unfold all_nor_mode in *.
  specialize (H x (st+n)). inv H. rewrite eq1 in H0. inv H0.
Qed.

Lemma get_core_simple: forall l, simple_ses l -> (exists na, get_core_ses l = Some na).
Proof.
  intros. induction l;try easy.
  simpl in *. exists nil. easy.
  simpl in *. inv H. unfold simple_bound in *. destruct x. easy. destruct y. easy.
  apply IHl in H4. destruct H4. rewrite H. exists ((a0, n, n0) :: x).
  easy.
Qed.

Lemma ses_len_simple: forall l, simple_ses l -> (exists na, ses_len l = Some na).
Proof.
  intros. unfold ses_len. apply get_core_simple in H.
  destruct H. rewrite H. exists (ses_len_aux x). easy.
Qed.

Lemma turn_oqasm_ses_simple: forall l n r f b, simple_ses l
      -> all_nor_mode f -> exists na, turn_oqasm_ses' r n l f b = Some na.
Proof.
  induction l; intros;simpl in *.
  exists (allfalse, b); try easy.
  destruct a. destruct p. inv H. unfold simple_bound in *.
  destruct b1. easy. destruct b0; try easy.
  apply (IHl (n + (n1 - n0)) r f b) in H7.
  destruct H7. rewrite H. destruct x.
  apply (turn_oqasm_range_exists (n1-n0) r n0 n v f b0 r0) in H0 as X1.
  destruct X1 as [v0 [t0 X1]]. exists (v0,t0). easy. easy.
Qed.

Lemma right_mode_env_compile_ses : forall l aenv b n t, compile_ses_qenv aenv l = (n, t)
    -> all_nor_mode (compile_ses_state l b) -> (forall x : Env.key, Env.MapsTo x OQASM.Nor (form_oenv t))
    -> right_mode_env n (form_oenv t) (compile_ses_state l b).
Proof.
  induction l;intros;simpl in *.
  unfold right_mode_env in *. intros.
  unfold all_nor_mode in *. destruct p. specialize (H0 v n0).
  simpl in *. specialize (H1 v).
  apply mapsto_always_same with (v1 := t0) in H1; subst; try easy.
  simpl in *.
  destruct a. destruct p.
  destruct (AEnv.find (elt:=ktype) v aenv) eqn:eq1. destruct k.
  unfold right_mode_env. intros. destruct p.
  unfold all_nor_mode in *. specialize (H0 v0 n0). simpl in *.
  specialize (H1 v0).
  apply mapsto_always_same with (v1 := t0) in H1; subst; try easy.
  destruct (compile_ses_qenv aenv l) eqn:eq2.
  destruct (var_in_list l0 v) eqn:eq3. inv H.
  unfold right_mode_env. intros. destruct p.
  unfold all_nor_mode in *. specialize (H0 v0 n1). simpl in *.
  specialize (H1 v0).
  apply mapsto_always_same with (v1 := t0) in H1; subst; try easy.
  unfold right_mode_env. intros. destruct p.
  unfold all_nor_mode in *. specialize (H0 v0 n2). simpl in *.
  specialize (H1 v0).
  apply mapsto_always_same with (v1 := t0) in H1; subst; try easy.
  unfold right_mode_env. intros. destruct p.
  unfold all_nor_mode in *. specialize (H0 v0 n0). simpl in *.
  specialize (H1 v0).
  apply mapsto_always_same with (v1 := t0) in H1; subst; try easy.
Qed.

Lemma compile_exp_WF : forall e ea l aenv qenv vl x v n, compile_ses_qenv aenv l = (qenv, vl)
      -> compile_exp_to_oqasm e = Some ea -> type_exp aenv e (QT n, l) -> v >= qenv x 
      -> exp_WF qenv ea.
Proof.
  induction e;intros;simpl in *.
  inv H1. inv H0. constructor. simpl in *.
  apply AEnv.find_1 in H7. rewrite H7 in H. inv H.
  bdestruct (x =? x). lia. easy.
  admit.
  destruct a; try easy.
  destruct (compile_exp_to_oqasm e) eqn:eq1; try easy. inv H0.
  constructor. simpl in *. inv H1.
Admitted.

Lemma compile_exp_fresh : forall e ea l aenv qenv vl x v n, compile_ses_qenv aenv l = (qenv, vl)
      -> compile_exp_to_oqasm e = Some ea -> type_exp aenv e (QT n, l) -> v >= qenv x 
      -> exp_fresh qenv (x,v) ea.
Proof.
Admitted.

Lemma eval_nor_exists {rmax : nat} : forall aenv l n c b e,
          type_exp aenv e (QT n,l) -> simple_ses l -> oracle_prop aenv l e
                 -> exists ba, eval_nor rmax aenv l c b e = Some ba.
Proof.
  intros.
  apply type_exp_exists_oqasm in H as X1.
  destruct X1 as [ea X1].
  apply ses_len_simple in H0 as X2. destruct X2.
  unfold eval_nor. destruct (compile_ses_qenv aenv l) eqn:eq1. rewrite X1.
  rewrite H2.
  specialize (turn_oqasm_ses_simple l 0 rmax (exp_sem n0 ea (compile_ses_state l b)) (cover_n b x) H0) as X2.
  assert (all_nor_mode (compile_ses_state l b)) as X3.
  unfold compile_ses_state. apply compile_ses_state'_nor.
  assert (right_mode_env n0 (form_oenv l0) (compile_ses_state l b)) as X4.
  apply right_mode_env_compile_ses with (aenv := aenv); try easy. 
  unfold oracle_prop in *. rewrite eq1 in H1. rewrite X1 in H1.
  destruct H1; try easy.
  unfold oracle_prop in *.
  rewrite eq1 in H1.
  rewrite X1 in H1.
  destruct H1 as [X5 X6].
  apply well_typed_right_mode_pexp with (e := ea) (tenv' := (form_oenv l0)) in X4 as eq2; try easy.
  assert (all_nor_mode (exp_sem n0 ea (compile_ses_state l b))).
  unfold all_nor_mode, right_mode_env in *. intros.
  specialize (X3 x0 n1). inv X3.
  specialize (eq2 OQASM.Nor (x0,n1)). simpl in *.
  bdestruct (n1 <? n0 x0). apply eq2 in H3; try easy.
  apply (compile_exp_WF e ea l aenv n0 l0 x0 n1 n) in H3 as X7; try easy.
  apply (compile_exp_fresh e ea l aenv n0 l0 x0 n1 n) in H3 as X8; try easy.
  rewrite efresh_exp_sem_irrelevant; try easy.
  assert (all_nor_mode (compile_ses_state l b)).
  apply compile_ses_state'_nor. unfold all_nor_mode in *. apply H4.
  apply (turn_oqasm_ses_simple l 0 rmax (exp_sem n0 ea (compile_ses_state l b)) (cover_n b x)) in H1 as X7.
  destruct X7. unfold turn_oqasm_ses. rewrite H3. destruct x0.
  exists ((c * Cexp (2 * PI * turn_angle b0 rmax))%C, r). easy. easy.
Qed.

Lemma eval_ch_exists {rmax : nat} : forall m aenv l n f e,
          type_exp aenv e (QT n,l) -> simple_ses l -> oracle_prop aenv l e
                 -> exists ba, eval_ch rmax aenv l m f e = Some ba.
Proof.
  induction m; intros;simpl in *.
  exists (fun _ : nat => (C0, allfalse)).
  easy.
  apply (@eval_nor_exists rmax aenv l n (fst (f m)) (snd (f m)) e) in H as X1; try easy.
  destruct X1. rewrite H2. destruct x.
  apply (IHm aenv l n f) in H as X1; try easy. destruct X1.
  rewrite H3. 
  exists (update x m (c, r)). easy.
Qed.


(* functions for defining boolean. *)

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

Axiom grab_bool_gt : forall f m size, m > 0 -> size > 0 -> fst (grab_bool f m size) > 0.

Inductive eval_bexp : qstate -> bexp -> qstate -> Prop :=
    | beq_sem_1 : forall s x y z i l n m f, 
                     eval_bexp (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m f)::s)
                                 (BEq (BA x) ((Num y)) z (Num i)) 
                            (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m (eval_eq_bool f m n y))::s)
    | beq_sem_2 : forall s x y z i l n m f, 
                eval_bexp (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m f)::s)
                                   (BEq ((Num y)) (BA x) z (Num i))
                            (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m (eval_eq_bool f m n y))::s)
    | blt_sem_1 : forall s x y z i l n m f, 
                eval_bexp ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f)::s)
                       (BLt (BA x) ((Num y)) z (Num i)) 
                         ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),(Cval m (eval_lt_bool f m n y)))::s)

    | blt_sem_2 : forall s x y z i l n m f, 
                 eval_bexp ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f)::s)
                        (BLt ((Num y)) (BA x) z (Num i))
                       ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),(Cval m (eval_rlt_bool f m n y)))::s)
    | btext_sem : forall s z i, eval_bexp s (BTest z (Num i)) s.

Lemma eval_bexp_det: forall q b q1 q2, eval_bexp q b q1 -> eval_bexp q b q2 -> q1 = q2.
Proof.
  intros. induction b;intros;simpl in *.
  inv H. inv H. inv H0. easy. inv H0. easy.
  inv H. inv H0. easy. inv H0. easy. inv H. inv H0. easy.
  inv H.
Qed.

Axiom bexp_eval_same: forall env b n n2 l l1 m r bl f, type_bexp env b (QT n, l) -> ses_len l = Some n ->
   ses_len (l ++ l1) = Some n2 ->
   (forall j : nat,
      j < m ->
      fst (r j) = fst (bl j) /\
      (forall i : nat, i < n2 -> snd (r j) i = snd (bl j) i)) ->
   eval_bexp ([(l ++ l1, Cval m bl)]) b ([(l ++ l1, Cval m f)]) ->
   eval_bexp ([(l ++ l1, Cval m r)]) b ([(l ++ l1, Cval m f)]).

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

Axiom assem_bool_gt : forall m m' n f fc fa, m > 0 -> m' > 0 -> assem_bool m m' n f fc fa -> (fst fa) > 0.

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

(*big step semantics. *)
Inductive ForallA (rmax:nat) (P: nat -> aenv -> state -> pexp -> state -> Prop):
             nat -> aenv -> state -> nat -> var -> bexp -> pexp -> state -> Prop :=
      | ForallA_nil : forall env l x b e s, ForallA rmax P 0 env s l x b e s
      | ForallA_cons : forall n env l x b e s s' s'', ForallA rmax P n env s l x b e s' ->
              P rmax env s' (If (subst_bexp b x (l+n)) (subst_pexp e x (l+n))) s''
             -> ForallA rmax P (S n) env s l x b e s''.

Inductive qfor_sem {rmax:nat}
           : aenv -> state -> pexp -> state -> Prop :=
  | state_eq_sem: forall aenv e s f f' S, @state_equiv rmax f f' -> qfor_sem aenv (s,f') e S -> qfor_sem aenv (s,f) e S
  | skip_sem : forall aenv s, qfor_sem aenv s PSKIP s
  | let_sem_c : forall aenv s s' x a n e, simp_aexp a = Some n -> qfor_sem aenv s (subst_pexp e x n) s'
        -> qfor_sem aenv s (Let x (AE a) e) s'
  | let_sem_m : forall aenv s s' x a n e, eval_aexp (fst s) a n -> qfor_sem (AEnv.add x (Mo MT) aenv) (update_cval s x n)  e s'
             -> qfor_sem aenv s (Let x (AE a) e) s'
  | let_sem_q : forall aenv W s s' l x a n e r v va va', AEnv.MapsTo a (QT n) aenv ->
                       @pick_mea n va (r,v) -> build_state_ch n v va = Some va' -> 
                    qfor_sem (AEnv.add x (Mo MT) aenv) (AEnv.add x (r,v) W, (l,va')::s) e s'
                  -> qfor_sem aenv (W,((a,BNum 0,BNum n)::l,va)::s) (Let x (Meas a) e) s'

  | appu_sem_nor : forall aenv W s a e l r b ra ba, 
      eval_nor rmax aenv a r b e = Some (ra,ba) -> qfor_sem aenv (W,(a++l,Nval r b)::s) (AppU a e) (W,(a++l,Nval ra ba)::s)
  | appu_sem_ch : forall aenv W s a e l b m ba, eval_ch rmax aenv a m b e = Some ba
          -> qfor_sem aenv (W,(a++l,Cval m b)::s) (AppU a e) (W,(a++l,Cval m ba)::s)

  | appsu_sem_h_nor : forall aenv W s p a r b n, @simp_varia aenv p a -> ses_len ([a]) = Some n ->
          qfor_sem aenv (W,([a],Nval r b)::s) (AppSU (RH p)) (W,([a],(Hval (eval_to_had n b)) )::s)

  | appsu_sem_h_had : forall aenv W s p a b n, @simp_varia aenv p a -> ses_len ([a]) = Some n ->
          qfor_sem aenv (W,([a],Hval b)::s) (AppSU (RH p)) (W,([a],(Nval C1 (eval_to_nor n b)))::s)
  (* rewrite the tenv type for oqasm with respect to the ch list type. *)

  | if_sem_ct : forall aenv s s' b e, simp_bexp b = Some true -> qfor_sem aenv s e s' -> qfor_sem aenv s (If b e) s'
  | if_sem_cf : forall aenv s b e, simp_bexp b = Some false -> qfor_sem aenv s (If b e) s
(*
  | if_sem_mt : forall aenv M s S b e, eval_cbexp M b true -> qfor_sem aenv (M,s) e S -> qfor_sem aenv (M,s) (If b e) S
  | if_sem_mf : forall aenv M s b e, eval_cbexp M b false -> qfor_sem aenv (M,s) (If b e) (M,s)
*)
  | if_sem_q : forall aenv W W' l l1 n n' s s' b e m m' f f' fc fc' fc'' fa,
     type_bexp aenv b (QT n,l) -> @eval_bexp ((l++l1, Cval m f)::s) b ((l++l1, Cval m f')::s) -> ses_len l1 = Some n' ->
     mut_state 0 n n' (Cval (fst (grab_bool f' m n)) (snd (grab_bool f' m n))) fc ->
     qfor_sem aenv (W,(l1,fc)::s) e (W',(l1,fc')::s') -> mut_state 0 n' n fc' (Cval m' fc'') ->
     assem_bool m m' n f' fc'' fa ->
     qfor_sem aenv (W,(l++l1, Cval m f)::s) (If b e) (W',(l++l1, Cval (fst fa) (snd fa))::s')
(*
  | if_sem_q : forall aenv l l1 n n' s s' sa sa' sac b e m m' f f' fc fc' fa,
               type_bexp aenv b (QT n,l) -> @eval_bexp rmax aenv s b s' ->
                @find_state rmax s' l (Some (l++l1, Cval m f)) -> ses_len l1 = Some n' ->
                 mut_state 0 n n' (Cval (fst (grab_bool f m n)) (snd (grab_bool f m n))) fc ->
                @up_state rmax s' (l++l1) fc sa -> qfor_sem aenv sa e sa' ->
                 @find_state rmax sa' l1 (Some (l1, fc')) -> mut_state 0 n' n fc' (Cval m' f') ->
                assem_bool m m' n f f' fa -> @up_state rmax s (l++l1) (Cval (fst fa) (snd fa)) sac ->
                    qfor_sem aenv s (If b e) sac
*)

 (* | diffuse_a: forall aenv s s' x n l n' l1 m f m' acc, type_vari aenv x (QT n,l) ->
                @find_state rmax s l (Some (l++l1, Cval m f)) -> ses_len l1 = Some n' ->
                dis_sem n n' m m f nil (m',acc) ->  @up_state rmax s (l++l1) (Cval m' acc) s' ->
                qfor_sem aenv s (Diffuse x) s' *)
  | seq_sem: forall aenv e1 e2 s s1 s2, qfor_sem aenv s e1 s1 -> qfor_sem aenv s1 e2 s2 -> qfor_sem aenv s (PSeq e1 e2) s2
  | for_sem: forall aenv s s' x l h b p, ForallA rmax (@qfor_sem) (h-l) aenv s l x b p s' 
           -> qfor_sem aenv s (For x (Num l) (Num h) b p) s'.

Definition qfor_sem_ind':
     forall (rmax:nat) (P : nat -> aenv -> state -> pexp -> state -> Prop),
       (forall (aenv: aenv) (e:pexp) (W:stack) (s s':qstate) (S:state),
            @state_equiv rmax s s' -> @qfor_sem rmax aenv (W,s') e S -> P rmax aenv (W,s') e S ->
             P rmax aenv (W,s) e S) -> 
       (forall (aenv: aenv) (S:state), P rmax aenv S PSKIP S) -> 
       (forall (aenv: aenv) (s s':state) (x:var) (a:aexp) (n:nat) (e:pexp),
              simp_aexp a = Some n -> @qfor_sem rmax aenv s (subst_pexp e x n) s' -> P rmax aenv s (subst_pexp e x n) s' ->
             P rmax aenv s (Let x (AE a) e) s') -> 
       (forall (aenv: aenv) (s s':state) (x:var) (a:aexp) (n:R * nat) (e:pexp),
             eval_aexp (fst s) a n -> @qfor_sem rmax (AEnv.add x (Mo MT) aenv) (update_cval s x n)  e s' ->
             P rmax (AEnv.add x (Mo MT) aenv) (update_cval s x n) e s' ->
             P rmax aenv s (Let x (AE a) e) s') -> 
       (forall (aenv: aenv) (W:stack) (s :qstate) (s':state) (l:session) (x:var) (a:var) (n:nat) (e:pexp) (r:R) (v:nat) (va va':state_elem),
              AEnv.MapsTo a (QT n) aenv -> @pick_mea n va (r,v) -> build_state_ch n v va = Some va' -> 
           @qfor_sem rmax (AEnv.add x (Mo MT) aenv) (AEnv.add x (r,v) W, (l,va')::s) e s' ->
           P rmax (AEnv.add x (Mo MT) aenv) (AEnv.add x (r,v) W, (l,va')::s) e s'
           -> P rmax aenv (W,((a,BNum 0,BNum n)::l,va)::s) (Let x (Meas a) e) s') -> 

       (forall (aenv: aenv) (W:stack) (s:qstate) (a:session) (e:exp) (l:session) (r:C) (b : rz_val) (ra:C) (ba:rz_val),
              eval_nor rmax aenv a r b e = Some (ra,ba) ->
             P rmax aenv (W,(a++l,Nval r b)::s) (AppU a e) (W,(a++l,Nval ra ba)::s)) ->
       (forall (aenv: aenv) (W:stack) (s:qstate) (a:session) (e:exp) (l:session) (b : nat -> C * rz_val) (m:nat) (ba:nat -> C * rz_val),
              eval_ch rmax aenv a m b e = Some ba ->
             P rmax aenv (W,(a++l,Cval m b)::s) (AppU a e) (W,(a++l,Cval m ba)::s)) ->

       (forall (aenv: aenv) (W:stack) (s:qstate) (p:varia) (a:range) (r:C) (b : rz_val) (n:nat),
              @simp_varia aenv p a -> ses_len ([a]) = Some n ->
             P rmax aenv (W,([a],Nval r b)::s) (AppSU (RH p)) (W,([a],(Hval (eval_to_had n b)) )::s)) ->

       (forall (aenv: aenv) (W:stack) (s:qstate) (p:varia) (a:range) (b : nat -> rz_val) (n:nat),
              @simp_varia aenv p a -> ses_len ([a]) = Some n ->
             P rmax aenv (W,([a],Hval b)::s) (AppSU (RH p)) (W,([a],(Nval C1 (eval_to_nor n b)))::s)) ->
       (forall (aenv: aenv) (s s':state) (b:bexp) (e:pexp),
              simp_bexp b = Some true -> @qfor_sem rmax aenv s e s' -> P rmax aenv s e s' -> P rmax aenv s (If b e) s') ->
       (forall (aenv: aenv) (s:state) (b:bexp) (e:pexp),
              simp_bexp b = Some false -> P rmax aenv s (If b e) s) ->

       (forall (aenv : aenv) (W W' : stack) (l : session)
         (l1 : list range) (n n' : nat)
         (s s' : list (list range * state_elem)) 
         (b : bexp) (e : pexp) (m m' : nat) (f f' : nat -> C * rz_val)
         (fc fc' : state_elem) (fc'' : nat -> C * rz_val)
         (fa : nat * (nat -> C * rz_val)),
        type_bexp aenv b (QT n,l) -> @eval_bexp ((l++l1, Cval m f)::s) b ((l++l1, Cval m f')::s) -> ses_len l1 = Some n' ->
        mut_state 0 n n' (Cval (fst (grab_bool f' m n)) (snd (grab_bool f' m n))) fc ->
        @qfor_sem rmax aenv (W,(l1,fc)::s) e (W',(l1,fc')::s') ->
        P rmax aenv (W,(l1,fc)::s) e (W',(l1,fc')::s') -> mut_state 0 n' n fc' (Cval m' fc'') ->
        assem_bool m m' n f' fc'' fa -> P rmax aenv (W,(l++l1, Cval m f)::s) (If b e) (W',(l++l1, Cval (fst fa) (snd fa))::s')) ->

       (forall (aenv: aenv) (e1 e2:pexp) (s s1 s2:state),
           @qfor_sem rmax aenv s e1 s1 -> P rmax aenv s e1 s1 ->
          @qfor_sem rmax aenv s1 e2 s2 -> P rmax aenv s1 e2 s2 -> P rmax aenv s (PSeq e1 e2) s2) -> 

       (forall (aenv: aenv) (s s':state) (x:var) (l h:nat) (b:bexp) (p:pexp),
          ForallA rmax (@qfor_sem) (h-l) aenv s l x b p s' -> ForallA rmax P (h-l) aenv s l x b p s' ->
          P rmax aenv s (For x (Num l) (Num h) b p) s') ->

       (forall (aenv: aenv) (S:state) (e:pexp) (S':state), @qfor_sem rmax aenv S e S' -> P rmax aenv S e S').
Proof.
  intros rmax P ST1 ST2 ST3 ST4 ST5 ST6 ST7 ST8 ST9 ST10 ST11 ST12 ST13 ST14.
    refine
      (fix PF aenv S e S' (Hw : @qfor_sem rmax aenv S e S') {struct Hw} :=
         match Hw with
         | state_eq_sem aenv e W s s' Sa Hseq Hw => ST1 aenv e W s s' Sa Hseq Hw _
         | skip_sem aenv s => ST2 aenv s
         | let_sem_c aenv s s' x a n e Hev Hw => ST3 aenv s s' x a n e Hev Hw _
         | let_sem_m aenv s s' x a n e Hev Hw => ST4 aenv s s' x a n e Hev Hw _
         | let_sem_q aenv W s s' l x a n e r v va va' Henv Hpick Hbd Hw =>
                 ST5 aenv W s s' l x a n e r v va va' Henv Hpick Hbd Hw _
         | appu_sem_nor aenv W s a e l r b ra ba Hev => ST6 aenv W s a e l r b ra ba Hev
         | appu_sem_ch aenv W s a e l b m ba Hev => ST7 aenv W s a e l b m ba Hev
         | appsu_sem_h_nor aenv W s p a r b n Hsp Hlen => ST8 aenv W s p a r b n Hsp Hlen
         | appsu_sem_h_had aenv W s p a b n Hsp Hlen => ST9 aenv W s p a b n Hsp Hlen
         | if_sem_ct aenv s s' b e Hsp Hw => ST10 aenv s s' b e Hsp Hw _
         | if_sem_cf aenv s b e Hsp => ST11 aenv s b e Hsp
         | if_sem_q aenv W W' l l1 n n' s s' b e m m' f f' fc fc' fc'' fa Hty Hev Hses Hmut1 Hw Hmut2 Has
            => ST12 aenv W W' l l1 n n' s s' b e m m' f f' fc fc' fc'' fa Hty Hev Hses Hmut1 Hw _ Hmut2 Has
         | seq_sem aenv e1 e2 s s1 s2 Hw1 Hw2 => ST13 aenv e1 e2 s s1 s2 Hw1 _ Hw2 _
         | for_sem aenv s s' x l h b p Hw => ST14 aenv s s' x l h b p Hw _
         end).
   exact (PF aenv (W, s') e Sa Hw).
   exact (PF aenv s (subst_pexp e x n) s' Hw).
   exact (PF (AEnv.add x (Mo MT) aenv) (update_cval s x n) e s' Hw).
   exact (PF (AEnv.add x (Mo MT) aenv) (AEnv.add x (r, v) W, (l, va') :: s) e s' Hw).
   exact (PF aenv s e s' Hw).
   exact (PF aenv (W, (l1, fc) :: s) e (W', (l1, fc') :: s') Hw).
   exact (PF aenv s e1 s1 Hw1).
   exact (PF aenv s1 e2 s2 Hw2).
   remember (h-l) as n. clear Heqn.
   induction Hw. constructor.
   apply PF in H. apply ForallA_cons with (s' := s'). easy. easy.
Qed.

Lemma state_equiv_sub: forall rmax l s s', @state_equiv rmax s s' -> 
          sub_qubits l (dom_to_ses (dom s)) -> sub_qubits l (dom_to_ses (dom s')).
Proof.
Admitted.

Lemma state_equiv_dis: forall rmax (s1 s s' : qstate), @state_equiv rmax s s' -> 
          dis_qubits (dom_to_ses (dom s)) (dom_to_ses (dom s1)) 
       -> dis_qubits (dom_to_ses (dom s')) (dom_to_ses (dom s1)).
Proof.
Admitted.

Lemma state_equiv_add: forall rmax (s1 s s' : qstate), @state_equiv rmax s s' -> @state_equiv rmax (s++s1) (s'++s1).
Proof.
Admitted.

Lemma qfor_sem_local: forall rmax env W W' e l s s' s1, 
 fv_pexp env e l -> sub_qubits l (dom_to_ses (dom s)) -> dis_qubits (dom_to_ses (dom s)) (dom_to_ses (dom s1)) ->
    @qfor_sem rmax env (W,s) e (W',s') -> @qfor_sem rmax env (W,s++s1) e (W',s'++s1).
Proof.
  intros. remember (W, s) as Sa. remember (W', s') as Sb.
  generalize dependent s. generalize dependent s'.
  generalize dependent W. generalize dependent W'.
  induction H2 using qfor_sem_ind'; intros; subst.
  inv HeqSa. 
  assert ((W', s'0) = (W', s'0)) by easy.
  apply state_equiv_sub with (rmax:=rmax) (s' := s') in H1; try easy.
  apply state_equiv_dis with (rmax:=rmax) (s' := s') in H3; try easy.
  assert ((W0, s') = (W0, s')) by easy.
  specialize (IHqfor_sem H W' W0 s'0 H4 s' H1 H3 H5).
  apply state_equiv_cong with (S3 := s1) in H0.
  apply state_eq_sem with (f' := (s' ++ s1)); try easy.
  inv HeqSa. constructor.
Admitted.


(*small step semantics. *)
Inductive step {rmax:nat}
           : aenv -> state -> pexp -> state -> pexp -> Prop :=
  | state_eq_step: forall aenv e e' s f f' S, @state_equiv rmax f f' -> step aenv (s,f') e S e' -> step aenv (s,f) e S e'
  | let_step_c : forall aenv s x a n e, simp_aexp a = Some n 
        -> step aenv s (Let x (AE a) e) s (subst_pexp e x n)
  | let_step_m : forall aenv s x a n e, eval_aexp (fst s) a n 
             -> step aenv s (Let x (AE a) e) (update_cval s x n) e
  | let_step_q : forall aenv W s l x a n e r v va va', AEnv.MapsTo a (QT n) aenv ->
                       @pick_mea n va (r,v) -> build_state_ch n v va = Some va' 
                  -> step (AEnv.add x (Mo MT) aenv) (W,((a,BNum 0,BNum n)::l,va)::s) (Let x (Meas a) e) (AEnv.add x (r,v) W, (l,va')::s) e

  | appu_step_nor : forall aenv W s a e l r b ra ba, eval_nor rmax aenv a r b e = Some (ra,ba) 
         -> step aenv (W,(a++l,Nval r b)::s) (AppU a e) (W,(a++l,Nval ra ba)::s) PSKIP

  | appu_step_ch : forall aenv W s a e l b m ba, eval_ch rmax aenv a m b e = Some ba 
           -> step aenv (W,(a++l,Cval m b)::s) (AppU a e) (W,(a++l,Cval m ba)::s) PSKIP

  | appsu_step_h_nor : forall aenv W s p a r b, @simp_varia aenv p a ->
          step aenv (W,([a],Nval r b)::s) (AppSU (RH p)) (W,([a],(Hval (fun i => (update allfalse 0 (b i)))) )::s) PSKIP

  | appsu_step_h_had : forall aenv W s p a b, @simp_varia aenv p a 
                   -> step aenv (W,([a],Hval b)::s) (AppSU (RH p)) (W,([a],(Nval C1 (fun j => b j 0)))::s) PSKIP
  (* rewrite the tenv type for oqasm with respect to the ch list type. *)

  | seq_step_1: forall aenv e1 e1' e2 s s1 s2, e1 <> PSKIP -> step aenv s e1 s1 e1' -> step aenv s (PSeq e1 e2) s2 (PSeq e1' e2)
  | seq_step_2: forall aenv e2 s, step aenv s (PSeq PSKIP e2) s e2
  | if_step_ct : forall aenv s s' b e e', simp_bexp b = Some true -> step aenv s e s' e' -> step aenv s (If b e) s (If b e')
  | if_step_cf : forall aenv s b e, simp_bexp b = Some false -> step aenv s (If b e) s PSKIP
  | if_step_mt : forall aenv M s s' b e e', eval_cbexp M b true -> step aenv (M,s) (If b e) s' e' -> step aenv (M,s) (If b e) s' (If b e')
  | if_step_mf : forall aenv M s b e, eval_cbexp M b false -> step aenv (M,s) (If b e) (M,s) PSKIP
  | if_step_q : forall aenv s b, step aenv s (If b PSKIP) s PSKIP
  | for_step_0 : forall aenv s x l h b p, h <= l -> step aenv s (For x (Num l) (Num h) b p) s PSKIP
  | for_step_s : forall aenv s x l h b p, l < h -> 
          step aenv s (For x (Num l) (Num h) b p) s (PSeq (If b p) (For x (Num (l+1)) (Num h) b p))
 (* | diffuse_step_a: forall aenv s s' x n l n' l1 m f m' acc, type_vari aenv x (QT n,l) ->
                @find_state rmax s l (Some (l++l1, Cval m f)) -> ses_len l1 = Some n' ->
                dis_sem n n' m m f nil (m',acc) ->  @up_state rmax s (l++l1) (Cval m' acc) s' ->
                step aenv s (Diffuse x) s' PSKIP
  *).


(*

Inductive session_system {rmax:nat}
           : atype -> aenv -> type_map -> pexp -> type_map -> Prop :=

Inductive qfor_sem {rmax:nat}
           : aenv -> state -> pexp -> state -> Prop :=

*)

