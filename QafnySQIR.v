Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates NDSem UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import OQASM.
Require Import CLArith.
Require Import RZArith.
Require Import QWhileSyntax.
Require Import SessionDef.
Require Import SessionSem.
Require Import SessionKind.
Require Import SessionType.
Require Import SessionTypeProof.
Require Import OQASMProof.
(**********************)
(** Session Definitions **)
(**********************)

From Coq Require Recdef.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Local Open Scope nat_scope.
Local Open Scope com_scope.

(*
Check OQASMProof.vars.

(avs: nat -> posi)
*)
Check SQIR.seq.
Locate meas.

Definition measure' {dim} n : base_com dim := (meas n skip skip).
(* avs is to support the compilation of OQASM, it is id with f. *)
Fixpoint trans_n_meas {dim} (n:nat) (p:nat) : base_com dim :=
  match n with 0 => SQIR.ID (p) | S m => measure' (p+m);trans_n_meas m p end.

Fixpoint nX (f : vars) (dim:nat) (x:var) (n:nat) : base_ucom dim :=
     match n with 0 => SQIR.ID (find_pos f (x,0))
               | S m => SQIR.useq (nX f dim x m) (SQIR.X (find_pos f (x,m))) 
     end.

Fixpoint controlled_x_gen (f : vars) (dim:nat) (x:var) (n : nat) (size:nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.X (find_pos f (x,size-1))
  | S m  => control (find_pos f (x,size - n)) (controlled_x_gen f dim x m size)
  end.

Definition diff (f : vars) (dim:nat) (x:var) (n : nat) : base_com dim := 
  nH f dim x n 0 ; nX f dim x n; 
   SQIR.H (find_pos f (x,n-1)); controlled_x_gen f dim x n n ; nX f dim x n; nH f dim x n 0.


(* M - x *)
Definition rz_sub_anti (x:var) (n:nat) (M:nat -> bool) := OQASM.Seq (negator0 n x) (rz_adder x n M).

(* M <? x *)
Definition rz_compare_anti (x:var) (n:nat) (c:posi) (M:nat) := 
 OQASM.Seq (rz_compare_half x n c M) (inv_exp ( OQASM.Seq (rz_sub_anti x n (nat2fb M)) (OQASM.RQFT x n))).

Definition rz_eq_circuit (x:var) (n:nat) (c:posi) (M:nat) :=
   OQASM.Seq (OQASM.Seq (OQASM.X c) (rz_compare_anti x n c M)) (OQASM.Seq (OQASM.X c) (rz_compare x n c M)).

Definition rz_lt_circuit (x:var) (n:nat) (c:posi) (M:nat) := rz_compare x n c M.

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.


  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
      | nil => x :: nil
      | h :: ls' =>
        if le x h
          then x :: ls
          else h :: insert x ls'
    end.


  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
      | nil => ls2
      | h :: ls' => insert h (merge ls' ls2)
    end.

End mergeSort.
            
            (*Defining trans_pexp using induction relation *)
            
Inductive trans_pexp_rel (dim:nat) : OQASMProof.vars -> pexp -> (nat -> posi) -> option (base_com dim) -> Prop :=
  | trans_pexp_skip : forall f avs,
      trans_pexp_rel dim f PSKIP avs (Some skip)
  | trans_pexp_let_num : forall f x a n s avs e',
      simp_aexp a = Some n ->
      trans_pexp_rel dim f (subst_pexp s x n) avs (Some e') ->
      trans_pexp_rel dim f (Let x (AE a) s) avs (Some e')
  | trans_pexp_let_mnum : forall f x r n s avs,
      trans_pexp_rel dim f s avs None ->
      trans_pexp_rel dim f (Let x (AE (MNum r n)) s) avs None

  | trans_pexp_let_meas : forall f x y s avs cr,
      trans_pexp_rel dim f s avs (Some cr) ->
      trans_pexp_rel dim f (Let x (Meas y) s) avs (Some (trans_n_meas (vsize f y) (start f y) ; cr))
  | trans_pexp_appsu_index : forall f avs x i,
      trans_pexp_rel dim f (AppSU (RH (Index x (Num i)))) avs (Some (from_ucom (SQIR.H (find_pos f (x,i)))))
  
  | trans_pexp_appsu_rh_ba : forall f x avs,
      trans_pexp_rel dim f (AppSU (RH (AExp (BA x)))) avs (Some (from_ucom (nH f dim x (vsize f x) 0)))
  
  | trans_pexp_appsu_sqft : forall f x avs,
      trans_pexp_rel dim f (AppSU (SQFT x)) avs (Some (from_ucom (trans_qft f dim x (vsize f x))))
  | trans_pexp_appsu_srqft : forall f x avs,
      trans_pexp_rel dim f (AppSU (SRQFT x)) avs (Some (from_ucom (trans_rqft f dim x (vsize f x))))
  | trans_pexp_appu : forall f l e avs e',
      compile_exp_to_oqasm e = Some e' ->
      trans_pexp_rel dim f (AppU l e) avs (Some (from_ucom (fst (fst (trans_exp f dim e' avs)))))
  | trans_pexp_pseq : forall f e1 e2 avs e1' e2',
      trans_pexp_rel dim f e1 avs (Some e1') ->
      trans_pexp_rel dim f e2 avs (Some e2') ->
      trans_pexp_rel dim f (PSeq e1 e2) avs (Some (e1' ; e2'))
  | trans_pexp_if_beq : forall f x y v n s avs s',
      trans_pexp_rel dim f s avs (Some s') ->
      trans_pexp_rel dim f (If (BEq (AExp (BA x)) (AExp (Num n)) y (Num v)) s)
              avs (Some ((fst (fst (trans_exp f dim (rz_eq_circuit x (vsize f x) (y, v) n) avs))) ; s'))
  | trans_pexp_if_blt : forall f x y v n s avs s',
      trans_pexp_rel dim f s avs (Some s') ->
      trans_pexp_rel dim f (If (BLt (AExp (BA x)) (AExp (Num n)) y (Num v)) s)
            avs (Some (((fst (fst (trans_exp f dim (rz_eq_circuit x (vsize f x) (y, v) n) avs)))); s'))
   
  | trans_pexp_if_btest : forall f x v s avs s' ce,
      trans_pexp_rel dim f s avs (Some (uc s')) ->
      Some (from_ucom (UnitaryOps.control (find_pos f (x, v)) s')) = ce ->
            trans_pexp_rel dim f (If (BTest x (Num v)) s) avs ce.
  | trans_pexp_rel_Default : forall f dim e s avs,
            (* Need to Define default case for remaining others
              Trans_pexp_rel f dim e s avs None   * ) . 

Function trans_pexp (f:OQASMProof.vars) (dim:nat) (e:pexp) (avs: nat -> posi) {struct e}: (option (base_com dim)) :=
  match e with PSKIP => Some skip
             | Let x (AE (Num n)) s => trans_pexp f dim (subst_pexp s x n) avs
             | Let x (AE (MNum r n)) s => trans_pexp f dim s avs
             | Let x (Meas y) s => match trans_pexp f dim s avs with None => None
                                    | Some cr => Some (trans_n_meas (vsize f y) (start f y) ; cr)
                                   end
             |AppSU (RH (Index x (Num i))) => Some (from_ucom (SQIR.H (find_pos f (x,i))))
             |AppSU (RH (AExp (BA x))) => Some (from_ucom (nH f dim x (vsize f x) 0))
             |AppSU (SQFT x) => Some (from_ucom (trans_qft f dim x (vsize f x)))
             |AppSU (SRQFT x) => Some (from_ucom (trans_rqft f dim x (vsize f x)))

             |AppU l e => match compile_exp_to_oqasm e
                            with None => None
                               | Some e' => match trans_exp f dim e' avs with (ce,_,_) => Some (from_ucom ce) end
                            end
             | PSeq e1 e2 => match trans_pexp f dim e1 avs with None => None
                                | Some e1' =>
                              match trans_pexp f dim e2 avs with None => None
                                 | Some e2' => Some (e1' ; e2')
                              end
                            end
           (*  | Diffuse (AExp (BA x)) => Some (diff f dim x (vsize f x)) *)

             | If (BEq (AExp (BA x)) (AExp (Num n)) y (Num v)) s => 
                   match trans_pexp f dim s avs with None => None
                      | Some e' =>
                    match trans_exp f dim (rz_eq_circuit x (vsize f x) (y,v) n) avs with (ce,_,_)
                             => Some (ce;e') 
                    end
                  end
             | If (BLt (AExp (BA x)) (AExp (Num n)) y (Num v)) s => 
                   match trans_pexp f dim s avs with None => None
                      | Some e' =>
                    match trans_exp f dim (rz_lt_circuit x (vsize f x) (y,v) n) avs with (ce,_,_)
                             => Some (ce;e') 
                    end
                  end

             | If (BTest x (Num v)) s => 
                   match trans_pexp f dim s avs with 
                      | Some (uc e') => Some (from_ucom (UnitaryOps.control (find_pos f (x,v)) e'))
                      | _ => None
                  end

       | _ => None
  end.


(*
Inductive state_elem :=
                 | Nval (p:C) (r:rz_val)
                 | Hval (b:nat -> rz_val)
                 | Cval (m:nat) (b : nat -> C * rz_val).

Definition qstate := list (session * state_elem).

Definition compile_val (v:val) (r_max : nat) : Vector 2 := 
   match v with nval b r => Cexp (2*PI * (turn_angle r r_max)) .* ∣ Nat.b2n b ⟩
            (* | hval b1 b2 r => RtoC(/ √ 2) * Cexp (2*PI * (turn_angle r r_max)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩) *)
             | qval q r => RtoC(/ √ 2) * Cexp (2*PI * (turn_angle q r_max)) .* (∣0⟩ .+ (Cexp (2*PI * (turn_angle r r_max))) .* ∣1⟩)
  end.

Lemma WF_compile_val : forall v r, WF_Matrix (compile_val v r).
Proof.
  intros. unfold compile_val.
  destruct v;auto with wf_db.
Qed.

Hint Resolve WF_compile_val : wf_db.

(*example *)
Definition trans_state (avs : nat -> posi) (rmax : nat) (f : posi -> val) : (nat -> Vector 2) :=
        fun i => compile_val (f (avs i)) rmax.

function: posi -> nat
                 | Nval (p:C) (r:rz_val)
                 | Hval (b:nat -> rz_val)
                 | Cval (m:nat) (b : nat -> C * rz_val).
*)

Check vsum.

Check find_pos.

Check allfalse.


(* n is the length, f is the mapping from posi to nat, s is a session, v is the virtual vector. *)
Check fold_left.

Fixpoint perm_range (f:OQASMProof.vars) (v:rz_val) (x:var) (i:nat) (j:nat)  (n:nat) (acc:rz_val) :=
   match n with 0 => acc
              | S m => update (perm_range f v x i j m acc) (find_pos f (x,i+m)) (v (j+m))
   end.

Fixpoint perm_vector (f:OQASMProof.vars) (s:session) (v:rz_val) (j:nat) := 
  match s with [] => Some allfalse
             | (x,BNum l, BNum r)::ne =>
          if l <=? r then
              (match perm_vector f ne v (j+(r-l))
                   with None => None
                      | Some acc => Some (perm_range f v x l j (r-l) acc)
               end)
          else None
             | _ => None
  end.



Fixpoint gen_qfun {d} (f:OQASMProof.vars) (s:session) (size:nat) (m:nat) (b : nat -> C * rz_val)
   : option (nat -> Vector d) :=
   match m with 0 => Some (fun q => Zero)
              | S ma => match perm_vector f s (snd (b ma)) 0
                            with None => None
                               | Some acc =>
                         match gen_qfun f s size ma b
                              with None => None
                               | Some new_f =>
                Some (update new_f ma ((fst (b ma)).* (@basis_vector d (a_nat2fb acc size))))
                         end
                        end
   end.

Definition trans_qstate (f:OQASMProof.vars) (s:qstate) :=
    match s with (sa,Cval m b)::nil =>
      match ses_len sa with None => None
                            | Some na => 
           match @gen_qfun (2^na) f sa na m b
              with None => None
                 | Some acc => Some (@vsum (2^na) m acc)
           end
      end
              | _ => None
   end.

Definition trans_state_qafny (f:OQASMProof.vars) (s:state) :=
  match s with (sa,q) => match trans_qstate f q 
       with None => None
          | Some acc => Some (sa,acc)
      end
  end.


Lemma trans_pexp_sem :
  forall dim e e' s s' t sa sa' tenv (tenv' : type_map) (aenv : aenv) rmax vs (avs : nat -> posi),
    (*vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    exp_WF (size_env vs) e ->
    at_match (size_env vs) tenv ->
    exp_com_WF vs dim ->
    exp_com_gt vs avs dim ->
    well_typed_oexp (size_env vs) tenv e tenv' ->
    right_mode_env (size_env vs) tenv f ->
    avs_prop vs avs dim -> 
    exp_rmax (size_env vs) rmax e ->
    qft_uniform (size_env vs) tenv f ->
    qft_gt (size_env vs) tenv f ->*)
    dim > 0 ->
    @session_system rmax t aenv tenv e tenv' ->
    @qfor_sem rmax aenv s e s' ->
    trans_pexp vs dim e avs = Some e' ->
    trans_state_qafny vs s' = Some sa' ->
    trans_state_qafny vs s = Some sa ->
    @nd_eval dim e' (snd sa) (snd sa').
Proof.
intros. generalize dependent tenv. generalize dependent tenv'. 
   induction H1 using qfor_sem_ind';
    intros; subst; simpl in *.
- rewrite H3 in H4. inv H4. inv H2. apply nd_skip.
- inv H5. rewrite H0 in *. inv H14. destruct a; simpl in *; try easy. inv H0.
  eapply IHqfor_sem; try easy. admit. apply H15. apply type_aexp_mo_no_simp in H12.
  rewrite H0 in H12. inv H12.
- inv H5. apply simp_aexp_no_eval in H0. rewrite H0 in H14. inv H14.
  destruct a; simpl in *; try easy. eapply IHqfor_sem; try easy. unfold trans_state_qafny in *.
  destruct (trans_qstate vs s'); try easy. admit. unfold trans_state_qafny in *. destruct s in *; simpl in *. admit. apply H15.
- admit.
- inv H3.
- admit.
- inv H3.
- inv H3.
- destruct b in *; simpl in *; try easy.
- destruct b in *; simpl in *; try easy.
- admit.
- admit. 
- inv H2.
Admitted.

 
