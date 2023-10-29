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
Require Import OQASM.
Require Import OQASMProof.
Require Import CLArith.
Require Import RZArith.
Require Import QWhileSyntax.
Require Import SessionDef.
Require Import SessionSem.
(**********************)
(** Session Definitions **)
(**********************)

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

Fixpoint trans_pexp (f:OQASMProof.vars) (dim:nat) (e:pexp) (avs: nat -> posi) : (option (base_com dim)) :=
  match e with PSKIP => Some skip
             | Let x (AE (Num n)) s => trans_pexp f dim s avs
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
             | Diffuse (AExp (BA x)) => Some (diff f dim x (vsize f x))

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
                      | Some (uc e') => Some (from_ucom (control (find_pos f (x,v)) e'))
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


(*
Lemma trans_pexp_sem :
  forall dim e f tenv tenv' rmax vs (avs : nat -> posi),
    vars_start_diff vs ->
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
    qft_gt (size_env vs) tenv f ->
    dim > 0 ->
    (uc_eval (fst (fst (trans_pexp vs dim e avs)))) × (vkron dim (trans_qstate avs rmax f)) 
                =  vkron dim (trans_qstate (snd (trans_pexp vs dim e avs)) rmax (qfor_sem (size_env vs) e f)).
Proof.

*)

