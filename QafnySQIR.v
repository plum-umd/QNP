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
Require Import QafnySyntax.
Require Import LocusDef.
Require Import LocusKind.
Require Import LocusSem.
Require Import LocusType.
Require Import LocusTypeProof.
Require Import OQASMProof.
(**********************)
(** Locus Definitions **)
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



