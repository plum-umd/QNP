Require Import UnitaryOps.

(** TODO: replace SQIR's ucom type with the ucom type defined below **)

(* Experimenting with a version of ucom that uses a list argument and no 
   dependent dim type *)
Inductive ucom (U : nat -> Set) : Set :=
| useq :  ucom U -> ucom U -> ucom U
| uapp : forall n, U n -> list nat -> ucom U.
Arguments useq {U}.
Arguments uapp {U n}.
Notation "u1 >> u2" := (useq u1 u2) (at level 50). 
(* >> because ; is already used in the ucom scope *)

Inductive well_formed {U} : ucom U -> Prop :=
  | WF_useq : forall u1 u2, well_formed u1 -> well_formed u2 -> well_formed (u1 >> u2)
  | WF_uapp : forall n (g : U n) qs, length qs = n -> well_formed (uapp g qs).

(* RNR: Next three lemmas aren't needed but replace old 
   lemmas and could possibly be useful *)
Lemma uapp_WF_length : forall {U : nat -> Set} (n : nat) (g : U n) qs,
  well_formed (uapp g qs) -> length qs = n.
Proof.
  intros.
  inversion H; subst; easy.
Qed.

Lemma destruct_list_S : forall {A} (l : list A) (n : nat),
    length l = S n ->
    exists x l', length l' = n /\ l = x :: l'.
Proof.
  intros A l.
  induction l; intros.
  - discriminate.
  - eauto.
Qed.

Lemma destruct_list_0 : forall {A} (l : list A),
    length l = O ->
    l = nil.
Proof. destruct l; easy. Qed.

Ltac simpl_WF :=
  repeat match goal with
  | [H : well_formed _ |- _] => apply uapp_WF_length in H
  | [H : length ?l = ?n |- _] => destruct l; inversion H; clear H
  end.

Ltac simpl_WF_alt :=
  repeat match goal with
  | [H : well_formed _ |- _] => apply uapp_WF_length in H
  | [H : length ?l = S ?n |- _] => apply destruct_list_S in H as [? [? [? ?]]]; subst
  | [H : length ?l = O |- _] => apply destruct_list_0 in H; subst
  end.

(** More general gate set **)

Inductive U : nat -> Set :=
  | U_X : U 1
  | U_H : U 1
  | U_U1 : R -> U 1
  | U_U2 : R -> R -> U 1 
  | U_U3 : R -> R -> R -> U 1
  | U_CX : U 2
  | U_CU1 : R -> U 2
  | U_CH : U 2
  | U_SWAP : U 2
  | U_CCX : U 3
  | U_CCU1 : R -> U 3
  | U_CSWAP : U 3
  | U_C3X : U 4.

Fixpoint to_base_ucom dim (u : ucom U) : base_ucom dim :=
  match u with
  | u1 >> u2 => (to_base_ucom dim u1 ; to_base_ucom dim u2)%ucom
  | uapp g qs => 
      match g, qs with
      | U_X, (q1 :: List.nil)%list => SQIR.X q1
      | U_H, (q1 :: List.nil) => H q1
      | U_U1 r1, (q1 :: List.nil) => U1 r1 q1
      | U_U2 r1 r2, (q1 :: List.nil) => U2 r1 r2 q1
      | U_U3 r1 r2 r3, (q1 :: List.nil) => U3 r1 r2 r3 q1
      | U_CX, (q1 :: q2 :: List.nil) => CNOT q1 q2
      | U_CU1 r, (q1 :: q2 :: List.nil) => UnitaryOps.control q1 (U1 r q2)
      | U_CH, (q1 :: q2 :: List.nil) => UnitaryOps.control q1 (H q2)
      | U_SWAP, (q1 :: q2 :: List.nil) => SWAP q1 q2
      | U_CCX, (q1 :: q2 :: q3 :: List.nil) => UnitaryOps.control q1 (CNOT q2 q3)
      | U_CCU1 r, (q1 :: q2 :: q3 :: List.nil) => 
          UnitaryOps.control q1 (UnitaryOps.control q2 (U1 r q3))
      | U_CSWAP, (q1 :: q2 :: q3 :: List.nil) => UnitaryOps.control q1 (SWAP q2 q3)
      | U_C3X, (q1 :: q2 :: q3 :: q4 :: List.nil) => 
          UnitaryOps.control q1 (UnitaryOps.control q2 (CNOT q3 q4))
      (* dummy value - unreachable for well-formed progs *)
      | _, _ => SKIP
      end
  end.

Definition uc_eval dim (u : ucom U) := uc_eval (to_base_ucom dim u).

Lemma change_dim : forall u m n,
  uc_eval m u = UnitarySem.uc_eval (cast (to_base_ucom n u) m).
Proof.
  intros u m n.
  unfold uc_eval.
  induction u; simpl.
  rewrite IHu1, IHu2.
  reflexivity.
  destruct u; repeat (destruct l; try reflexivity).
Qed.

Ltac invert_WT :=
  repeat match goal with
  | H : uc_well_typed (UnitaryOps.control _ _)%ucom |- _ => idtac
  | H : uc_well_typed _ |- _ => inversion H; clear H; subst
  end.

Local Transparent SQIR.ID SQIR.X SQIR.H SQIR.Rz SQIR.CNOT SQIR.SWAP.
Local Opaque UnitaryOps.control.
Lemma change_dim_WT : forall (u : ucom U) (m n : nat),
  (m <= n)%nat -> 
  well_formed u ->
  uc_well_typed (to_base_ucom m u) ->
  uc_well_typed (to_base_ucom n u).
Proof.
  intros u m n Hmn WF WT.
  induction u.
  inversion WT; subst.
  inversion WF; subst.
  constructor; auto.
  destruct u; simpl in *; simpl_WF; invert_WT.
  (* U_X, U_H, U_U1, U_U2, U_U3, U_CX, U_SWAP, & SKIP cases *) 
  all: repeat constructor; try lia.
  (* U_CU1 *)
  apply uc_well_typed_control in WT as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try constructor; lia.
  (* U_CH *)
  apply uc_well_typed_control in WT as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try constructor; lia.
  (* U_CCX *)
  apply uc_well_typed_control in WT as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try constructor; lia.
  (* U_CCU1 *)
  apply uc_well_typed_control in WT as [? [? ?]].
  apply fresh_control in H0 as [? ?].
  apply uc_well_typed_control in H1 as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try lia.
  apply fresh_control; split; try constructor; lia.
  apply uc_well_typed_control; repeat split; try constructor; lia.
  (* U_CSWAP *)
  apply uc_well_typed_control in WT as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; repeat constructor; lia.
  (* U_C3X *)
  apply uc_well_typed_control in WT as [? [? ?]].
  apply fresh_control in H0 as [? ?].
  apply uc_well_typed_control in H1 as [? [? ?]].
  invert_WT; invert_is_fresh.
  apply uc_well_typed_control.
  repeat split; try lia.
  apply fresh_control; split; try constructor; lia.
  apply uc_well_typed_control; repeat split; try constructor; lia.
Qed.
Local Transparent UnitaryOps.control.
Local Opaque SQIR.ID SQIR.X SQIR.H SQIR.Rz SQIR.U1 SQIR.U2 SQIR.U3 SQIR.CNOT SQIR.SWAP.

(* Defining constants separately for easier extraction. *)
Definition R2 : R := 2.
Definition R4 : R := 4.
Definition R8 : R := 8.

Definition X q := uapp U_X [q].
Definition H q := uapp U_H [q].
Definition U1 r1 q := uapp (U_U1 r1) [q].
Definition U2 r1 r2 q := uapp (U_U2 r1 r2) [q].
Definition U3 r1 r2 r3 q := uapp (U_U3 r1 r2 r3) [q].
Definition T q := U1 (PI / R4) q.
Definition Tdg q := U1 (- (PI / R4)) q.
Definition ID q := U1 R0 q.
Definition SKIP := ID O. (* used as a dummy value *)
Definition P8 q := U1 (PI / R8) q.
Definition P8dg q := U1 (- (PI / R8)) q.
Definition CX q1 q2 := uapp U_CX (q1 :: q2 :: List.nil).
Definition CU1 r q1 q2 := uapp (U_CU1 r) (q1 :: q2 :: List.nil).
Definition CH q1 q2 := uapp U_CH (q1 :: q2 :: List.nil).
Definition SWAP q1 q2 := uapp U_SWAP (q1 :: q2 :: List.nil).
Definition CCX q1 q2 q3 := uapp U_CCX (q1 :: q2 :: q3 :: List.nil).
Definition CCU1 r q1 q2 q3 := uapp (U_CCU1 r) (q1 :: q2 :: q3 :: List.nil).
Definition CSWAP q1 q2 q3 := uapp U_CSWAP (q1 :: q2 :: q3 :: List.nil).
Definition C3X q1 q2 q3 q4 := uapp U_C3X (q1 :: q2 :: q3 :: q4 :: List.nil).

Definition decompose_CH (a b : nat) : ucom U := 
  U3 (PI/R4) R0 R0 b >> CX a b >> U3 (- (PI/R4)) R0 R0 b. 

Definition decompose_CU1 r1 (a b : nat) : ucom U := 
  U1 (r1/R2) a >> U1 (r1/R2) b >> CX a b >> U1 (- (r1/R2)) b >> CX a b.

Definition decompose_CU2 r1 r2 (a b : nat) : ucom U := 
  U1 ((r2+r1)/R2) a >> U1 ((r2-r1)/R2) b >> CX a b >>
  U3 (-(PI/R4)) R0 (-(r1+r2)/R2) b >> CX a b >> U3 (PI/R4) r1 R0 b.

Definition decompose_CU3 r1 r2 r3 (a b : nat) : ucom U := 
  U1 ((r3+r2)/R2) a >> U1 ((r3-r2)/R2) b >> CX a b >>
  U3 (-(r1/R2)) R0 (-(r2+r3)/R2) b >> CX a b >> U3 (r1/R2) r2 R0 b.

Definition decompose_CCU1 r1 (a b c : nat) : ucom U := 
  CU1 (r1/R2) a b >> CX b c >> CU1 (-r1/R2) a c >> CX b c >> CU1 (r1/R2) a c.

Definition decompose_CSWAP (a b c : nat) : ucom U := 
  CCX a b c >> CCX a c b >> CCX a b c.

Definition decompose_CCX (a b c : nat) : ucom U := 
  H c >> CX b c >> Tdg c >> CX a c >> 
  T c >> CX b c >> Tdg c >> CX a c >> 
  CX a b >> Tdg b >> CX a b >>
  T a >> T b >> T c >> H c.

(* Based on https://qiskit.org/documentation/_modules/qiskit/circuit/library/standard_gates/x.html#C3XGate *)
Definition decompose_C3X (a b c d : nat) : ucom U := 
  H d >> P8 a >> P8 b >> P8 c >> P8 d >>
  CX a b >> P8dg b >> CX a b >> CX b c >> P8dg c >> 
  CX a c >> P8 c >> CX b c >> P8dg c >> CX a c >> 
  CX c d >> P8dg d >> CX b d >> P8 d >> CX c d >> 
  P8dg d >> CX a d >> P8 d >> CX c d >> P8dg d >> 
  CX b d >> P8 d >> CX c d >> P8dg d >> CX a d >> H d.

Fixpoint control' a (c : ucom U) (n : nat) : ucom U :=
  match n with 
  | O => SKIP (* unreachable with "fuel" below *)
  | S n' => 
      match c with
      | c1 >> c2 => control' a c1 n' >> control' a c2 n'
      | uapp U_X (b :: List.nil) => CX a b
      | uapp U_H (b :: List.nil) => CH a b
      | uapp (U_U1 r) (b :: List.nil) => CU1 r a b
      | uapp U_CX (b :: c :: List.nil) => CCX a b c
      | uapp (U_CU1 r) (b :: c :: List.nil) => CCU1 r a b c
      | uapp U_CCX (b :: c :: d :: List.nil) => C3X a b c d
      | uapp U_SWAP (b :: c :: List.nil) => CSWAP a b c
      (* We don't support CU2, CU3, CCH, C3U1, CCSWAP or C4X, so decompose *)
      | uapp (U_U2 r1 r2) (b :: List.nil) => decompose_CU2 r1 r2 a b
      | uapp (U_U3 r1 r2 r3) (b :: List.nil) => decompose_CU3 r1 r2 r3 a b
      | uapp U_CH (b :: c :: List.nil) => control' a (decompose_CH b c) n'
      | uapp (U_CCU1 r) (b :: c :: d :: List.nil) => control' a (decompose_CCU1 r b c d) n'
      | uapp U_CSWAP (b :: c :: d :: List.nil) => control' a (decompose_CSWAP b c d) n'
      | uapp U_C3X (b :: c :: d :: e :: List.nil) => control' a (decompose_C3X b c d e) n'
      | _ => SKIP (* unreachable *)
      end
  end.

(* Fuel for control'. This may return a larger number than necessary (meaning that
   control' will return before consuming all its fuel), but this will always
   provide enough fuel to complete the computation (see how "fuel" is used in 
   control'_correct. *)
Definition fuel_CH : nat := 2.
Definition fuel_CCU1 : nat := 4.
Definition fuel_CSWAP : nat := 2.
Definition fuel_C3X : nat := 30.
Fixpoint fuel (c : ucom U) :=
  match c with
  | c1 >> c2 => S (max (fuel c1) (fuel c2))
  | uapp U_CH _ => S fuel_CH
  | uapp (U_CCU1 r) _ => S fuel_CCU1
  | uapp U_CSWAP _ => S fuel_CSWAP
  | uapp U_C3X _ => S fuel_C3X
  | _ => O
  end.
Definition control a (c : ucom U) :=
  control' a c (S (fuel c)).

Lemma fuel_CH_eq : forall a b, fuel (decompose_CH a b) = fuel_CH.
Proof. intros. reflexivity. Qed.
Lemma fuel_CCU1_eq : forall r a b c, fuel (decompose_CCU1 r a b c) = fuel_CCU1.
Proof. intros. reflexivity. Qed.
Lemma fuel_CSWAP_eq : forall a b c, fuel (decompose_CSWAP a b c) = fuel_CSWAP.
Proof. intros. reflexivity. Qed.
Lemma fuel_C3X_eq : forall a b c d, fuel (decompose_C3X a b c d) = fuel_C3X.
Proof. intros. reflexivity. Qed.

Hint Rewrite <- RtoC_minus : RtoC_db.

Local Transparent SQIR.H SQIR.U3.
Lemma decompose_CH_is_control_H : forall dim a b,
  uc_eval dim (decompose_CH a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.H b)).
Proof.
  assert (aux1 : rotation (- (PI / 4)) 0 0 × (σx × rotation (PI / 4) 0 0) =
                 Cexp (PI / 2) .* (rotation (PI / 2 / 2) 0 0 ×
                   (σx × (rotation (- (PI / 2) / 2) 0 (- PI / 2) × 
                     (σx × phase_shift (PI / 2)))))).
  { (* messy :) should make better automation -KH *)
    solve_matrix; repeat rewrite RIneq.Ropp_div; autorewrite with Cexp_db trig_db; 
      repeat rewrite RtoC_opp; field_simplify_eq; try nonzero.
    replace (((R1 + R1)%R, (R0 + R0)%R) * cos (PI / 4 / 2) * sin (PI / 4 / 2)) 
      with (2 * sin (PI / 4 / 2) * cos (PI / 4 / 2)) by lca.
    2: replace (((- (R1 + R1))%R, (- (R0 + R0))%R) * Ci * Ci * 
                  cos (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2))
         with (2 * sin (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2)) by lca.
    3: replace (- sin (PI / 4 / 2) * sin (PI / 4 / 2) + 
                  cos (PI / 4 / 2) * cos (PI / 4 / 2)) 
         with (cos (PI / 4 / 2) * cos (PI / 4 / 2) - 
                 sin (PI / 4 / 2) * sin (PI / 4 / 2)) by lca.
    3: replace ((R1 + R1)%R, (R0 + R0)%R) with (RtoC 2) by lca.
    4: replace (((- (R1 + R1))%R, (- (R0 + R0))%R) * sin (PI / 4 / 2) * 
                  cos (PI / 4 / 2)) 
         with (- (2 * sin (PI / 4 / 2) * cos (PI / 4 / 2))) by lca.
    4: replace (- Ci * Ci * sin (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2) + 
                  Ci * Ci * cos (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2))
         with (- (cos (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2) - 
                 sin (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2))) by lca.
    all: autorewrite with RtoC_db; rewrite <- sin_2a; rewrite <- cos_2a;
         replace (2 * (PI / 4 / 2))%R with (PI / 4)%R by lra;
         replace (2 * (PI / 2 / 2 / 2))%R with (PI / 4)%R by lra;
         autorewrite with trig_db; reflexivity. }
  assert (aux2 : rotation (- (PI / 4)) 0 0 × rotation (PI / 4) 0 0 =
                 rotation (PI / 2 / 2) 0 0 × 
                   (rotation (- (PI / 2) / 2) 0 (- PI / 2) × phase_shift (PI / 2))).
  { assert (aux: forall x, (x * x = x²)%R) by (unfold Rsqr; reflexivity).
    solve_matrix; repeat rewrite RIneq.Ropp_div; autorewrite with Cexp_db trig_db; 
      repeat rewrite RtoC_opp; field_simplify_eq; try nonzero; 
      autorewrite with RtoC_db; repeat rewrite aux.
    rewrite 2 (Rplus_comm ((cos _)²)).
    rewrite 2 sin2_cos2.
    reflexivity.
    rewrite 2 sin2_cos2.
    reflexivity. }
  intros dim a b.
  unfold SQIR.H, decompose_CH, uc_eval.
  simpl.
  autorewrite with eval_db.
  gridify; trivial; autorewrite with ket_db. (* slow! *)
  - rewrite Rminus_0_r, Rplus_0_l, Rplus_0_r.
    apply f_equal2.
    + rewrite <- Mscale_kron_dist_l.
      rewrite <- Mscale_kron_dist_r.
      do 2 (apply f_equal2; try reflexivity).
      apply aux1.
    + unfold R4. 
      replace R0 with 0 by reflexivity.
      rewrite aux2.
      reflexivity.
  - rewrite Rminus_0_r, Rplus_0_l, Rplus_0_r.
    apply f_equal2.
    + rewrite <- 3 Mscale_kron_dist_l.
      rewrite <- Mscale_kron_dist_r.
      do 4 (apply f_equal2; try reflexivity).
      apply aux1.
    + unfold R4.
      replace R0 with 0 by reflexivity.
      rewrite aux2.
      reflexivity.
Qed.
Local Opaque SQIR.H SQIR.U3.

Local Transparent SQIR.Rz SQIR.U1.
Lemma decompose_CU1_is_control_U1 : forall dim r a b,
  uc_eval dim (decompose_CU1 r a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.U1 r b)).
Proof.
  intros dim r a b.
  unfold SQIR.U1, decompose_CU1, uc_eval.
  simpl.
  autorewrite with R_db.
  repeat rewrite phase_shift_rotation.
  rewrite phase_0.
  bdestruct (b <? dim).
  replace (pad b dim (I 2)) with (I (2 ^ dim)).
  Msimpl. reflexivity.
  unfold pad.
  gridify. reflexivity.
  autorewrite with eval_db.
  gridify.
Qed.
Local Opaque SQIR.Rz SQIR.U1.

Local Transparent SQIR.U2.
Lemma decompose_CU2_is_control_U2 : forall dim r1 r2 a b,
  uc_eval dim (decompose_CU2 r1 r2 a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.U2 r1 r2 b)).
Proof.
  intros dim r1 r2 a b.
  unfold SQIR.U2, decompose_CU2, uc_eval.
  simpl.
  replace (PI / 2 / 2)%R with (PI / 4)%R by lra.
  replace (- (PI / 2) / 2)%R with (- (PI / 4))%R by lra.
  reflexivity.
Qed.
Local Opaque SQIR.U2.

Local Transparent SQIR.U3.
Lemma decompose_CU3_is_control_U3 : forall dim r1 r2 r3 a b,
  uc_eval dim (decompose_CU3 r1 r2 r3 a b) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.U3 r1 r2 r3 b)).
Proof.
  intros dim r1 r2 r3 a b.
  unfold SQIR.U3, decompose_CU3, uc_eval.
  simpl.
  replace (- r1 / 2)%R with (- (r1 / 2))%R by lra.
  reflexivity.
Qed.
Local Opaque SQIR.U3.

Local Transparent SQIR.SWAP.
Lemma decompose_CSWAP_is_control_SWAP : forall dim a b c,
  uc_eval dim (decompose_CSWAP a b c) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.SWAP b c)).
Proof.
  intros dim a b c.
  unfold decompose_CSWAP, uc_eval, SWAP.
  simpl.
  reflexivity.
Qed.
Local Opaque SQIR.SWAP.


Lemma f_to_vec_control0 : forall dim q c f,
  (q < dim)%nat -> f q = false ->
  is_fresh q c -> uc_well_typed c ->
  UnitarySem.uc_eval (UnitaryOps.control q c) × (f_to_vec dim f) = f_to_vec dim f.
Proof.
  intros.
  rewrite control_correct by auto.
  rewrite Mmult_plus_distr_r.
  rewrite proj_fresh_commutes by auto.
  rewrite f_to_vec_proj_eq by auto.
  rewrite Mmult_assoc.
  rewrite f_to_vec_proj_neq; auto.
  Msimpl. reflexivity.
  rewrite H1. easy.
Qed.

Lemma f_to_vec_control1 : forall dim q c f,
  (q < dim)%nat -> f q = true ->
  is_fresh q c -> uc_well_typed c ->
  UnitarySem.uc_eval (UnitaryOps.control q c) × (f_to_vec dim f) = 
    (UnitarySem.uc_eval c) × (f_to_vec dim f).
Proof. 
  intros.
  rewrite control_correct by auto.
  rewrite Mmult_plus_distr_r.
  rewrite proj_fresh_commutes by auto.
  rewrite f_to_vec_proj_neq; auto.
  rewrite Mmult_assoc.
  rewrite f_to_vec_proj_eq by auto.
  Msimpl. reflexivity.
  rewrite H1. easy.
Qed.

Local Transparent SQIR.U1.
Lemma fresh_U1: forall dim r q1 q2, q1 <> q2 <-> is_fresh q1 (@SQIR.U1 dim r q2).
Proof. 
  intros.
  split; intro H.
  constructor. auto. 
  inversion H. auto.
Qed.
Local Opaque SQIR.U1.

Ltac apply_f_to_vec_rewrites :=
  repeat (try rewrite f_to_vec_control1 by auto;
          try rewrite f_to_vec_Rz by auto;
          try rewrite f_to_vec_CNOT by auto;
          distribute_scale;
          repeat rewrite update_index_eq;
          repeat rewrite update_index_neq by auto).

Lemma decompose_CCU1_is_control_CU1 : forall dim r a b c,
  uc_eval dim (decompose_CCU1 r a b c) = 
    UnitarySem.uc_eval (UnitaryOps.control a (UnitaryOps.control b (SQIR.U1 r c))).
Proof.
  intros dim r a b c.
  (* manually handle all the ill-typed cases *)
  bdestruct (a <? dim).
  2: { unfold decompose_CCU1, uc_eval. simpl.
       repeat rewrite (control_q_geq_dim a) by auto.
       Msimpl. reflexivity. }
  bdestruct (b <? dim).
  2: { unfold decompose_CCU1, uc_eval. simpl.
       rewrite (control_not_WT _ (SQIR.U1 (r / R2) b)).
       rewrite (control_not_WT _ (UnitaryOps.control _ _)).
       Msimpl. reflexivity.
       intro contra.
       apply uc_well_typed_control in contra as [? [? ?]]. lia.
       intro contra. apply uc_well_typed_Rz in contra. lia. }
  bdestruct (c <? dim).
  2: { unfold decompose_CCU1, uc_eval. simpl.
       rewrite (control_not_WT _ (SQIR.U1 (r / R2) c)).
       rewrite (control_not_WT _ (UnitaryOps.control _ _)).
       Msimpl. reflexivity.
       intro contra.
       apply uc_well_typed_control in contra as [? [? contra]]. 
       apply uc_well_typed_Rz in contra. lia.
       intro contra. apply uc_well_typed_Rz in contra. lia. }
  bdestruct (a =? b). subst.
  unfold decompose_CCU1, uc_eval. simpl.
  rewrite (control_not_fresh b (SQIR.U1 (r / R2) b)).
  rewrite (control_not_fresh b (UnitaryOps.control _ _)).
  Msimpl. reflexivity.
  intro contra.
  apply fresh_control in contra as [? ?]. lia.
  intro contra.
  apply fresh_U1 in contra. lia.
  bdestruct (a =? c). subst.
  unfold decompose_CCU1, uc_eval. simpl.
  rewrite (control_not_fresh c (SQIR.U1 (r / R2) c)).
  rewrite (control_not_fresh c (UnitaryOps.control _ _)).
  Msimpl. reflexivity.
  intro contra.
  apply fresh_control in contra as [? contra]. 
  apply fresh_U1 in contra. lia.
  intro contra.
  apply fresh_U1 in contra. lia.
  bdestruct (b =? c). subst.
  unfold decompose_CCU1, uc_eval. simpl.
  rewrite denote_cnot, unfold_ueval_cnot.
  bdestruct_all.
  rewrite (control_not_WT _ (UnitaryOps.control _ _)).
  Msimpl. reflexivity.
  intro contra.
  apply uc_well_typed_control in contra as [? [contra ?]]. 
  apply fresh_U1 in contra. lia.
  (* assert a couple easy facts for later reuse *)
  assert (is_fresh b (@SQIR.U1 dim r c)).
  { apply fresh_U1; auto. }
  assert (uc_well_typed (@SQIR.U1 dim r c)).
  { apply uc_well_typed_Rz; auto. }
  assert (is_fresh a (UnitaryOps.control b (@SQIR.U1 dim r c))).
  { apply fresh_control. split; auto.
    apply fresh_U1; auto. }
  assert (uc_well_typed (UnitaryOps.control b (@SQIR.U1 dim r c))).
  { apply uc_well_typed_control. repeat split; auto. }
  assert (is_fresh a (@SQIR.U1 dim (r / R2) b)).
  { apply fresh_U1; auto. }
  assert (uc_well_typed (@SQIR.U1 dim (r / R2) b)).
  { apply uc_well_typed_Rz; auto. }
  assert (is_fresh a (@SQIR.U1 dim (- r / R2) c)).
  { apply fresh_U1; auto. }
  assert (uc_well_typed (@SQIR.U1 dim (- r / R2) c)).
  { apply uc_well_typed_Rz; auto. }
  assert (is_fresh a (@SQIR.U1 dim (r / R2) c)).
  { apply fresh_U1; auto. }
  assert (uc_well_typed (@SQIR.U1 dim (r / R2) c)).
  { apply uc_well_typed_Rz; auto. }
  apply equal_on_basis_states_implies_equal.
  unfold decompose_CCU1, uc_eval. simpl. auto with wf_db.
  auto with wf_db.
  intro f.
  unfold decompose_CCU1, uc_eval. simpl.
  repeat rewrite Mmult_assoc.
  (* destruct on possible values of the control qubits *)
  destruct (f a) eqn:fa; destruct (f b) eqn:fb.
  - rewrite 2 f_to_vec_control1; auto.
    apply_f_to_vec_rewrites.
    rewrite f_to_vec_control1; auto.
    apply_f_to_vec_rewrites.
    rewrite f_to_vec_control1; auto.
    apply_f_to_vec_rewrites.
    rewrite fb. simpl.
    rewrite update_twice_eq.
    rewrite update_same; auto.
    rewrite <- 2 Cexp_add.
    destruct (f c); simpl; autorewrite with R_db.
    apply f_equal2; auto.
    apply f_equal; auto.
    unfold R2. lra.
    apply f_equal2; auto.
    apply f_equal; auto.
    lra.
    destruct (f c); reflexivity.
    rewrite fb.
    rewrite 2 update_index_neq; auto.
    rewrite update_index_neq; auto.
  - rewrite 2 f_to_vec_control1; auto.
    apply_f_to_vec_rewrites.
    rewrite f_to_vec_control1; auto.
    apply_f_to_vec_rewrites.
    rewrite f_to_vec_control1; auto.
    apply_f_to_vec_rewrites.
    rewrite f_to_vec_control0; auto.
    rewrite fb. simpl.
    rewrite update_twice_eq.
    rewrite update_same; auto.
    rewrite <- 2 Cexp_add.
    destruct (f c); simpl; autorewrite with R_db.
    replace (- (r * / R2) + r * / R2)%R with 0%R.
    rewrite Cexp_0, Mscale_1_l. reflexivity.
    unfold R2. lra.
    rewrite Cexp_0, Mscale_1_l. reflexivity.
    destruct (f c); reflexivity.
    rewrite fb.
    rewrite 2 update_index_neq; auto.
    rewrite update_index_neq; auto.
  - rewrite 2 f_to_vec_control0; auto.
    apply_f_to_vec_rewrites.
    rewrite f_to_vec_control0; auto.
    apply_f_to_vec_rewrites.
    rewrite f_to_vec_control0; auto.
    rewrite update_twice_eq.
    rewrite update_same; auto.
    rewrite fb. destruct (f c); reflexivity.
    rewrite 2 update_index_neq; auto.
    rewrite update_index_neq; auto.
  - rewrite 2 f_to_vec_control0; auto.
    apply_f_to_vec_rewrites.
    rewrite f_to_vec_control0; auto.
    apply_f_to_vec_rewrites.
    rewrite f_to_vec_control0; auto.
    rewrite update_twice_eq.
    rewrite update_same; auto.
    rewrite fb. destruct (f c); reflexivity.
    rewrite 2 update_index_neq; auto.
    rewrite update_index_neq; auto.
Qed.

Local Transparent SQIR.CNOT.
Lemma decompose_CCX_is_control_CX : forall dim a b c,
  uc_eval dim (decompose_CCX a b c) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.CNOT b c)).
Proof.
  intros dim a b c.
  unfold decompose_CCX, uc_eval, SQIR.CNOT.
  simpl.
  reflexivity.
Qed.
Local Opaque SQIR.CNOT.

Lemma f_to_vec_C3X : forall (dim a b c d : nat) (f : nat -> bool),
   (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> (d < dim)%nat -> 
   a <> b -> a <> c -> a <> d -> b <> c -> b <> d -> c <> d ->
  uc_eval dim (decompose_C3X a b c d) × (f_to_vec dim f) 
      = f_to_vec dim (update f d (f d ⊕ (f a && f b && f c))).
Proof. 
  intros.
  unfold uc_eval, decompose_C3X.
  simpl.
  repeat rewrite Mmult_assoc.
  (* TODO: why does "repeat" get stuck here? The term doesn't seem to
     change with more than 18 iterations. *)
  do 18 f_to_vec_simpl_body.
  repeat rewrite update_twice_eq.
  repeat rewrite update_index_eq.
  rewrite (update_twice_neq _ d b) by auto.
  rewrite (update_twice_neq _ d c) by auto.
  rewrite 2 update_twice_eq.
  rewrite (update_same _ b).
  2: destruct (f a); destruct (f b); reflexivity.
  rewrite (update_same _ c).
  2: destruct (f a); destruct (f b); destruct (f c); reflexivity.
  destruct (f a) eqn:fa; destruct (f b) eqn:fb; 
    destruct (f c) eqn:fc; destruct (f d) eqn:fd; simpl.
  all: autorewrite with R_db C_db Cexp_db.
  all: group_Cexp.
  all: try match goal with 
       | |- context [Cexp ?r] => field_simplify r
       end; unfold R8; try lra.
  all: autorewrite with R_db C_db Cexp_db.
  all: group_Cexp.
  all: try match goal with 
       | |- context [Cexp ?r] => field_simplify r
       end.
  all: replace (8 * PI / 8)%R with PI by lra.
  all: autorewrite with R_db C_db Cexp_db.
  all: rewrite Mscale_plus_distr_r.
  all: distribute_scale; group_radicals.
  all: lma.
Qed.

Local Transparent SQIR.CNOT.
Lemma fresh_CNOT : forall dim a b c, is_fresh a (@CNOT dim b c) -> a <> b /\ a <> c.
Proof. intros ? ? ? ? H. inversion H. auto. Qed.
Local Opaque SQIR.CNOT.

Local Transparent SQIR.H SQIR.CNOT SQIR.Rz SQIR.ID.
Lemma uc_well_typed_CCX: forall dim a b c : nat,
  (a < dim)%nat /\ (b < dim)%nat /\ (c < dim)%nat /\ a <> b /\ a <> c /\ b <> c 
    <-> uc_well_typed (@SQIR.CCX dim a b c).
Proof.
  intros dim a b c.
  split; intro H.
  destruct H as [? [? [? [? [? ?]]]]]. 
  repeat constructor; assumption. 
  invert_WT. 
  repeat split; assumption. 
Qed.
Local Opaque SQIR.H SQIR.CNOT SQIR.Rz SQIR.ID.

Lemma C3X_not_fresh : forall (dim a b c d : nat),
  ~ is_fresh a (@SQIR.CCX dim b c d) -> uc_eval dim (decompose_C3X a b c d) = Zero.
Proof.
  intros dim a b c d H.
  unfold uc_eval.
  simpl.
  assert (H0 : UnitarySem.uc_eval (@CNOT dim a b) = Zero \/ 
               UnitarySem.uc_eval (@CNOT dim a c) = Zero \/
               UnitarySem.uc_eval (@CNOT dim a d) = Zero).
  { assert (H0 : a = b \/ a = c \/ a = d).
    apply Classical_Prop.NNPP.
    intro contra. contradict H.
    apply fresh_CCX; repeat split; auto.
    destruct H0 as [H0 | [H0 | H0]]; subst.
    left. autorewrite with eval_db. gridify.
    right. left. autorewrite with eval_db. gridify.
    right. right. autorewrite with eval_db. gridify. }
  destruct H0 as [H0 | [H0 | H0]]; rewrite H0; Msimpl_light; trivial.
Qed.

Lemma C3X_not_WT : forall (dim a b c d : nat),
  ~ uc_well_typed (@SQIR.CCX dim b c d) -> uc_eval dim (decompose_C3X a b c d) = Zero.
Proof.
  intros dim a b c d H.
  unfold uc_eval.
  simpl.
  assert (H0 : UnitarySem.uc_eval (@CNOT dim b c) = Zero \/ 
               UnitarySem.uc_eval (@CNOT dim b d) = Zero \/ 
               UnitarySem.uc_eval (@CNOT dim c d) = Zero).
  { rewrite <- uc_well_typed_CCX in H.
    autorewrite with eval_db.
    gridify; auto. }
  destruct H0 as [H0 | [H0 | H0]]; rewrite H0; Msimpl_light; trivial.
Qed.

Lemma C3X_a_geq_dim : forall dim a b c d : nat,
  (dim <= a)%nat -> uc_eval dim (decompose_C3X a b c d) = Zero.
Proof.
  intros dim a b c d H.
  unfold uc_eval.
  simpl.
  assert (H0 : UnitarySem.uc_eval (@SQIR.U1 dim (PI / R8) a) = Zero).
  { autorewrite with eval_db. gridify. }
  rewrite H0.
  Msimpl_light. 
  trivial.
Qed.

Lemma decompose_C3X_is_control_CCX : forall dim a b c d,
  uc_eval dim (decompose_C3X a b c d) = 
    UnitarySem.uc_eval (UnitaryOps.control a (SQIR.CCX b c d)).
Proof.
  intros dim a b c d.
  bdestruct (a <? dim).
  destruct (@is_fresh_b _ dim a (SQIR.CCX b c d)) eqn:Hfr.
  apply is_fresh_b_equiv in Hfr.
  destruct (@uc_well_typed_b _ dim (SQIR.CCX b c d)) eqn:HWT.
  apply uc_well_typed_b_equiv in HWT.
  (* in the one well-typed case, we can use f_to_vec_C3X *)
  apply equal_on_basis_states_implies_equal. 
  unfold uc_eval. simpl.
  auto 40 with wf_db.
  auto with wf_db.
  intro f. Search SQIR.CCX.
  apply uc_well_typed_CCX in HWT as [? [? [? [? [? ?]]]]].
  apply fresh_CCX in Hfr as [? [? ?]].
  rewrite f_to_vec_C3X by assumption.
  rewrite control_correct.
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_assoc.
  rewrite f_to_vec_CCX by assumption.
  destruct (f a) eqn:fa.
  rewrite f_to_vec_proj_neq; auto.
  rewrite f_to_vec_proj_eq; auto.
  rewrite andb_true_l.
  lma.
  rewrite update_index_neq; auto.
  rewrite fa.
  apply diff_true_false. 
  rewrite (f_to_vec_proj_neq _ _ _ true); auto.
  rewrite f_to_vec_proj_eq; auto.
  rewrite andb_false_l.
  rewrite xorb_false_r.
  rewrite update_same; auto.
  lma.
  rewrite update_index_neq; auto.
  rewrite fa.
  apply diff_false_true. 
  apply fresh_CCX; auto.
  apply uc_well_typed_CCX; repeat split; auto.
  (* ill-typed cases *)
  apply not_true_iff_false in HWT.
  rewrite uc_well_typed_b_equiv in HWT.
  rewrite control_not_WT by assumption.
  apply C3X_not_WT. assumption.
  apply not_true_iff_false in Hfr.
  rewrite is_fresh_b_equiv in Hfr.
  rewrite control_not_fresh by assumption.
  apply C3X_not_fresh. assumption.
  rewrite control_q_geq_dim by assumption.
  apply C3X_a_geq_dim. assumption.
Qed.

Lemma decompose_CH_WF : forall x y,
  well_formed (decompose_CH x y).
Proof. intros. repeat constructor. Qed.

Lemma decompose_CCU1_WF : forall r x y z,
  well_formed (decompose_CCU1 r x y z).
Proof. intros. repeat constructor. Qed.

Lemma decompose_CSWAP_WF : forall x y z,
  well_formed (decompose_CSWAP x y z).
Proof. intros. repeat constructor. Qed.

Lemma decompose_C3X_WF : forall x y z w,
  well_formed (decompose_C3X x y z w).
Proof. intros. repeat constructor. Qed.

Lemma control'_WF : forall a u n, well_formed u -> well_formed (control' a u n).
Proof.
  intros a u n.
  generalize dependent u.
  generalize dependent a.
  induction n; intros a u WF.
  constructor; reflexivity.
  destruct u; simpl.
  inversion WF; subst.
  constructor; apply IHn; assumption.
  destruct u; simpl_WF; repeat constructor.
  all: apply IHn; repeat constructor.
Qed.

Local Transparent SQIR.Rz SQIR.U1 SQIR.U2 SQIR.U3 SQIR.H SQIR.X SQIR.CNOT SQIR.SWAP UnitaryOps.CU.

Lemma decompose_CH_fresh : forall dim a b c,
  UnitaryOps.is_fresh a (to_base_ucom dim (decompose_CH b c)) <->
  UnitaryOps.is_fresh a (UnitaryOps.control b (@SQIR.H dim c)).
Proof.
  intros dim a b c.
  split; intro H; simpl in *.
  invert_is_fresh.
  repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
Qed.

Lemma decompose_CCU1_fresh : forall dim a r b c d,
  is_fresh a (to_base_ucom dim (decompose_CCU1 r b c d)) <->
  is_fresh a (UnitaryOps.control b (UnitaryOps.control c (@SQIR.U1 dim r d))).
Proof.
  intros dim a r b c d.
  split; intro H; simpl in *.
  invert_is_fresh.
  repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
Qed.

Lemma decompose_CSWAP_fresh : forall dim a b c d,
  UnitaryOps.is_fresh a (to_base_ucom dim (decompose_CSWAP b c d)) <->
  UnitaryOps.is_fresh a (UnitaryOps.control b (@SQIR.SWAP dim c d)).
Proof. intros. reflexivity. Qed.

Lemma decompose_CCX_fresh : forall dim a b c d,
  UnitaryOps.is_fresh a (to_base_ucom dim (decompose_CCX b c d)) <->
  UnitaryOps.is_fresh a (UnitaryOps.control b (@SQIR.CNOT dim c d)).
Proof.
  intros dim a b c d.
  split; intro H; simpl in *.
  invert_is_fresh.
  apply fresh_CCX; auto.
  apply fresh_CCX in H as [? [? ?]].
  repeat constructor; auto.
Qed.

Lemma decompose_C3X_fresh : forall dim a b c d e,
  is_fresh a (to_base_ucom dim (decompose_C3X b c d e)) <->
  is_fresh a (UnitaryOps.control b (UnitaryOps.control c (@CNOT dim d e))).
Proof.
  intros dim a b c d e.
  split; intro H; simpl in *.
  invert_is_fresh.
  repeat constructor; auto.
  invert_is_fresh.
  repeat constructor; auto.
Qed.

Lemma fresh_control' : forall dim a b u n,
  (fuel u < n)%nat ->
  well_formed u ->
  (a <> b /\ UnitaryOps.is_fresh a (to_base_ucom dim u)) <-> 
  UnitaryOps.is_fresh a (to_base_ucom dim (control' b u n)).
Proof.
  intros dim a b u n Hfu WF.
  split.
  - intros [H1 H2].
    generalize dependent u.
    generalize dependent b.
    generalize dependent a.
    induction n; intros a b H1 u Hfu WF H2.
    lia.
    destruct u.
    inversion H2; subst.
    simpl in Hfu.
    inversion WF; subst.
    simpl.
    constructor; apply IHn; auto; lia.
    simpl.
    destruct u; simpl_WF.
    (* solve the cases that don't make a recursive call *)
    all: match goal with
         | |- context[control' _ _ _] => idtac
         | |- _ => invert_is_fresh; repeat constructor; auto
         end.
    (* C-CH *)
    apply IHn.
    assumption.
    simpl in Hfu. rewrite fuel_CH_eq. lia.
    apply decompose_CH_WF.
    invert_is_fresh; repeat constructor; auto.
    (* C-CCU1 *)
    apply IHn.
    assumption.
    simpl in Hfu. rewrite fuel_CCU1_eq. lia.
    apply decompose_CCU1_WF.
    invert_is_fresh; repeat constructor; auto.
    (* C-CSWAP *)
    apply IHn.
    assumption.
    simpl in Hfu. rewrite fuel_CSWAP_eq. lia.
    apply decompose_CSWAP_WF.
    invert_is_fresh; repeat constructor; auto.
    (* C-C3X *)
    apply IHn.
    assumption.
    simpl in Hfu. rewrite fuel_C3X_eq. lia.
    apply decompose_C3X_WF.
    invert_is_fresh; repeat constructor; auto.
  - generalize dependent u.
    generalize dependent b.
    generalize dependent a.
    induction n; intros a b u Hfu WF H.
    lia.
    destruct u.
    inversion H; subst.
    simpl in Hfu.
    inversion WF; subst.
    eapply IHn in H2 as [Hu1_1 Hu1_2].
    eapply IHn in H5 as [Hu2_1 Hu2_2].
    split. apply Hu1_1.
    constructor.
    apply Hu1_2.
    apply Hu2_2.
    lia.
    apply H4.
    lia.
    apply H3.
    destruct u; simpl_WF; simpl in *.
    1-7,9-10: invert_is_fresh; split; auto;repeat constructor; auto.
    (* C-CH *)
    apply IHn in H as [? ?].
    split; auto.
    invert_is_fresh.
    repeat constructor; auto.
    rewrite fuel_CH_eq. lia.
    apply decompose_CH_WF.
    (* C-CCU1 *)
    apply IHn in H as [? ?].
    split; auto.
    invert_is_fresh.
    repeat constructor; auto.
    rewrite fuel_CCU1_eq. lia.
    apply decompose_CCU1_WF.
    (* C-CSWAP *)
    apply IHn in H as [? ?].
    split; auto.
    rewrite fuel_CSWAP_eq. lia.
    apply decompose_CSWAP_WF.
    (* C-C3X *)
    apply IHn in H as [? ?].
    split; auto.
    invert_is_fresh.
    repeat constructor; auto.
    rewrite fuel_C3X_eq. lia.
    apply decompose_C3X_WF.
Qed.

Local Opaque SQIR.Rz SQIR.U1 SQIR.U2 SQIR.U3 SQIR.H SQIR.X SQIR.CNOT SQIR.SWAP UnitaryOps.CU.

Local Opaque decompose_CU1.
Lemma control'_correct : forall dim a u n,
  (fuel u < n)%nat ->
  well_formed u ->
  uc_eval dim (control' a u n) = 
    UnitarySem.uc_eval (UnitaryOps.control a (to_base_ucom dim u)).
Proof.
  intros dim a u n.
  generalize dependent u.
  generalize dependent a.
  induction n; intros a u Hfu WF.
  lia.
  destruct u; simpl.
  inversion WF; subst.
  unfold uc_eval in *.
  simpl in *.
  rewrite 2 IHn; try lia; auto.
  destruct u; simpl_WF; try reflexivity.
  (* C-X *)
  unfold uc_eval.
  simpl.
  rewrite control_ucom_X.
  reflexivity.
  (* C-U2 *)
  rewrite <- decompose_CU2_is_control_U2.
  reflexivity.
  (* C-U3 *)
  rewrite <- decompose_CU3_is_control_U3.
  reflexivity.
  (* C-CH *)
  unfold uc_eval in *.
  rewrite IHn.
  apply control_cong. 
  apply decompose_CH_is_control_H.
  apply decompose_CH_fresh.
  simpl in Hfu. rewrite fuel_CH_eq. lia.
  apply decompose_CH_WF.
  (* C-CU1 *)
  unfold uc_eval in *.
  rewrite IHn.
  apply control_cong. 
  apply decompose_CCU1_is_control_CU1.
  apply decompose_CCU1_fresh.
  simpl in Hfu. rewrite fuel_CCU1_eq. lia.
  apply decompose_CCU1_WF.
  (* C-CSWAP *)
  unfold uc_eval in *.
  rewrite IHn.
  apply control_cong. 
  apply decompose_CSWAP_is_control_SWAP.
  apply decompose_CSWAP_fresh.
  simpl in Hfu. rewrite fuel_CSWAP_eq. lia.
  apply decompose_CSWAP_WF.
  (* C-C3X *)
  unfold uc_eval in *.
  rewrite IHn.
  apply control_cong.
  apply decompose_C3X_is_control_CCX.
  apply decompose_C3X_fresh.
  simpl in Hfu. rewrite fuel_C3X_eq. lia.
  apply decompose_C3X_WF.
Qed.

Lemma control_correct : forall dim a u,
  well_formed u ->
  uc_eval dim (control a u) = 
    UnitarySem.uc_eval (UnitaryOps.control a (to_base_ucom dim u)).
Proof. intros. apply control'_correct; auto. Qed.

Fixpoint map_qubits (f : nat -> nat) (c : ucom U) : ucom U :=
  match c with
  | c1 >> c2 => map_qubits f c1 >> map_qubits f c2
  | uapp g qs => uapp g (List.map f qs)
  end.

Lemma map_qubits_WF : forall f (u : ucom U), 
  well_formed u -> well_formed (map_qubits f u).
Proof.
  intros f u WF.
  induction WF.
  simpl. constructor; auto.
  simpl. constructor.
  rewrite map_length. auto.
Qed.

Lemma map_qubits_same : forall dim f u,
  well_formed u ->
  to_base_ucom dim (map_qubits f u) = UnitaryOps.map_qubits f (to_base_ucom dim u).
Proof.
  intros dim f u WF.
  induction u.
  simpl.
  inversion WF; subst.
  rewrite <- IHu1, <- IHu2 by assumption.
  reflexivity.
  simpl.
  destruct u; simpl_WF; reflexivity.
Qed.

Lemma map_qubits_control' : forall f q u n,
  (fuel u < n)%nat ->
  well_formed u ->
  map_qubits f (control' q u n) = control' (f q) (map_qubits f u) n.
Proof.
  intros f q u n Hfu WF.
  generalize dependent u.
  generalize dependent q.
  induction n; intros q u Hfu WF.
  lia.
  destruct u.
  simpl.
  inversion WF; subst.
  simpl in Hfu.
  rewrite 2 IHn; auto; try lia.
  destruct u; simpl_WF; simpl in *; try reflexivity.
  (* C-CH *)
  rewrite IHn.
  reflexivity. 
  rewrite fuel_CH_eq. lia.
  apply decompose_CH_WF.
  (* C-CCU1 *)
  rewrite IHn.
  reflexivity. 
  rewrite fuel_CCU1_eq. lia.
  apply decompose_CCU1_WF.
  (* C-CSWAP *)
  rewrite IHn.
  reflexivity. 
  rewrite fuel_CSWAP_eq. lia.
  apply decompose_CSWAP_WF.
  (* C-C3X *)
  rewrite IHn.
  reflexivity. 
  rewrite fuel_C3X_eq. lia.
  apply decompose_C3X_WF.
Qed.

Lemma map_qubits_fuel : forall f u, fuel (map_qubits f u) = fuel u.
Proof. intros f u. induction u; simpl; auto. Qed.

Lemma map_qubits_control : forall f q u,
  well_formed u -> map_qubits f (control q u) = control (f q) (map_qubits f u).
Proof. 
  intros. 
  unfold control. 
  rewrite map_qubits_fuel.
  apply map_qubits_control'; auto.
Qed.

Fixpoint npar n (u : U 1) : ucom U :=
  match n with
  | O => SKIP
  | S O => uapp u [O]
  | S n' => npar n' u >> uapp u [n']
  end.

Lemma npar_H_same : forall n,
  uc_eval n (npar n U_H) = UnitarySem.uc_eval (UnitaryOps.npar n SQIR.U_H).
Proof.
  intro dim.
  assert (H : forall n, (0 < dim)%nat -> (n <= dim)%nat -> 
            uc_eval dim (npar n U_H) = 
              UnitarySem.uc_eval (UnitaryOps.npar' dim n SQIR.U_H)).
  { intros n Hdim Hn.
    induction n; try reflexivity.
    destruct n.
    unfold uc_eval. simpl. autorewrite with eval_db. gridify.
    rewrite hadamard_rotation. reflexivity. lia.
    unfold uc_eval in *.
    simpl in *.
    rewrite IHn.
    reflexivity.
    lia. }
  destruct dim; try reflexivity.
  apply H; lia.
Qed.

Fixpoint invert (u : ucom U) : ucom U :=
  match u with
  | u1 >> u2 => invert u2 >> invert u1
  | uapp g qs => 
      match g, qs with
      | U_X, (q1 :: List.nil)%list => X q1
      | U_H, (q1 :: List.nil) => H q1
      | U_U1 r1, (q1 :: List.nil) => U1 (- r1) q1
      | U_U2 r1 r2, (q1 :: List.nil) => U2 (- r2 - PI) (- r1 + PI) q1
      | U_U3 r1 r2 r3, (q1 :: List.nil) => U3 (- r1) (- r3) (- r2) q1
      | U_CX, (q1 :: q2 :: List.nil) => CX q1 q2
      | U_CH, (q1 :: q2 :: List.nil) => CH q1 q2
      | U_CU1 r, (q1 :: q2 :: List.nil) => CU1 (- r) q1 q2
      | U_SWAP, (q1 :: q2 :: List.nil) => SWAP q1 q2
      | U_CCX, (q1 :: q2 :: q3 :: List.nil) => CCX q1 q2 q3
      | U_CCU1 r, (q1 :: q2 :: q3 :: List.nil) => CCU1 (- r) q1 q2 q3
      | U_CSWAP, (q1 :: q2 :: q3 :: List.nil) => CSWAP q1 q2 q3
      | U_C3X, (q1 :: q2 :: q3 :: q4 :: List.nil) => C3X q1 q2 q3 q4
      (* dummy value - unreachable for well-formed progs *)
      | _, _ => SKIP
      end
  end.

Lemma invert_WF : forall u, well_formed u -> well_formed (invert u).
Proof.
  intros u H. 
  induction u. 
  inversion H; subst.
  simpl. constructor; auto.
  destruct u; simpl_WF; constructor; reflexivity.
Qed.

Lemma is_fresh_invert : forall {dim} q (u : base_ucom dim),
  is_fresh q u <-> is_fresh q (UnitaryOps.invert u).
Proof.
  intros dim q u.
  split; intro H.
  - induction u; try dependent destruction u.
    inversion H; subst.
    constructor; auto.
    invert_is_fresh; constructor; auto.
    invert_is_fresh; constructor; auto.
  - induction u; try dependent destruction u.
    inversion H; subst.
    constructor; auto.
    invert_is_fresh; constructor; auto.
    invert_is_fresh; constructor; auto.
Qed.

Local Opaque SQIR.CCX UnitaryOps.control.
Local Transparent SQIR.U1 SQIR.U2 SQIR.U3 SQIR.SWAP SQIR.CNOT.
Lemma invert_same : forall dim u,
  well_formed u -> (* WF isn't necessary, but makes the proof easier *)
  uc_eval dim (invert u) = 
    UnitarySem.uc_eval (UnitaryOps.invert (to_base_ucom dim u)).
Proof.
  intros dim u WF.
  induction u.
  unfold uc_eval in *.
  simpl.
  inversion WF; subst.
  rewrite IHu1, IHu2; auto.
  destruct u; simpl_WF; simpl; try reflexivity.
  (* U_X *)
  rewrite invert_X.
  reflexivity.
  (* U_H *)
  rewrite invert_H.
  reflexivity.
  (* U_U1 *)
  unfold uc_eval. simpl.
  rewrite Ropp_0.
  apply f_equal.
  unfold rotation.
  solve_matrix; autorewrite with Cexp_db trig_db R_db; lca.
  (* U_U2 *)
  unfold uc_eval. simpl.
  apply f_equal.
  unfold rotation.
  solve_matrix; autorewrite with Cexp_db trig_db R_db; lca.
  (* U_CU1 *)
  rewrite invert_control.
  unfold uc_eval. simpl.
  rewrite Ropp_0.
  apply control_cong.
  unfold uc_equiv. simpl.
  apply f_equal.
  unfold rotation.
  solve_matrix; autorewrite with Cexp_db trig_db R_db; lca.
  split; intro; invert_is_fresh; repeat constructor; auto.
  (* U_CH *)
  rewrite invert_control.
  apply control_cong.
  rewrite invert_H.
  reflexivity.
  apply is_fresh_invert.
  (* U_SWAP *)
  unfold uc_eval. simpl. 
  rewrite Mmult_assoc. 
  reflexivity.
  (* U_CCX *)
  rewrite invert_control.
  reflexivity.
  (* U_CCU1 *)
  rewrite invert_control.
  unfold uc_eval. simpl.
  apply control_cong.
  rewrite invert_control.
  apply control_cong.
  unfold uc_equiv. simpl.
  rewrite Ropp_0.
  apply f_equal.
  unfold rotation.
  solve_matrix; autorewrite with Cexp_db trig_db R_db; lca.
  split; intro; invert_is_fresh; repeat constructor; auto.
  rewrite <- is_fresh_invert.
  rewrite <- 2 fresh_control.
  split; intros [? ?]; invert_is_fresh; repeat constructor; auto.
  (* U_CSWAP *)
  rewrite invert_control.
  unfold uc_eval. simpl.
  apply control_cong.
  unfold uc_equiv. simpl.
  rewrite Mmult_assoc. 
  reflexivity.
  split; intro; invert_is_fresh; repeat constructor; auto.
  (* U_C3X *)
  rewrite invert_control.
  apply control_cong.
  rewrite invert_control.
  reflexivity.
  apply is_fresh_invert.
Qed.
Local Opaque SQIR.U1 SQIR.U2 SQIR.U3 SQIR.SWAP SQIR.CNOT.
Local Transparent SQIR.CCX UnitaryOps.control.

(* VOQC currently doesn't support CH, CU1, CCU1, CSWAP, C3X so it's useful
   to decompose these gates before writing out to a file.

   CCU1 gets its own pass since its decomposition uses CU1. *)
Fixpoint decompose_to_voqc_gates1 (u : ucom U) : ucom U :=
  match u with
  | u1 >> u2 => decompose_to_voqc_gates1 u1 >> decompose_to_voqc_gates1 u2
  | uapp (U_CCU1 r) (q1 :: q2 :: q3 :: List.nil) => decompose_CCU1 r q1 q2 q3
  | _ => u
  end.

Fixpoint decompose_to_voqc_gates2 (u : ucom U) : ucom U :=
  match u with
  | u1 >> u2 => decompose_to_voqc_gates2 u1 >> decompose_to_voqc_gates2 u2
  | uapp U_CH (q1 :: q2 :: List.nil) => decompose_CH q1 q2
  | uapp (U_CU1 r) (q1 :: q2 :: List.nil) => decompose_CU1 r q1 q2
  | uapp U_CSWAP (q1 :: q2 :: q3 :: List.nil) => decompose_CSWAP q1 q2 q3
  | uapp U_C3X (q1 :: q2 :: q3 :: q4 :: List.nil) => decompose_C3X q1 q2 q3 q4
  | _ => u
  end.

Definition decompose_to_voqc_gates u :=
  decompose_to_voqc_gates2 (decompose_to_voqc_gates1 u).

Lemma decompose_to_voqc_gates_preserves_semantics : forall dim u,
  uc_eval dim (decompose_to_voqc_gates u) = uc_eval dim u.
Proof.
  intro dim.
  assert (H1: forall u, uc_eval dim (decompose_to_voqc_gates1 u) = uc_eval dim u).
  { induction u.
    unfold uc_eval in *.
    simpl. 
    rewrite IHu1, IHu2.
    reflexivity.
    destruct u; simpl; try reflexivity.
    do 4 (destruct l; try reflexivity).
    apply decompose_CCU1_is_control_CU1. }
  assert (H2: forall u, uc_eval dim (decompose_to_voqc_gates2 u) = uc_eval dim u).
  { induction u.
    unfold uc_eval in *.
    simpl. 
    rewrite IHu1, IHu2.
    reflexivity.
    destruct u; simpl; try reflexivity.
    do 3 (destruct l; try reflexivity).
    apply decompose_CU1_is_control_U1.
    do 3 (destruct l; try reflexivity).
    apply decompose_CH_is_control_H.
    do 4 (destruct l; try reflexivity).
    do 4 (destruct l; try reflexivity).
    destruct l; [| reflexivity].
    apply decompose_C3X_is_control_CCX. }
  unfold decompose_to_voqc_gates.
  intro u. rewrite H2, H1. reflexivity.
Qed.
