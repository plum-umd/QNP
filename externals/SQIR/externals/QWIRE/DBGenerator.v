From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Contexts.
Require Import HOASCircuits.
Require Import DBCircuits.
Require Import Generator.

Require Import String. Open Scope string.
Require Import Reals.

Open Scope circ_scope.

(* DBCircuit 
Inductive DeBruijn_Circuit (w : WType) : Set :=
| db_output : Pat w -> DeBruijn_Circuit w
| db_gate   : forall {w1 w2},
               Gate w1 w2 -> Pat w1 -> DeBruijn_Circuit w -> DeBruijn_Circuit w
| db_lift   : Pat Bit -> (bool -> DeBruijn_Circuit w) -> DeBruijn_Circuit w
.
*)

Instance showDBCircuit {w : WType} : Show (DeBruijn_Circuit w) :=
  {| show := 
       let fix aux t :=
         match t with
           | db_output p => "db_output (" ++ (show p) ++ ")"
           | db_gate _ _ g p t' =>
             "db_gate " ++ (show g) ++ " (" ++ (show p) ++ "); " ++ (aux t')
           | db_lift p f =>
             "db_lift (" ++ (show p) ++ ") ("
                         ++ (aux (f true)) ++ ") (" ++ (aux (f false)) ++ ")"
         end
       in aux
  |}.

Eval compute in (show (db_output (pair (qubit 1) (bit 2)))).

Inductive AuxiliaryDBCircuit : WType -> Set :=
| aux_db_output {w} (p : Pat w) : AuxiliaryDBCircuit w
| aux_db_gate {w} (gg : GeneralGate) (pw1 : Pat (fst (GeneralGate_to_WType gg)))
              (adb : AuxiliaryDBCircuit w)
  : AuxiliaryDBCircuit w
| aux_db_lift {w} (pb : Pat Bit) (f : bool -> AuxiliaryDBCircuit w)
  : AuxiliaryDBCircuit w.

Instance showAuxiliaryDBCircuit {w} : Show (AuxiliaryDBCircuit w) :=
  {| show := 
       let fix aux {w} depth t := 
           match t with
           | aux_db_output _ p => "aux_db_output (" ++ (show p) ++ ")"
           | aux_db_gate _ g p t' =>
             "aux_db_gate " ++ (show g) ++ " (" ++ (show p) ++ ") (" ++ (aux depth t') ++ ")"
           | aux_db_lift _ p f =>
             "aux_db_lift (" ++ (show p) ++ ") ("
                             ++ "fun b" ++ (writeNat depth) ++ " => " ++
                             "match b" ++ (writeNat depth) ++ " with" ++
                             " | true => (" ++ (aux (S depth) (f true)) ++ ")" ++
                             " | false => (" ++ (aux (S depth) (f false)) ++ ")" ++
                             " end)"
           end
       in aux O
  |}.

Eval compute in (show (aux_db_output (pair (qubit 1) (bit 2)))).

Fixpoint AuxiliaryDBCircuit_to_WType {w} (adb : AuxiliaryDBCircuit w) : WType := w.
Check AuxiliaryDBCircuit_to_WType.
Fixpoint AuxiliaryDBCircuit_to_DBCircuit {w} (adb : AuxiliaryDBCircuit w) :
  DeBruijn_Circuit w :=
  match adb with
  | aux_db_output _ p => db_output p
  | aux_db_gate _ gg pw1 adb' => db_gate (GeneralGate_to_Gate gg) pw1
                                         (AuxiliaryDBCircuit_to_DBCircuit adb')
  | aux_db_lift _ pb f =>
    db_lift pb
            (fun (b : bool) =>
               match b with
               | true => (AuxiliaryDBCircuit_to_DBCircuit (f true))
               | false => (AuxiliaryDBCircuit_to_DBCircuit (f false))
               end)
  end.
Check AuxiliaryDBCircuit_to_DBCircuit.

Check fresh_pat.
Check substitution.
Check subst_pat.
Print subst_pat.
Check  hoas_to_db.
Check process_gate_state.
Print process_gate_state.
Check get_fresh.
Check (Monad.State substitution Var).
Check process_gate_pat.
Print Ctx.
Locate process_gate_pat.
Check process_gate_pat.
Print substitution.
Print Ctx.

(* [G (Var * Ctx)] corresponds to the generator for the type of [Var] selection in Ctx *)
Fixpoint genQubitsInCtx (?? : Ctx) (idx : nat) : list (G (ChoiceInCtx Var)) :=
  match ?? with
  | [] => []
  | h :: t => match h with
              | Some Qubit =>
                [returnGen (choice_in_Ctx Var idx (remove_var idx ??))]
                  ++ (genQubitsInCtx t (S idx))
              | Some Bit |Some One | Some (Tensor _ _) | None => genQubitsInCtx t (S idx)
              end
  end.

Fixpoint genBitsInCtx (?? : Ctx) (idx : nat) : list (G (ChoiceInCtx Var)) :=
  match ?? with
  | [] => []
  | h :: t => match h with
              | Some Bit => [returnGen (choice_in_Ctx Var idx (remove_var idx ??))]
                              ++ (genBitsInCtx t (S idx))
              | Some Qubit |Some One | Some (Tensor _ _) | None => genBitsInCtx t (S idx)
              end
  end.

Check (choice_in_Ctx Var).
Fixpoint selection_in_Ctx_to_selection_in_OCtx (s : (ChoiceInCtx Var)) : (ChoiceInOCtx Var) :=
  let (v, ctx) := s in (choice_in_OCtx Var v (Valid ctx)).

Fixpoint apply_fmap_in_list {A B} (li : list (G A)) (f : A -> B) : list (G B) :=
  match li with
  | [] => []
  | h :: t => (fmap f h) :: (apply_fmap_in_list t f)
  end.

(* [G (Var * OCtx)] corresponds to the generator for the type of [Var] selection in OCtx *)
Fixpoint genQubitsInOCtx (?? : OCtx) : list (G (ChoiceInOCtx Var)) :=
  match ?? with
  | Valid ctx =>
    apply_fmap_in_list (genQubitsInCtx ctx O) selection_in_Ctx_to_selection_in_OCtx
  | Invalid => []
  end.

Fixpoint genBitsInOCtx (?? : OCtx) : list (G (ChoiceInOCtx Var)) :=
  match ?? with
  | Valid ctx =>
    apply_fmap_in_list (genBitsInCtx ctx O) selection_in_Ctx_to_selection_in_OCtx
  | Invalid => []
  end.

(* genGeneralQubitFromOCtx : generator for the constructor [general_qubit] selection in OCtx
   genGeneralBitFromOCtx : generator for the constructor [general_bit] selection in OCtx *)
Fixpoint selection_of_Var_to_selection_of_general_qubit (s : (ChoiceInOCtx Var)) :
  (ChoiceInOCtx GeneralPat) :=
  let (v, octx) := s in (choice_in_OCtx GeneralPat (general_qubit v) octx).
Fixpoint selection_of_Var_to_selection_of_general_bit (s : (ChoiceInOCtx Var)) :
  (ChoiceInOCtx GeneralPat) :=
  let (v, octx) := s in (choice_in_OCtx GeneralPat (general_bit v) octx).
Fixpoint genGeneralQubitFromOCtx (?? : OCtx) : G (ChoiceInOCtx GeneralPat) :=
  fmap selection_of_Var_to_selection_of_general_qubit
       (oneof (returnGen (choice_in_OCtx Var O (remove_var O ??))) (genQubitsInOCtx ??)).
Fixpoint genGeneralBitFromOCtx (?? : OCtx) : G (ChoiceInOCtx GeneralPat) :=
  fmap selection_of_Var_to_selection_of_general_bit
       (oneof (returnGen (choice_in_OCtx Var O (remove_var O ??))) (genBitsInOCtx ??)).

(* genQubitFromOCtx : generator for the constructor [qubit] selection in OCtx
   genBitFromOCtx : generator for the constructor [bit] selection in OCtx *)
Fixpoint selection_of_Var_to_selection_of_qubit (s : (ChoiceInOCtx Var)) :
  (ChoiceInOCtx (Pat Qubit)) :=
  let (v, octx) := s in (choice_in_OCtx (Pat Qubit) (qubit v) octx).
Fixpoint selection_of_Var_to_selection_of_bit (s : (ChoiceInOCtx Var)) :
  (ChoiceInOCtx (Pat Bit)) :=
  let (v, octx) := s in (choice_in_OCtx (Pat Bit) (bit v) octx).
Fixpoint genQubitFromOCtx (?? : OCtx) : G (ChoiceInOCtx (Pat Qubit)) :=
  fmap selection_of_Var_to_selection_of_qubit
       (oneof (returnGen (choice_in_OCtx Var O (remove_var O ??))) (genQubitsInOCtx ??)).
Fixpoint genBitFromOCtx (?? : OCtx) : G (ChoiceInOCtx (Pat Bit)) :=
  fmap selection_of_Var_to_selection_of_bit
       (oneof (returnGen (choice_in_OCtx Var O (remove_var O ??))) (genBitsInOCtx ??)).

(* genGeneralPatWTypedFromOCtx : 
   generator for the type [ChoiceInOCtx GeneralPat] in OCtx for given [WType] *)
Fixpoint genGeneralPatWTypedFromOCtx (?? : OCtx) (w : WType) : G (ChoiceInOCtx GeneralPat) :=
  match w with
  | Qubit => genGeneralQubitFromOCtx ??
  | Bit => genGeneralBitFromOCtx ??
  | One => returnGen (choice_in_OCtx GeneralPat general_unit ??)
  | Tensor l r => bindGen (genGeneralPatWTypedFromOCtx ?? l)
                          (fun (lc : ChoiceInOCtx GeneralPat)
                           => let (pl, ??') := lc in
                              (bindGen (genGeneralPatWTypedFromOCtx ??' r)
                                       (fun (rc : ChoiceInOCtx GeneralPat)
                                        => let (pr, ??'') := rc in
                                           (returnGen
                                              (choice_in_OCtx GeneralPat
                                                              (general_pair pl pr)
                                                              ??'')))))
  end.

Sample (genGeneralPatWTypedFromOCtx ??? (Tensor (Qubit) (Tensor One Bit))).
Sample (genGeneralPatWTypedFromOCtx
          (Valid [Some Qubit; Some Qubit; Some Bit; Some Bit; Some Bit])
          (Tensor (Qubit) (Tensor One Bit))).
Check genGeneralPatWTypedFromOCtx.

(* genPatWTypedFromOCtx : generator for the type of choice for [Pat w] in OCtx *)
Fixpoint genPatWTypedFromOCtx (?? : OCtx) (w : WType) : G (ChoiceInOCtx (Pat w)) :=
  match w with
  | Qubit => genQubitFromOCtx ??
  | Bit => genBitFromOCtx ??
  | One => returnGen (choice_in_OCtx (Pat One) unit ??)
  | Tensor l r => bindGen (genPatWTypedFromOCtx ?? l)
                          (fun (lc : ChoiceInOCtx (Pat l))
                           => let (pl, ??') := lc in
                              (bindGen (genPatWTypedFromOCtx ??' r)
                                       (fun (rc : ChoiceInOCtx (Pat r))
                                        => let (pr, ??'') := rc in
                                           (returnGen
                                              (choice_in_OCtx (Pat (Tensor l r))
                                                              (pair pl pr)
                                                              ??'')))))
  end.

Sample (genPatWTypedFromOCtx ??? (Tensor (Qubit) (Tensor One Bit))).
Sample (genPatWTypedFromOCtx
          (Valid [Some Qubit; Some Qubit; Some Bit; Some Bit; Some Bit])
          (Tensor (Qubit) (Tensor One Bit))).
Check genPatWTypedFromOCtx.

Fixpoint countQubitsInWType (w : WType) : nat :=
  match w with
  | One => O
  | Qubit => 1
  | Bit => O
  | Tensor l r => (countQubitsInWType l) + (countQubitsInWType r)
  end.

Fixpoint countBitsInWType (w : WType) : nat :=
  match w with
  | One => O
  | Qubit => O
  | Bit => 1
  | Tensor l r => (countQubitsInWType l) + (countQubitsInWType r)
  end.

Fixpoint countQubitsInCtx (?? : Ctx) : nat :=
  match ?? with
  | [] => O
  | h :: t => match h with
              | Some w => (countQubitsInWType w) + (countQubitsInCtx t)
              | None => countQubitsInCtx t
              end
  end.

Fixpoint countBitsInCtx (?? : Ctx) : nat :=
  match ?? with
  | [] => O
  | h :: t => match h with
              | Some w => (countBitsInWType w) + (countBitsInCtx t)
              | None => countBitsInCtx t
              end
  end.

Fixpoint countQubitsInOCtx (?? : OCtx) : nat :=
  match ?? with
  | Valid ctx => countQubitsInCtx ctx
  | Invalid => O
  end.

Fixpoint countBitsInOCtx (?? : OCtx) : nat :=
  match ?? with
  | Valid ctx => countBitsInCtx ctx
  | Invalid => O
  end.

Check get_fresh.
Print Monad.State.
Print get_fresh.
Check get_fresh_var.
Print get_fresh_var.
Fixpoint add_init0_to_AuxiliaryDBCircuit {w} (adb : AuxiliaryDBCircuit w)
  : AuxiliaryDBCircuit w :=
  (aux_db_gate general_init0 unit adb).
Fixpoint add_init1_to_AuxiliaryDBCircuit {w} (adb : AuxiliaryDBCircuit w)
  : AuxiliaryDBCircuit w :=
  (aux_db_gate general_init1 unit adb).
Fixpoint add_new0_to_AuxiliaryDBCircuit {w} (adb : AuxiliaryDBCircuit w)
  : AuxiliaryDBCircuit w :=
  (aux_db_gate general_new0 unit adb).
Fixpoint add_new1_to_AuxiliaryDBCircuit {w} (adb : AuxiliaryDBCircuit w)
  : AuxiliaryDBCircuit w :=
  (aux_db_gate general_new1 unit adb).
Fixpoint add_meas_to_AuxiliaryDBCircuit {w} (qbit : Pat Qubit) (adb : AuxiliaryDBCircuit w)
  : AuxiliaryDBCircuit w :=
  (aux_db_gate general_meas qbit adb).
Fixpoint add_discard_to_AuxiliaryDBCircuit {w} (bit : Pat Bit) (adb : AuxiliaryDBCircuit w)
  : AuxiliaryDBCircuit w :=
  (aux_db_gate general_discard bit adb).

Eval compute in (get_fresh Qubit (Valid [Some Qubit; Some Bit])).

Fixpoint init_random_qubits_before
         {w : WType} (qn : nat) (gen : OCtx -> G (AuxiliaryDBCircuit w)) (?? : OCtx)
  : G (AuxiliaryDBCircuit w) :=
  match qn with
  | O => gen ??
  | S qn' => let (x, ??') := (get_fresh Qubit ??) in
             oneOf [ fmap add_init0_to_AuxiliaryDBCircuit
                          (init_random_qubits_before qn' gen ??') ;
                       fmap add_init1_to_AuxiliaryDBCircuit
                            (init_random_qubits_before qn' gen ??')
                   ]
  end.

Fixpoint new_random_bits_before
         {w : WType} (bn : nat) (gen : OCtx -> G (AuxiliaryDBCircuit w)) (?? : OCtx)
  : G (AuxiliaryDBCircuit w) :=
  match bn with
  | O => gen ??
  | S bn' => let (x, ??') := (get_fresh Bit ??) in
             oneOf [ fmap add_new0_to_AuxiliaryDBCircuit
                          (new_random_bits_before bn' gen ??') ;
                       fmap add_new1_to_AuxiliaryDBCircuit
                            (new_random_bits_before bn' gen ??')
                   ]
  end.

Check bindGen.
Check change_type.

Fixpoint meas_qubits_before
         {w : WType} (qn : nat) (gen : OCtx -> G (AuxiliaryDBCircuit w)) (?? : OCtx)
  : G (AuxiliaryDBCircuit w) :=
  match qn with
  | O => gen ??
  | S qn' => bindGen (genPatWTypedFromOCtx ?? Qubit)
                     (fun (choice : ChoiceInOCtx (Pat Qubit)) =>
                        let (qbit, _) := choice in
                        match qbit with
                        | qubit v => let ??' := (change_type v Bit ??) in
                                     fmap (add_meas_to_AuxiliaryDBCircuit qbit)
                                          (meas_qubits_before qn' gen ??')
                        end
                     )
  end.

Fixpoint discard_bits_before
         {w : WType} (bn : nat) (gen : OCtx -> G (AuxiliaryDBCircuit w)) (?? : OCtx)
  : G (AuxiliaryDBCircuit w) :=
  match bn with
  | O => gen ??
  | S bn' => bindGen (genPatWTypedFromOCtx ?? Bit)
                     (fun (choice : ChoiceInOCtx (Pat Bit)) =>
                        let (bit, _) := choice in
                        match bit with
                        | bit v => let ??' := (remove_var v ??) in
                                     fmap (add_discard_to_AuxiliaryDBCircuit bit)
                                          (meas_qubits_before bn' gen ??')
                        end
                     )
  end.

(* genAuxiliaryDBOutput : create required qubits and bits before the
   generator for the [aux_db_output] of type w from OCtx *)
Fixpoint genAuxiliaryDBOutput {w : WType} (?? : OCtx) : G (AuxiliaryDBCircuit w) :=
  meas_qubits_before
    ((countQubitsInOCtx ??) - (countQubitsInWType w))
    (discard_bits_before
       ((countQubitsInOCtx ??) - (countQubitsInWType w)
        + (countBitsInOCtx ??) - (countBitsInWType w))
       (init_random_qubits_before
          ((countQubitsInWType w) - (countQubitsInOCtx ??))
          (new_random_bits_before
             ((countBitsInWType w) - (countBitsInOCtx ??))
             (fun (?? : OCtx) =>
                liftGen aux_db_output
                        (fmap (fun (p : Pat w) => subst_pat ?? p)
                              (fmap (fun (p?? : ChoiceInOCtx (Pat w)) => let (p, ??) := p?? in p)
                                    (genPatWTypedFromOCtx ?? w))
                        )
             )
          )
       )
    )
    ??
.

(* genAuxiliaryDBLiftAux : create required qubits and bits before the
   generator for the [aux_db_lift] of type AuxiliaryDBCircuit from OCtx
   using given generator for [AuxiliaryDBCircuit w] *)
Fixpoint genAuxiliaryDBLift {w : WType} (?? : OCtx) (gen : OCtx -> G (AuxiliaryDBCircuit w))
  : G (AuxiliaryDBCircuit w) :=
  new_random_bits_before
    (1 - (countBitsInOCtx ??))
    (fun (?? : OCtx) =>
       bindGen (fmap (fun (p?? : ChoiceInOCtx (Pat Bit)) => let (p, ??) := p?? in p)
                     (genPatWTypedFromOCtx ?? Bit))
               (fun (p : Pat Bit) =>
                  let p0 := subst_pat ?? p in
                  let ??' := remove_pat p ?? in
                  (fmap (aux_db_lift p0)
                        (liftGen2 (fun (c1 c2 : AuxiliaryDBCircuit w) =>
                                     (fun (b : bool) => match b with
                                                        | true => c1
                                                        | false => c2
                                                        end)
                                  ) (gen ??') (gen ??')))
               )
    )
    ??.

(* genAuxiliaryDBGate : create required qubits and bits before the
   generator for the [aux_db_gate] of type AuxiliaryDBCircuit from OCtx
   using given generator for [AuxiliaryDBCircuit w] *)
Check genGeneralGate.
Print genGeneralGate.
Check liftGen2.
Check GeneralGate_to_WType.
Check genGeneralPatWTypedFromOCtx.
Print ChoiceInOCtx.
Check general_BNOT .
Print GeneralGate.
(*
Definition process_general_gate_state
           (g : GeneralGate) (p : Pat (fst (GeneralGate_to_WType g))) (?? : OCtx) : OCtx :=
  match g with 
  | general_U _ | general_BNOT    => ??
  | general_init0 | general_init1 => add_fresh_state Qubit ??
  | general_new0 | general_new1   => add_fresh_state Bit ??
  | general_meas                  => match p with
                                     | qubit x => change_type x Bit ??
                                     | _ =>  ??
                                     end
  | general_measQ                 => ??
  | general_discard               => match p with
                                     | bit x => remove_var x ??
                                     | _ =>  ??
                                     end
  | general_assert0 | general_assert1   => match p with
                                           | qubit x => remove_var x ??
                                           | _ =>  ??
                                           end
  end.
*)
Fixpoint genAuxiliaryDBGate
         {w : WType} (?? : OCtx) (tn : nat) (gen : OCtx -> G (AuxiliaryDBCircuit w))
  : G (AuxiliaryDBCircuit w) :=
  bindGen (genGeneralGate tn)
          (fun (g : GeneralGate) =>
             let (w1, w2) := (GeneralGate_to_WType g) in
             init_random_qubits_before
               ((countQubitsInWType w1) - (countQubitsInOCtx ??))
               (new_random_bits_before
                  ((countBitsInWType w1) - (countBitsInOCtx ??))
                  (fun (?? : OCtx) =>
                     (bindGen (fmap
                                 (fun (p?? : ChoiceInOCtx (Pat (fst (GeneralGate_to_WType g))))
                                  => let (p, ??) := p?? in p)
                                 (genPatWTypedFromOCtx ?? (fst (GeneralGate_to_WType g)))
                              )
                              (fun (p : Pat (fst (GeneralGate_to_WType g))) =>
                                 let g' := GeneralGate_to_Gate g in
                                 let p' := process_gate_pat g' p ?? in
                                 let p0 := subst_pat ?? p in
                                 let ??' := process_gate_state g' p ?? in
                                 (liftGen (aux_db_gate g p0) (gen ??'))
                              )
                     )
                  )
               )
               ??
          )
.

(* ?? can be either [Ctx] or [OCtx]
   but assumed to be [OCtx] for this generator *)
(* tn : parameter for [Unitary] gate generator *)
Fixpoint genAuxiliaryDBCircuitWTypedSizedAux (w : WType) (sz : nat) (tn : nat) (?? : OCtx)
  : G (AuxiliaryDBCircuit w) :=
  match sz with
  | O => genAuxiliaryDBOutput ??
  | S sz' => oneOf [ genAuxiliaryDBGate ?? tn (genAuxiliaryDBCircuitWTypedSizedAux w sz' tn) ;
                       genAuxiliaryDBLift ?? (genAuxiliaryDBCircuitWTypedSizedAux w sz' tn)
                   ]
  end.

(* we are using OCtx as state type *)
Fixpoint genAuxiliaryDBCircuitWTypedSized (w : WType) (sz : nat)
  : G (AuxiliaryDBCircuit w) :=
  bindGen arbitrary
          (fun (tn : nat) =>
             genAuxiliaryDBCircuitWTypedSizedAux w sz tn (Valid [])
          ).

Check ???.
Check liftGen.
Check bindGen.
Fixpoint genAuxiliaryDBCircuitWTyped (w : WType) : G (AuxiliaryDBCircuit w) :=
  bindGen arbitrary
          (fun (sz : nat) =>
             genAuxiliaryDBCircuitWTypedSized w sz
          ).

Sample (genAuxiliaryDBCircuitWTyped Qubit).

Inductive GeneralDBCircuit :=
| general_db_circuit : forall (w : WType), AuxiliaryDBCircuit w -> GeneralDBCircuit.

Check GeneralDBCircuit.

Instance showGeneralDBCircuit : Show (GeneralDBCircuit) :=
  {| show := 
       let fix aux t := 
           match t with
           | general_db_circuit w adb => "general_db_circuit (" ++ (show adb) ++ ")"
           end
       in aux
  |}.

Eval compute in (show (general_db_circuit
                         Qubit
                         (aux_db_gate general_init0 (unit) (aux_db_output (qubit 1))))).

Fixpoint GeneralDBCircuit_to_WType (gdb : GeneralDBCircuit) : WType :=
  match gdb with
  | general_db_circuit w adb => w
  end.
Check GeneralDBCircuit_to_WType.
Fixpoint GeneralDBCircuit_to_DBCircuit (gdb : GeneralDBCircuit) :
  DeBruijn_Circuit (GeneralDBCircuit_to_WType gdb) :=
  match gdb with
  | general_db_circuit w adb => AuxiliaryDBCircuit_to_DBCircuit adb
  end.
Check GeneralDBCircuit_to_DBCircuit.

(*
Inductive GeneralDBCircuit :=
| general_db_output (gp : GeneralPat) : GeneralDBCircuit
| general_db_gate
    (gg : GeneralGate) (pw1 : Pat (fst (GeneralGate_to_WType gg))) (gdb : GeneralDBCircuit)
  : GeneralDBCircuit
| general_db_lift (pb : Pat Bit) (f : bool -> GeneralDBCircuit)
  : GeneralDBCircuit.

Instance showGeneralDBCircuit : Show (GeneralDBCircuit) :=
  {| show := 
       let fix aux t := 
           match t with
           | general_db_output p => "general_db_output (" ++ (show p) ++ ")"
           | general_db_gate g p t' =>
             "general_db_gate " ++ (show g) ++ " (" ++ (show p) ++ "); " ++ (aux t')
           | general_db_lift p f =>
             "general_db_lift (" ++ (show p) ++ ") ("
                         ++ (aux (f true)) ++ ") (" ++ (aux (f false)) ++ ")"
           end
       in aux
  |}.

Eval compute in (show (general_db_output (general_pair (general_qubit 1) (general_bit 2)))).

Fixpoint GeneralDBCircuit_to_WType (gdb : GeneralDBCircuit) : WType :=
  match gdb with
  | general_db_output gp => GeneralPat_to_WType gp
  | general_db_gate gg pw1 gdb' => GeneralDBCircuit_to_WType gdb'
  | general_db_lift pb f => GeneralDBCircuit_to_WType (f true)
  end.
Check GeneralDBCircuit_to_WType.
Fail Fixpoint GeneralDBCircuit_to_DBCircuit (gdb : GeneralDBCircuit) :
  DeBruijn_Circuit (GeneralDBCircuit_to_WType gdb) :=
  match gdb with
  | general_db_output gp => db_output (GeneralPat_to_Pat gp)
  | general_db_gate gg pw1 gdb' => db_gate (GeneralGate_to_Gate gg) pw1
                                           (GeneralDBCircuit_to_DBCircuit gdb')
  | general_db_lift pb f => db_lift pb
                                    (fun (b : bool) =>
                                       match b with
                                       | true => (GeneralDBCircuit_to_DBCircuit (f true))
                                       | false => (GeneralDBCircuit_to_DBCircuit (f false))
                                       end)
  end.
Fail Check GeneralDBCircuit_to_DBCircuit.
*)

Fixpoint genGeneralDBCircuitWTyped (w : WType) :=
  liftGen (general_db_circuit w) (genAuxiliaryDBCircuitWTyped w).

Sample (genAuxiliaryDBCircuitWTypedSized Qubit 3).

Check genWType.
Check genGeneralDBCircuitWTyped.
Definition genGeneralDBCircuit : G GeneralDBCircuit :=
  bindGen genWType genGeneralDBCircuitWTyped.

(* Too slow!
Sample genGeneralDBCircuit.
 *)

(* Properties on the random db_circuits *)

(* compare the denotation semantic with qasm simulator *)
(*
Require Import Denotation.
Check denote_db_circuit.

Open Scope nat.


Definition random_auxiliary_db_circuit_long := aux_db_gate general_new0 (unit) (aux_db_lift (bit 0) (fun b0 => match b0 with | true => (aux_db_gate general_new1 (unit) (aux_db_lift (bit 0) (fun b1 => match b1 with | true => (aux_db_gate general_init0 (unit) (aux_db_output (qubit 0))) | false => (aux_db_gate general_init0 (unit) (aux_db_output (qubit 0))) end))) | false => (aux_db_gate general_new0 (unit) (aux_db_lift (bit 0) (fun b1 => match b1 with | true => (aux_db_gate general_init0 (unit) (aux_db_output (qubit 0))) | false => (aux_db_gate general_init0 (unit) (aux_db_output (qubit 0))) end))) end)).

Definition random_auxiliary_db_circuit := aux_db_gate general_new1 (unit) (aux_db_lift (bit 0) (fun b1 => match b1 with | true => (aux_db_gate general_init0 (unit) (aux_db_output (qubit 0))) | false => (aux_db_gate general_init0 (unit) (aux_db_output (qubit 0))) end)).

Definition random_db_circuit :=
  (AuxiliaryDBCircuit_to_DBCircuit random_auxiliary_db_circuit).

Eval compute in random_db_circuit.
Eval compute in (process_general_gate_state general_discard (bit O) (Valid [Some Bit])).
Eval compute in (process_general_gate_state general_init0 (unit) (Valid [None])).

Lemma random_db_circuit_WT :
  Types_DB ??? (random_db_circuit).
Proof.
  unfold random_db_circuit.
  simpl.
  eapply (types_db_gate ??? ??? ???).
  { apply types_unit. }
  { assert (L : process_gate_state new0 unit (Valid []) = Valid [Some Bit]).
    { unfold process_gate_state. simpl. reflexivity. }
    rewrite L. clear L.
    eapply (types_db_lift (Valid [Some Bit]) (Valid [Some Bit]) ??? (Valid [None])).
    { eapply types_bit.
      apply SingletonHere. }
    { destruct b.
      { eapply (types_db_gate (Valid [None]) ??? (Valid [None])).
        { apply types_unit. }
        { assert (process_gate_state new1 unit [None] = [Some Bit]).
          { unfold process_gate_state. simpl. simpl.
          Eval compute in (.
          eapply (types_db_lift (Valid [Some Bit]) (Valid [Some Bit]) ??? (Valid [None])).
          { eapply types_bit. apply SingletonLater. }
          process_gate_state new1 unit [None]
        }
        { solve_merge. }
      }
      { eapply (types_db_gate (Valid [None]) ??? (Valid [None])).
        { apply types_unit. }
        { admit. }
        { solve_merge. }
      }
    }
    { solve_merge. }
    { unfold remove_pat. simpl. reflexivity. }
  }
        { solve_merge. }
        
Qed.
Definition random_denotation :=
  (denote_db_circuit true O O random_db_circuit).

Check random_denotation.

Eval simpl in (random_denotation (I 1)).
Eval compute in (random_denotation (I 1)).
)

Definition eq_denotation_qasm_simulator (gdb : GeneralDBCircuit) :=
  let dbc := (GeneralDBCircuit_to_DBCircuit gdb) in
  let denotation := (denote_db_circuit true O O dbc) in
  let mat := denotation (I 1) in
  (mat O O + mat 1%nat 1%nat) = 1?.

QuickChick (forAll (genGeneralDBCircuitWTyped Qubit) eq_denotation_qasm_simulator).
  type_check (GeneralDBCircuit_to_DBCircuit gdb).

QuickChick QASMP
*)
Close Scope circ_scope.
