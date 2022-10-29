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
(**********************)
(** Session Definitions **)
(**********************)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Local Open Scope nat_scope.

Check exp.

Inductive simple_ses : session -> Prop :=
    simple_ses_empty : simple_ses nil
  | simple_ses_many :  forall a x y l, simple_bound x -> simple_bound y -> simple_ses l -> simple_ses ((a,x,y)::l).


Inductive ses_eq : session -> session -> Prop :=
   ses_eq_empty : forall a, ses_eq a a
 | ses_eq_range_empty : forall x n a b, ses_eq a b -> ses_eq ((x,n,n)::a) b
 | ses_eq_split: forall x i n m a b, n <= i < m -> 
        ses_eq ((x,BNum n,BNum i)::((x,BNum i,BNum m)::a)) b -> ses_eq ((x,BNum n,BNum m)::a) b
 | ses_eq_merge: forall x i n m a b, n <= i < m -> ses_eq ((x,BNum n,BNum m)::a) b
        -> ses_eq ((x,BNum n,BNum i)::((x,BNum i,BNum m)::a)) b.


Inductive ses_sub : session -> session -> Prop :=
   ses_sub_prop : forall a b b', ses_eq b (a++b') -> ses_sub a b.

Definition in_range (r1 r2:range) :=
  match r1 with (x,BNum a,BNum b) => 
    match r2 with (y,BNum c, BNum d) => ((x = y) /\ (c <= a) /\ (b <= d))
                  | _ => False
    end
              | _ => False
  end.

Inductive ses_dis_aux : range -> session -> Prop := 
    ses_dis_aux_empty : forall r, ses_dis_aux r nil
  | ses_dis_aux_many: forall r a l, ~ in_range r a -> ses_dis_aux r l -> ses_dis_aux r (a::l).


Inductive ses_dis_aux2 : range -> session -> Prop := 
    ses_dis_empty : forall r, ses_dis_aux2 r nil
  | ses_dis_many: forall r a l, ses_dis_aux r (a::l) -> ses_dis_aux2 a l -> ses_dis_aux2 r (a::l).

Definition ses_dis (s:session) :=
   match s with [] => True | (a::l) => ses_dis_aux2 a l end.
 
(*
Inductive in_seses  : list (var*nat*nat) -> list (var*nat*nat) -> Prop :=
   in_ses_1 : forall a b l, in_ses a b = true -> in_seses (a::l) (b::l)
 | in_ses_2 : forall a b l, in_ses a b = true -> in_seses (l++([a])) (l++([b])).

Inductive in_session : list (var*nat*nat) -> list (var*nat*nat) -> Prop :=
     in_session_rule : forall a a' b c d, b = c++a'++d -> in_seses a a' -> in_session a b.

Inductive in_ses_pos : list (var*nat*nat) -> list (var*nat*nat) -> nat * nat -> Prop :=
   find_pos_rule: forall a b c d, b = c++a++d -> in_ses_pos a b (length c, length c + length a).

*)

(*
Fixpoint find_pos' (p:posi) (l:list (var*nat*nat)) (pos:nat) :=
   match l with [] => 0
              | (x,n,m)::xs => if (x =? fst p) && (n <=? snd p) && (snd p <? m)
                               then (pos + (snd p) - n)
                               else find_pos' p xs (pos + m - n)
   end.
Definition find_pos p l := find_pos' p l 0.

Fixpoint find_range' (x:var) (l:list (var*nat*nat)) (pos : nat) :=
   match l with [] => None
             | (y,n,m)::xs => if x =? y
                          then (if n =? 0 then Some (pos,pos +m) else None)
                          else find_range' x xs (pos + m -n)
   end.
Definition find_range x l := find_range' x l 0.

Definition type_cfac : Type := nat -> rz_val.

Inductive type_phase :=  Uni.
*)

(*| Uni (b: nat -> rz_val) | DFT (b: nat -> rz_val). *)
Definition type_cfac : Type := nat -> rz_val.
Inductive se_type : Type := TNor | THad | CH.

(*
Inductive se_type : Type := THT (n:nat) (t:type_elem).
*)

Definition type_map := list (session * se_type).

Fixpoint ses_len_aux (l:list (var * nat * nat)) :=
   match l with nil => 0 | (x,l,h)::xl => (h - l) + ses_len_aux xl end. 

Fixpoint get_core_ses (l:session) :=
   match l with [] => Some nil
           | (x,BNum n, BNum m)::al => 
      match get_core_ses al with None => None
                           | Some xl => Some ((x,n,m)::xl)
      end
            | _ => None
   end.

Definition ses_len (l:session) := match get_core_ses l with None => None | Some xl => Some (ses_len_aux xl) end.

Inductive subtype :  se_type -> se_type -> Prop :=
   | sub_refl: forall a, subtype a a 
   | nor_ch:  subtype TNor CH
   | had_ch:  subtype THad CH.
(*
   | nor_ch: forall n p, subtype n (TNor (Some p))
           (CH (Some (1,fun i => if i =? 0 then p else allfalse)))
   | ch_nor: forall n b, subtype n (CH (Some (1,b))) (TNor (Some (b 0)))
   | had_ch: forall n p, subtype n (TH p) (CH (Some ((2^n),(fun i => nat2fb i))))
   | ch_had: forall p, p 0 = nat2fb 0 -> p 1 = nat2fb 1 -> 
           subtype 1 (CH (Some (2,p))) (TH None)
   | ch_none: forall n p, subtype n (CH (Some p)) (CH None).
*)

(*
Definition join_val {A:Type} (n :nat) (r1 r2:nat -> A) := fun i => if i <? n then r1 n else r2 (i-n).

Definition lshift_fun {A:Type} (f:nat -> A) (n:nat) := fun i => f (i+n).

Definition join_nor_val (n:nat) (r1 r2:option rz_val) :=
   match (r1,r2) with (Some ra1,Some ra2) => Some (join_val n ra1 ra2)
                   | (_,_) => None
   end.

Definition join_had_val (n:nat) (r1 r2:option type_phase) :=
   match (r1,r2) with (Some Uni,Some Uni) => Some Uni
                   | (_,_) => None
   end.

Fixpoint car_s (i:nat) (n:nat) (m:nat) (r1:rz_val) (r2 : type_cfac) : type_cfac := 
    match n with 0 => (fun x => allfalse)
              | S n' => (fun x => if x =? i+n' then join_val m r1 (r2 n') else car_s i n' m r1 r2 x)
    end.
Fixpoint car_fun (size n m:nat) (r1 r2: type_cfac) :=
   match n with 0 => (fun x => allfalse)
        | S n' => (fun x => if (m * n' <=? x) && (x <? m * n)
                        then car_s (m * n') m size (r1 n') r2 x
                        else car_fun size n' m r1 r2 x)
   end.

Definition join_ch_val (size:nat) (r1 r2:option (nat * type_cfac)) :=
   match (r1,r2) with (Some (n,r1),Some (m,r2)) => Some (m*n,car_fun size n m r1 r2)
                   | (_,_) => None
   end.
*)

Inductive times_type: se_type -> se_type -> se_type -> Prop :=
  | nor_nor_to: times_type TNor TNor TNor
  | had_had_to: times_type THad THad THad
  | ch_ch_to_1 : forall a, times_type a CH CH
  | ch_ch_to_2 : forall b, times_type CH b CH.

(*
Definition split_nor_val (n:nat) (r:option rz_val) :=
   match r with None => (None,None)
             | Some ra => (Some (cut_n ra n), Some (lshift_fun ra n))
   end.

Definition split_had_val (n:nat) (r:option type_phase) :=
   match r with None => (None,None)
             | Some Uni => (Some Uni, Some Uni)
   end.
*)

Inductive split_type: se_type -> se_type -> Prop :=
  | nor_split: split_type TNor TNor
  | had_split: split_type THad THad.

(*
Inductive mut_type: nat -> nat -> nat -> se_type -> se_type -> Prop :=
  | nor_mut: forall pos n m r,
             mut_type pos n m (TNor (r)) (TNor (mut_nor pos n m r))
  | had_mut: forall pos n m r, mut_type pos n m ((TH (r))) ((TH r))
  | ch_mut: forall pos n m r, mut_type pos n m ((CH r)) ((CH (mut_ch pos n m r))).
*)
Inductive env_equiv : type_map -> type_map -> Prop :=
     | env_empty : forall v S, env_equiv ((nil,v)::S) S
     | env_comm :forall a1 a2, env_equiv (a1++a2) (a2++a1)
     | env_ses_eq: forall s s' v S, ses_eq s s' -> env_equiv ((s,v)::S) ((s',v)::S)
     | env_ses_split: forall s s' v S, split_type v v -> env_equiv ((s++s',v)::S) ((s,v)::(s',v)::S) 
     | env_ses_merge: forall s s' a b c S, times_type a b c -> env_equiv ((s,a)::(s',b)::S) ((s++s',c)::S)
     | env_mut: forall l1 l2 a b v S, env_equiv ((l1++(a::b::l2),v)::S) ((l1++(b::a::l2),v)::S).

Inductive find_env {A:Type}: list (session * A) -> session -> option (session * A) -> Prop :=
  | find_env_empty : forall l, find_env nil l None
  | find_env_many_1 : forall S x y t, ses_sub x y -> find_env ((y,t)::S) x (Some (y,t))
  | find_env_many_2 : forall S x y v t, ~ ses_sub x y -> find_env S y t -> find_env ((x,v)::S) y t.

Inductive find_type : type_map -> session -> option (session * se_type) -> Prop :=
    | find_type_rule: forall S S' x t, env_equiv S S' -> find_env S' x t -> find_type S x t.


Inductive update_env {A:Type}: list (session * A) -> session -> A -> list (session * A) -> Prop :=
  | up_env_empty : forall l t, update_env nil l t ([(l,t)])
  | up_env_many_1 : forall S x t t', update_env ((x,t)::S) x t' ((x,t')::S)
  | up_env_many_2 : forall S S' x y t t', x <> y -> update_env S x t' S' -> update_env ((y,t)::S) x t' ((y,t)::S').

(* Define semantic state equations. *)

Inductive state_elem :=
                 | Nval (p:C) (r:rz_val)
                 | Hval (b:nat -> rz_val)
                 | Cval (m:nat) (b : nat -> C * rz_val).

Definition qstate := list (session * state_elem).

Fixpoint n_rotate (rmax:nat) (r1 r2:rz_val) :=
   match rmax with 0 => r1
              | S n => if r2 n then n_rotate n (addto r1 n) r2 else n_rotate n r1 r2
   end.

Fixpoint sum_rotate (n:nat) (b:nat->bool) (rmax:nat) (r:nat -> rz_val) :=
   match n with 0 => allfalse
             | S m => if b m then n_rotate rmax (sum_rotate m b rmax r) (r m) else sum_rotate m b rmax r
   end.

Fixpoint r_n_rotate (rmax:nat) (r1 r2:rz_val) :=
   match rmax with 0 => r1
              | S n => if r2 n then r_n_rotate n (addto_n r1 n) r2 else r_n_rotate n r1 r2
   end.

Definition a_nat2fb f n := natsum n (fun i => Nat.b2n (f i) * 2^i).

Fixpoint turn_angle_r (rval :nat -> bool) (n:nat) (size:nat) : R :=
   match n with 0 => (0:R)
             | S m => (if (rval m) then (1/ (2^ (size - m))) else (0:R)) + turn_angle_r rval m size
   end.
Definition turn_angle (rval:nat -> bool) (n:nat) : R :=
      turn_angle_r (fbrev n rval) n n.

Definition get_amplitude (rmax:nat) (r1:R) (r2:rz_val) : C := 
    r1 * Cexp (2*PI * (turn_angle r2 rmax)).

Definition sum_rotates (n:nat) (rmax:nat) (r:nat -> rz_val) :=
    fun i => if i <? 2^n then 
        (get_amplitude rmax ((1/sqrt (2^n))%R) (sum_rotate n (nat2fb i) rmax r),nat2fb i) else (C0,allfalse).

Inductive state_same {rmax:nat} : nat -> state_elem -> state_elem -> Prop :=
   | nor_ch_ssame: forall n r c, state_same n (Nval r c)
             (Cval 1 (fun i => if i =? 0 then (r,c) else (C0,allfalse)))
   | ch_nor_ssame: forall n r, state_same n (Cval 1 r) (Nval (fst (r 0)) (snd (r 0)))
   | had_ch_ssame : forall n r, state_same n (Hval r) (Cval (2^n) (sum_rotates n rmax r)).
(*
   | ch_had_ssame: forall r a e1 e2, r 0 = (a,e1,nat2fb 0) -> 
            r 1 = (a,e2,nat2fb 1) -> state_same 1 (Cval 2 r) (Hval (fun i => r_n_rotate rmax e2 e1))
   | ch_fch_ssame: forall n m r, state_same n (Cval m r) 
                (Fval m (fun i => (get_amplitude rmax (fst (fst (r i))) (snd (fst (r i))), snd (r i)))).
*)

Definition mut_had_state (pos n m: nat) (r : (nat -> rz_val)) :=
    fun i => if i <? pos then r i
      else if (pos <=? i) && (i <? pos + m) then r (i+n)
      else if (pos + m <=? i) && (i <? pos + m + n) then r (i - m)
      else r i.

(*
Definition mut_ch_state (pos n m:nat) (r : nat -> R * rz_val * rz_val) :=
    fun i => (fst (fst (r i)),snd (fst (r i)), mut_nor_aux pos n m (snd (r i))).
*)
Definition mut_nor_aux (pos n m: nat) (r : rz_val) :=
    fun i => if i <? pos then r i
      else if (pos <=? i) && (i <? pos + m) then r (i+n)
      else if (pos + m <=? i) && (i <? pos + m + n) then r (i - m)
      else r i.

Definition mut_nor (pos n m:nat) (r: option rz_val) :=
   match r with None => None | Some ra => Some (mut_nor_aux pos n m ra) end.


Definition mut_ch_aux (pos n m: nat) (r : type_cfac) : type_cfac :=
    fun i => mut_nor_aux pos n m (r i).

Definition mut_ch (pos n m : nat) (r : option (nat * type_cfac)) :=
  match r with None => None | Some (len,ra) => Some (len, mut_ch_aux pos n m ra) end.

Definition mut_fch_state (pos n m:nat) (r : nat -> C * rz_val) :=
    fun i => (fst (r i), mut_nor_aux pos n m (snd (r i))).

Definition join_val {A:Type} (n :nat) (r1 r2:nat -> A) := fun i => if i <? n then r1 n else r2 (i-n).

Definition lshift_fun {A:Type} (f:nat -> A) (n:nat) := fun i => f (i+n).

Definition join_cval (rmax:nat) (m:nat) (r1 r2: R * rz_val * rz_val) :=
     (((fst (fst r1)) * (fst (fst r2)))%R,n_rotate rmax (snd (fst r1)) (snd (fst r2)),join_val m (snd r1) (snd r2)).

Fixpoint car_s_ch (rmax:nat) (i:nat) (n:nat) (m:nat) (r1:R*rz_val*rz_val) (r2 : nat -> R*rz_val*rz_val) := 
    match n with 0 => (fun x => (0%R,allfalse,allfalse))
              | S n' => (fun x => if x =? i+n' 
                  then join_cval rmax m r1 (r2 n') else car_s_ch rmax i n' m r1 r2 x)
    end.
Fixpoint car_fun_ch (rmax size n m:nat) (r1 r2: nat -> R * rz_val * rz_val) :=
   match n with 0 => (fun x => (0%R,allfalse,allfalse))
        | S n' => (fun x => if (m * n' <=? x) && (x <? m * n)
                        then car_s_ch rmax (m * n') m size (r1 n') r2 x
                        else car_fun_ch rmax size n' m r1 r2 x)
   end.

Definition join_fval (m:nat) (r1 r2: C * rz_val) : C * rz_val :=
     (((fst r1) * (fst r2))%C,join_val m (snd r1) (snd r2)).

Fixpoint car_s_fch (i:nat) (n:nat) (m:nat) (r1:C * rz_val) (r2 : nat -> C * rz_val) := 
    match n with 0 => (fun x => (C0,allfalse))
              | S n' => (fun x => if x =? i+n' 
                  then join_fval m r1 (r2 n') else car_s_fch i n' m r1 r2 x)
    end.
Fixpoint car_fun_fch (size n m:nat) (r1 r2: nat -> C * rz_val) :=
   match n with 0 => (fun x => (C0,allfalse))
        | S n' => (fun x => if (m * n' <=? x) && (x <? m * n)
                        then car_s_fch (m * n') m size (r1 n') r2 x
                        else car_fun_fch size n' m r1 r2 x)
   end.


Inductive mut_state: nat -> nat -> nat -> state_elem -> state_elem -> Prop :=
  | nor_mut_state: forall pos n m r c,
             mut_state pos n m (Nval r c) (Nval r (mut_nor_aux pos n m c))
  | had_mut_state: forall pos n m r, mut_state pos n m (Hval r) (Hval (mut_had_state pos n m r))
  (*| ch_mut_state: forall pos n m num r, mut_state pos n m (Cval num r) (Cval num (mut_ch_state pos n m r)) *)
  | fch_mut_state: forall pos n m num r, mut_state pos n m (Cval num r) (Cval num (mut_fch_state pos n m r)).

Inductive times_state {rmax:nat}: nat -> state_elem -> state_elem -> state_elem -> Prop :=
  | state_nor_nor_to: forall n r1 r2 p1 p2,
               times_state n (Nval r1 p1) (Nval r2 p2) (Nval (r1*r2)%C (join_val n p1 p2))
  | state_had_had_to: forall n p1 p2,
               times_state n (Hval p1) (Hval p2) (Hval (join_val n p1 p2))
 (* | state_ch_ch_to : forall n m1 m2 p1 p2,
               times_state n (Cval m1 p1) (Cval m2 p2) (Cval (m1*m2) (car_fun_ch rmax n m1 m2 p1 p2)). *)
  | state_fch_fch_to : forall n m1 m2 p1 p2,
               times_state n (Cval m1 p1) (Cval m2 p2) (Cval (m1*m2) (car_fun_fch n m1 m2 p1 p2)).

Definition cut_n_rz (f:nat -> rz_val) (n:nat) := fun i => if i <? n then f i else allfalse.

Inductive split_state {rmax:nat}: nat -> state_elem -> state_elem * state_elem -> Prop :=
  | nor_split_state: forall n r c, split_state n (Nval r c) (Nval r (cut_n c n), Nval C1 (lshift_fun c n))
  | had_split_state: forall n r, split_state n (Hval r) (Hval (cut_n_rz r n), Hval (lshift_fun r n))
  (*| ch_split_state: forall n m r r1 r2, car_fun_ch rmax n m 1 r1 r2 = r
                -> split_state n (Cval m r) (Cval m r1, Cval 1 r2) *)
  | fch_split_state: forall n m r r1 r2, car_fun_fch n m 1 r1 r2 = r
                -> split_state n (Cval m r) (Cval m r1, Cval 1 r2).


Inductive state_equiv {rmax:nat} : qstate -> qstate -> Prop :=
     | state_empty : forall v S, state_equiv ((nil,v)::S) S
     | state_comm :forall a1 a2, state_equiv (a1++a2) (a2++a1)
     | state_ses_eq: forall s s' v S, ses_eq s s' -> state_equiv ((s,v)::S) ((s',v)::S)
     | state_sub: forall x v n u a, ses_len x = Some n -> @state_same rmax n v u -> state_equiv ((x,v)::a) ((x,u)::a)
     | state_mut: forall l1 l2 n a n1 b n2 v u S, ses_len l1 = Some n -> ses_len ([a]) = Some n1 -> ses_len ([b]) = Some n2 ->
                     mut_state n n1 n2 v u ->
                 state_equiv ((l1++(a::b::l2),v)::S) ((l1++(b::a::l2),u)::S)
     | state_merge: forall x n v y u a vu, ses_len x = Some n -> 
                       @times_state rmax n v u vu -> state_equiv ((x,v)::((y,u)::a)) ((x++y,vu)::a)
     | state_split: forall x n y v v1 v2 a, ses_len x = Some n -> 
                  @split_state rmax n v (v1,v2) -> state_equiv ((x++y,v)::a) ((x,v1)::(y,v2)::a).


(* partial measurement list filter.  *)
(*
Fixpoint build_type_par (m n v i:nat) (f acc:type_cfac) :=
    match m with 0 => (i,acc)
              | S m' => if a_nat2fb (f i) n =? v
             then build_type_par m' n v (i+1) f (fun x => if x =? i then lshift_fun (f i) n else acc x)
             else build_type_par m' n v i f acc
    end.
Definition build_type_pars m n v f := build_type_par m n v 0 f (fun i => allfalse).

Definition build_type_ch n v (t : se_type) := 
     match t with CH None => Some (CH None)
                | CH (Some (m,f)) => match build_type_pars m n v f with (m',f') => Some (CH (Some (m', f'))) end
                | _ => None
     end.

Fixpoint merge_acc' (m size n:nat) (f:type_cfac) (r:rz_val) := 
   match m with 0 => (size+1,fun i => if i =? size then r else f i)
             | S i => if a_nat2fb (f i) n =? a_nat2fb r n then (size,f) else merge_acc' i size n f r
   end.
Definition merge_acc (m n:nat) (f:type_cfac) (r:rz_val) := merge_acc' m m n f r.

Fixpoint build_type_fac (m n:nat) (f:type_cfac) (acc: nat * type_cfac) :=
    match m with 0 => acc
              | S i => build_type_fac i n f (merge_acc (fst acc) n (snd acc) (cut_n (f i) n))
    end.
Definition build_type_facs (m n:nat) (f:type_cfac) := build_type_fac m n f (0,fun i => allfalse).

Definition mask_type (l:session) (m n:nat) (t:type_cfac) :=
   ExT (build_type_facs m n t) (fun v => CH (Some (build_type_pars m n v t))).



Fixpoint build_state_par (m n v i:nat) (f acc:nat -> C * rz_val) :=
    match m with 0 => (i,acc)
              | S m' => if a_nat2fb (snd (f i)) n =? v
             then build_state_par m' n v (i+1) f (fun x => if x =? i then (fst (f i),lshift_fun (snd (f i)) n) else acc x)
             else build_state_par m' n v i f acc
    end.
Definition build_state_pars m n v f := build_state_par m n v 0 f (fun i => (C0,allfalse)).

Definition build_state_ch n v (t : state_elem) := 
     match t with | Fval m f => match build_state_pars m n v f with (m',f') => Some (Fval m' f') end
                | _ => None
     end.

Inductive mask_state {rmax:nat}: session -> nat -> qstate -> qstate -> Prop :=
    mask_state_rule : forall l n l1 t t' S Sa, @state_equiv rmax S ((l++l1,t)::Sa) -> 
              build_state_ch (ses_len l) n t = Some t' -> mask_state l n S ((l1,t')::Sa).
*)
(* substitution *)

Fixpoint subst_aexp (a:aexp) (x:var) (n:nat) :=
    match a with BA y => if x =? y then Num n else BA y
              | Num a => Num a
              | MNum r a => MNum r a
              | APlus c d => match ((subst_aexp c x n),(subst_aexp d x n)) with (Num q, Num t) =>  Num (q+t)
                                | _ => APlus (subst_aexp c x n) (subst_aexp d x n) 
                             end
              | AMult c d => match ((subst_aexp c x n),(subst_aexp d x n)) with (Num q, Num t) =>  Num (q*t)
                                | _ => AMult (subst_aexp c x n) (subst_aexp d x n) 
                             end
    end.

Fixpoint simp_aexp (a:aexp) :=
   match a with BA y => None
             | Num a => Some a
              | MNum r a => None
             | APlus c d => match (simp_aexp c,simp_aexp d) with (Some v1,Some v2) => Some (v1+v2)
                                | (_,_) => None
                            end
             | AMult c d => match (simp_aexp c,simp_aexp d) with (Some v1,Some v2) => Some (v1*v2)
                                | (_,_) => None
                            end
   end.


Definition subst_varia (a:varia) (x:var) (n:nat) :=
   match a with AExp b => AExp (subst_aexp b x n)
              | Index x v => Index x (subst_aexp v x n)
   end. 

Definition subst_cbexp (a:cbexp) (x:var) (n:nat) :=
    match a with CEq c d => CEq (subst_varia c x n) (subst_varia d x n)
              | CLt c d => CLt (subst_varia c x n) (subst_varia d x n)
    end.

Definition subst_bexp (a:bexp) (x:var) (n:nat) :=
    match a with CB b => CB (subst_cbexp b x n)
              | BEq c d i e => BEq (subst_varia c x n) (subst_varia d x n) i (subst_aexp e x n)
              | BLt c d i e => BLt (subst_varia c x n) (subst_varia d x n) i (subst_aexp e x n)
              | BTest i e => BTest i (subst_aexp e x n)
    end.

Definition subst_bound (b:bound) (x:var) (n:nat) :=
   match b with (BVar y m) => if x =? y then BNum (n+m) else (BVar y m) | BNum m => BNum m end.

Definition subst_range (r:range) (x:var) (n:nat) := 
   match r with (a,b,c) => (a,subst_bound b x n,subst_bound c x n) end.

Fixpoint subst_session (l:session) (x:var) (n:nat) :=
  match l with nil => nil
          | y::yl => (subst_range y x n)::(subst_session yl x n)
  end.

Fixpoint subst_exp (e:exp) (x:var) (n:nat) :=
        match e with SKIP y a => SKIP y (subst_aexp a x n)
                   | X y a => X y (subst_aexp a x n) 
                   | CU y a e' => CU y (subst_aexp a x n) (subst_exp e' x n)
                   | RZ q y a => RZ q y (subst_aexp a x n)
                   | RRZ q y a => RRZ q y (subst_aexp a x n)
                   | SR q y => SR q y
                   | SRR q y => SRR q y
                   | Lshift x => Lshift x
                   | Rshift x => Rshift x
                   | Rev x => Rev x
                   | QFT x b => QFT x b
                   | RQFT x b => RQFT x b
                   | Seq s1 s2 => Seq (subst_exp s1 x n) (subst_exp s2 x n)
        end.

Definition subst_mexp (e:maexp) (x:var) (n:nat) :=
   match e with AE a => AE (subst_aexp a x n)
              | Meas y => Meas y
   end.

Check List.fold_right.
Fixpoint subst_pexp (e:pexp) (x:var) (n:nat) :=
        match e with PSKIP => PSKIP
                   | Let y a e' => if y =? x then Let y (subst_mexp a x n) e' else Let y (subst_mexp a x n) (subst_pexp e' x n)
                   | AppSU (RH v) => AppSU (RH (subst_varia v x n))
                   | AppSU p => AppSU p
                   | AppU l e' => AppU l (subst_exp e' x n)
                   | If b s => If (subst_bexp b x n) (subst_pexp s x n)
                   | For i l h b p => if i =? x then For i (subst_aexp l x n) (subst_aexp h x n) b p
                                      else For i (subst_aexp l x n) (subst_aexp h x n) (subst_bexp b x n) (subst_pexp p x n)
                   | Diffuse y => Diffuse y
                   | PSeq s1 s2 => PSeq (subst_pexp s1 x n) (subst_pexp s2 x n)
        end.

(* Session Type. *)
(*Inductive factor := AType (a:atype) | Ses (a:session).

Coercion AType : atype >-> factor.

Coercion Ses : session  >-> factor.
*)
Module AEnv := FMapList.Make Nat_as_OT.
Module AEnvFacts := FMapFacts.Facts (AEnv).
Definition aenv := AEnv.t atype.
Definition empty_aenv := @AEnv.empty atype.

Definition stack := AEnv.t (R * nat).
Definition empty_stack := @AEnv.empty (R * nat).

Definition state : Type := (stack * qstate).

Definition find_cenv (l:state) (a:var) := (AEnv.find a (fst l)).

Inductive remove_type : type_map -> session -> type_map -> Prop :=
   | remove_type_rule: forall S S' l v, @env_equiv S ((l,v)::S') -> remove_type S l S'.

Inductive up_type : type_map -> session -> se_type -> type_map -> Prop :=
   | up_type_rule: forall S S' l l1 v t, @env_equiv S ((l++l1,v)::S') -> up_type S l t ((l,t)::S').

Inductive up_types: type_map -> type_map -> type_map -> Prop :=
   | up_type_empty: forall T, up_types T [] T
   | up_type_many: forall T T1 T2 T3 s t, up_type T s t T1 -> up_types T1 T2 T3 -> up_types T ((s,t)::T2) T3.

Inductive find_state {rmax} : state -> session -> option (session * state_elem) -> Prop :=
    | find_qstate_rule: forall M S S' x t, @state_equiv rmax S S' -> find_env S' x t -> find_state (M,S) x t.

(*
Inductive pick_mea {rmax:nat} : state -> var -> nat -> (R * nat) -> Prop :=
   pick_meas : forall s x n l m b i r bl, @find_state rmax s ([(x,0,n)]) (Some (([(x,0,n)])++l, Fval m b))
            -> 0 <= i < m -> b i = (r,bl) -> pick_mea s x n (Cmod r, a_nat2fb bl n).
*)

Definition update_cval (l:state) (a:var) (v: R * nat) := (AEnv.add a v (fst l),snd l).

Inductive up_state {rmax:nat} : state -> session -> state_elem -> state -> Prop :=
    | up_state_rule : forall S M M' M'' l t, @state_equiv rmax M M' -> update_env M' l t M'' -> up_state (S,M) l t (S,M'').


Definition join_two_ses (a:(var * nat * nat)) (b:(var*nat*nat)) :=
   match a with (x,n1,n2) => 
      match b with (y,m1,m2) => 
            if x =? y then (if n1 <=? m1 then 
                               (if n2 <? m1 then None
                                else if n2 <? m2 then Some (x,n1,m2)
                                else Some(x,n1,n2))
                            else if m2 <? n1 then None
                            else if n2 <? m2 then Some (x,m1,m2)
                            else Some (x,m1,n2))
            else None
     end
   end.

Definition dom {A:Type} (l: list (session * A)) := fst (split l).

Fixpoint join_ses_aux (a:(var * nat * nat)) (l:list ((var * nat * nat))) :=
     match l with [] => ([a])
           | (x::xs) => match join_two_ses a x with None => x::join_ses_aux a xs
                                         | Some ax => ax::xs
                        end
     end.

Fixpoint join_ses (l1 l2:list ((var * nat * nat))) :=
    match l1 with [] => l2
               | x::xs => join_ses_aux x (join_ses xs l2)
   end.


Definition union_f (t1 t2:ktype) := meet_ktype t1 t2.

Inductive type_aexp : aenv -> aexp -> (ktype*session) -> Prop :=
   | ba_type : forall env b t, AEnv.MapsTo b t env -> type_aexp env b t
   | num_type : forall env n, type_aexp env n CT
   | plus_type : forall env e1 e2 t1 t2, 
                   type_aexp env e1 t1 -> type_aexp env e2 t2 ->  
                     type_aexp env (APlus e1 e2) (meet_atype t1 t2)
   | mult_type : forall env e1 e2 t1 t2, 
                   type_aexp env e1 t1 -> type_aexp env e2 t2 ->  
                     type_aexp env (AMult e1 e2) (meet_atype t1 t2)
   | mnum_type : forall env r n, type_aexp env (MNum r n) MT.


Inductive type_vari : aenv -> varia -> (ktype*session) -> Prop :=
   | aexp_type : forall env a t, type_aexp env a t -> type_vari env a t
   | index_type : forall env x a b v,
       AEnv.MapsTo x (Ses ([(x,a,b)])) env -> a <= v < b -> type_vari env (Index x (Num v)) (Ses ([(x,v,S v)]))
   | permu_type: forall env e t1 t2, Permutation t1 t2 -> type_vari env e (Ses t1) -> type_vari env e (Ses t2).


Inductive type_bexp : aenv -> bexp -> factor -> Prop :=
   | beq_type : forall env a b t1 t2 x v1 v2 v, type_vari env a t1 -> type_vari env b t2 ->
             AEnv.MapsTo x (Ses ([(x,v1,v2)])) env -> v1 <= v < v2 
            -> type_bexp env (BEq a b x (Num v)) (union_f (union_f t1 t2) (Ses ([(x,v,S v)])))
   | blt_type : forall env a b t1 t2 x v1 v2 v, type_vari env a t1 -> type_vari env b t2 ->
             AEnv.MapsTo x (Ses ([(x,v1,v2)])) env -> v1 <= v < v2 
            -> type_bexp env (BEq a b x (Num v)) (union_f (union_f t1 t2) (Ses ([(x,v,S v)])))
   | btest_type : forall env x v1 v2 v, 
             AEnv.MapsTo x (Ses ([(x,v1,v2)])) env -> v1 <= v < v2 
            -> type_bexp env (BTest x (Num v)) (Ses ([(x,v,S v)]))
   | bpermu_type: forall env e t1 t2, Permutation t1 t2 -> type_bexp env e (Ses t1) -> type_bexp env e (Ses t2).


Inductive type_exp (qenv : var -> nat) : aenv -> exp -> factor -> Prop :=
   | skip_fa : forall env x a, type_exp qenv env (SKIP x a) (Ses nil)
   | x_fa : forall env x v, type_exp qenv env (X x (Num v)) (Ses ([(x,v, S v)]))
   | rz_fa : forall env q x v, type_exp qenv env (RZ q x (Num v)) (Ses ([(x,v, S v)]))
   | rrz_fa : forall env q x v, type_exp qenv env (RRZ q x (Num v)) (Ses ([(x,v, S v)]))
   | sr_fa : forall env q x, type_exp qenv env (SR q x) (Ses ([(x,0, qenv x)]))
   | srr_fa : forall env q x, type_exp qenv env (SRR q x) (Ses ([(x,0, qenv x)]))
   | qft_fa : forall env q x, type_exp qenv env (QFT x q) (Ses ([(x,0, qenv x)]))
   | rqft_fa : forall env q x, type_exp qenv env (RQFT x q) (Ses ([(x,0, qenv x)]))
   | lft_fa : forall env x, type_exp qenv env (Lshift x) (Ses ([(x,0, qenv x)]))
   | rft_fa : forall env x, type_exp qenv env (Rshift x) (Ses ([(x,0, qenv x)]))
   | rev_fa : forall env x, type_exp qenv env (Rev x) (Ses ([(x,0, qenv x)]))
   | cu_fa : forall env x v e t1, type_exp qenv env e t1 ->
                 type_exp qenv env (CU x (Num v) e) (union_f (Ses ([(x,v, S v)])) t1)
   | seq_fa : forall env e1 t1 e2 t2, type_exp qenv env e1 t1 -> type_exp qenv env e2 t2 ->
                 type_exp qenv env (Seq e1 e2) (union_f t1 t2)
   | permu_fa: forall env e t1 t2, Permutation t1 t2 -> type_exp qenv env e (Ses t1) -> type_exp qenv env e (Ses t2).

Definition gen_ses (qenv: var -> nat) (p:varia) :=
   match p with (AExp (BA x)) => Some (([(x,0,qenv x)]),qenv x)
             | Index x (Num n) => Some (([(x,n,n+1)]), 1)
             | _ => None
   end.

Fixpoint remove_ses (s:session) (a: (var * nat * nat)) :=
   match s with [] => []
            | b::xl => if in_ses b a then xl else b::(remove_ses xl a)
   end.

Definition remove_ses_env (env:aenv) (a:(var*nat*nat)) :=
 AEnv.map (fun f => match f with AType b => AType b | Ses b => Ses (remove_ses b a) end) env.

Inductive Fold_all {P : (var -> nat) -> aenv -> pexp -> factor -> Prop} (qenv:var -> nat): nat -> nat -> aenv -> pexp -> factor -> Prop :=
      | Forall_nil : forall n aenv e, Fold_all qenv n 0 aenv e (Ses nil)
      | Forall_cons : forall n m aenv e t1 t2, P qenv aenv e t1 -> Fold_all qenv (S n) m aenv e t2 -> Fold_all qenv n (S m) aenv e (union_f t1 t2).


Inductive type_pexp (qenv : var -> nat) : aenv -> pexp -> factor -> Prop :=
  | pskip_fa: forall env, type_pexp qenv env (PSKIP) (Ses nil)
  | let_fa_c : forall env x a v e t2, type_aexp env a (AType CT) -> simp_aexp a = Some v ->
                   type_pexp qenv env (subst_pexp e x v) t2 -> type_pexp qenv env (Let x (AE a) e) t2
  | let_fa_1 : forall env x a e t2, type_aexp env a (AType MT) ->
                   type_pexp qenv env e t2 -> type_pexp qenv env (Let x (AE a) e) (union_f MT t2)
  | let_fa_2 : forall env x y e t2, 
                   type_pexp qenv (AEnv.add x (Ses ([(x,0,y)])) env) e t2 
                     -> type_pexp qenv env (Let x (Init y) e) t2
  | let_fa_3 : forall env x y e t2, 
                   type_pexp qenv env e t2 
                     -> type_pexp qenv env (Let x (Meas y) e) t2
  | appsu_fa_h: forall env a x lb rb,
          type_aexp env a (Ses ([(x,lb,rb)])) -> type_pexp qenv env (AppSU (RH a)) (Ses ([(x,lb,rb)]))
  | appsu_fa_qft: forall env x s, AEnv.MapsTo x (Ses s) env
             -> type_pexp qenv env (AppSU (SQFT x)) (Ses s)
  | appsu_fa_rqft: forall env x s, AEnv.MapsTo x (Ses s) env
             -> type_pexp qenv env (AppSU (SRQFT x)) (Ses s)
  | appu_fa: forall env e t, type_exp qenv env e (Ses t) -> type_pexp qenv env (AppU t e) (Ses t)
  | pseq_fa : forall env e1 e2 t1 t2, type_pexp qenv env e1 t1 -> type_pexp qenv env e2 t2 -> type_pexp qenv env (PSeq e1 e2) (union_f t1 t2)
  | if_fa : forall env e b t1 t2, type_bexp env b t1 -> type_pexp qenv env e t2 -> type_pexp qenv env (If b e) (union_f t1 t2)
  | for_fa : forall env x l h b e t, @Fold_all type_pexp qenv l h env (If b e) t -> type_pexp qenv env (For x (Num l) (Num h) b e) t
  | amplify_fa: forall env x n b s, type_aexp env n (AType b) -> AEnv.MapsTo x (Ses s) env -> 
                         type_pexp qenv env (Amplify x n) (Ses s)
  | diffuse_fa: forall env x s, AEnv.MapsTo x (Ses s) env -> type_pexp qenv env (Diffuse x) (Ses s)
  | permu_fa_p: forall env e t1 t2, Permutation t1 t2 -> type_pexp qenv env e (Ses t1) -> type_pexp qenv env e (Ses t2).

