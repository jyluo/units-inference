Require Import Bool.
Require Import Lists.List.
Import List.ListNotations.
Require Import Arith.
Require Import Arith.EqNat.

From PUnits Require Import UnitsDefs.

(* Values, which are numbers that are labeled with a Unit *)
Inductive Value : Type :=
  Val : Unit -> nat -> Value.

Definition Value_GetUnit (v : Value) : Unit :=
  match v with
  | Val u _ => u
  end.

Definition Value_GetNumber (v : Value) : nat :=
  match v with
  | Val _ z => z
  end.

(* Lemmas for Value equality and inequality, as well as simplification lemmas for subsequent proofs *)
(* Value equality is decideable *)
Theorem Value_eq_dec : forall v1 v2 : Value, {v1 = v2} + {v1 <> v2}.
Proof.
  intros v1 v2.
  destruct v1 as [u1 n1]; destruct v2 as [u2 n2].
  destruct (unit_eq_dec u1 u2) as [HuEQ | HuNEQ]; destruct (eq_nat_dec n1 n2) as [HnEQ | HnNEQ]; subst;
    try (left; reflexivity);
    try (right; intros contra; inversion contra; subst; contradiction).
Qed.

Theorem Value_eq_true :
  forall (T:Type) (v : Value) (p q : T),
  (if Value_eq_dec v v then p else q) = p.
Proof.
  intros.
  destruct Value_eq_dec.
  (* Case "i = i" *)
    reflexivity.
  (* Case "i <> j" *)
    contradiction.
Qed.

Theorem Value_eq_false :
  forall (T:Type) (v1 v2 : Value) (p q : T),
    v1 <> v2 ->
    (if Value_eq_dec v1 v2 then p else q) = q.
Proof.
  intros.
  destruct (Value_eq_dec).
  (* Case "i = y" *)
    contradiction.
  (* Case "i <> y" *)
    reflexivity.
Qed.

Definition Value_beq v1 v2 :=
  if Value_eq_dec v1 v2 then true else false.
Hint Unfold Value_beq : pUnitsHintDatabase.

Theorem Value_beq_refl : forall v, Value_beq v v = true.
Proof.
  intros. unfold Value_beq. apply Value_eq_true.
Qed.

Theorem Value_beq_trans : forall v1 v2 v3,
  Value_beq v1 v2 = true ->
  Value_beq v2 v3 = true ->
  Value_beq v1 v3 = true.
Proof.
  intros v1 v2 v3.
  unfold Value_beq. intros Hv12 Hv23.
  destruct Value_eq_dec;
  destruct Value_eq_dec;
  destruct Value_eq_dec;
  try reflexivity;
  try (subst; contradiction);
  try assumption.
Qed.
