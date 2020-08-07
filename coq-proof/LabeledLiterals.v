Require Import Bool.
Require Import Lists.List.
Import List.ListNotations.
Require Import Arith.
Require Import Arith.EqNat.

From PUnits Require Import Units.

(* Labeled literal / labeled value l = T z, which are numbers z that are labeled
with a Unit T. Here we model z as a nat. *)
Inductive LabeledLiteral : Type :=
  Lit : Unit -> nat -> LabeledLiteral.

Definition LabeledLiteral_GetUnit (l : LabeledLiteral) : Unit :=
  match l with
  | Lit u _ => u
  end.

Definition LabeledLiteral_GetNumber (l : LabeledLiteral) : nat :=
  match l with
  | Lit _ z => z
  end.

(* Lemmas for equality, as well as simplification lemmas for subsequent
proofs. *)

(* LabeledLiteral equality is decideable. *)
Theorem LabeledLiteral_eq_dec : forall l1 l2 : LabeledLiteral, {l1 = l2} + {l1 <> l2}.
Proof.
  intros l1 l2.
  destruct l1 as [u1 n1]; destruct l2 as [u2 n2].
  destruct (unit_eq_dec u1 u2) as [HuEQ | HuNEQ]; destruct (eq_nat_dec n1 n2) as [HnEQ | HnNEQ]; subst;
    try (left; reflexivity);
    try (right; intros contra; inversion contra; subst; contradiction).
Qed.

Theorem LabeledLiteral_eq_true :
  forall (T:Type) (l : LabeledLiteral) (p q : T),
  (if LabeledLiteral_eq_dec l l then p else q) = p.
Proof.
  intros.
  destruct LabeledLiteral_eq_dec.
  (* Case "i = i" *)
    reflexivity.
  (* Case "i <> j" *)
    contradiction.
Qed.

Theorem LabeledLiteral_eq_false :
  forall (T:Type) (l1 l2 : LabeledLiteral) (p q : T),
    l1 <> l2 ->
    (if LabeledLiteral_eq_dec l1 l2 then p else q) = q.
Proof.
  intros.
  destruct (LabeledLiteral_eq_dec).
  (* Case "i = y" *)
    contradiction.
  (* Case "i <> y" *)
    reflexivity.
Qed.

Definition LabeledLiteral_beq l1 l2 :=
  if LabeledLiteral_eq_dec l1 l2 then true else false.
Hint Unfold LabeledLiteral_beq : pUnitsHintDatabase.

Theorem LabeledLiteral_beq_refl : forall l, LabeledLiteral_beq l l = true.
Proof.
  intros. unfold LabeledLiteral_beq. apply LabeledLiteral_eq_true.
Qed.

Theorem LabeledLiteral_beq_trans : forall l1 l2 l3,
  LabeledLiteral_beq l1 l2 = true ->
  LabeledLiteral_beq l2 l3 = true ->
  LabeledLiteral_beq l1 l3 = true.
Proof.
  intros l1 l2 l3.
  unfold LabeledLiteral_beq. intros Hl12 Hl23.
  destruct LabeledLiteral_eq_dec;
  destruct LabeledLiteral_eq_dec;
  destruct LabeledLiteral_eq_dec;
  try reflexivity;
  try (subst; contradiction);
  try assumption.
Qed.
