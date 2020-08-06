Require Import Bool.
Require Import Lists.List.
Import List.ListNotations.
Require Import Arith.
Require Import Arith.EqNat.

(* Field identifiers, which are fields with De Bruijn index names (nat) *)
Inductive ID : Type :=
  identifier : nat -> ID.
Notation "'Id' i" := (identifier i) (at level 1) : core_scope.

(* define x y and z as IDs for use in examples, with customizable units *)
Definition x := identifier 0.
Definition y := identifier 1.
Definition z := identifier 2.
Hint Unfold x : pUnitsHintDatabase.
Hint Unfold y : pUnitsHintDatabase.
Hint Unfold z : pUnitsHintDatabase.

(* Lemmas for ID equality and inequality, as well as simplification lemmas for subsequent proofs *)
(* ID equality is decideable *)
Theorem id_eq_dec : forall id1 id2 : ID, {id1 = id2} + {id1 <> id2}.
Proof.
  intros id1 id2.
  destruct id1 as [n1]; destruct id2 as [n2].
  destruct (eq_nat_dec n1 n2) as [HnEQ | HnNEQ]; subst;
    try (left; reflexivity);
    try (right; intros contra; inversion contra; subst; contradiction).
Qed.

Theorem id_eq_true :
  forall (T:Type) (id : ID) (p q : T),
  (if id_eq_dec id id then p else q) = p.
Proof.
  intros.
  destruct id_eq_dec.
  (* Case "i = i" *)
    reflexivity.
  (* Case "i <> j" *)
    contradiction.
Qed.

Theorem id_eq_false :
  forall (T:Type) (id1 id2 : ID) (p q : T),
    id1 <> id2 ->
    (if id_eq_dec id1 id2 then p else q) = q.
Proof.
  intros.
  destruct id_eq_dec.
  (* Case "i = y" *)
    contradiction.
  (* Case "i <> y" *)
    reflexivity.
Qed.

Definition id_beq id1 id2 :=
  if id_eq_dec id1 id2 then true else false.
Hint Unfold id_beq : pUnitsHintDatabase.

Theorem id_beq_refl : forall id, id_beq id id = true.
Proof.
  intros. unfold id_beq. apply id_eq_true.
Qed.

Theorem id_beq_trans : forall id1 id2 id3,
  id_beq id1 id2 = true ->
  id_beq id2 id3 = true ->
  id_beq id1 id3 = true.
Proof.
  intros id1 id2 id3.
  unfold id_beq. intros Hid12 Hid23.
  destruct id_eq_dec;
  destruct id_eq_dec;
  destruct id_eq_dec;
  try reflexivity;
  try (subst; contradiction);
  try assumption.
Qed.

Theorem id_beq_true : forall (T:Type) (id : ID) (p q : T),
  (if id_beq id id then p else q) = p.
Proof.
  intros.
  unfold id_beq.
  rewrite -> id_eq_true. reflexivity.
Qed.

Theorem id_beq_false : forall (T:Type) (id1 id2 : ID) (p q : T),
  id1 <> id2 ->
  (if id_beq id1 id2 then p else q) = q.
Proof.
  intros.
  unfold id_beq.
  rewrite -> id_eq_false. reflexivity. apply H.
Qed.
