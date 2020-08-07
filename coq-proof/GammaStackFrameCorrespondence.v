From PUnits Require Import UnitsDefs.
From PUnits Require Import SubtypingDefs.
From PUnits Require Import IDDefs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import GammaDefs.
From PUnits Require Import StackFrame.

(* ======================================================= *)

(* If gamma contains a field f, then there exists Tv and Tf such that Tv <: Tf,
    and Gamma(f) = FieldType(h, f) = Tf, FieldValue(h, f) = Tv z for some z. *)

Reserved Notation "'gh:' g '|-' h 'OK'" (at level 40).
Inductive Gamma_StackFrame_OK : Gamma -> StackFrame -> Prop :=
  | GH_Correspondence : forall (g : Gamma) (h : StackFrame),
    ( forall (f : ID), Gamma_Contains g f = true ->
      exists (Tf Tv : Unit) (z : nat),
        Gamma_Get g f = Some Tf /\
        FieldType h f = Some Tf /\
        Tv <: Tf = true /\
        FieldValue h f = Some (Val Tv z) ) ->
    gh: g |- h OK
where "'gh:' g '|-' h 'OK'" := (Gamma_StackFrame_OK g h).
