Require Import UnitsDefs.
Require Import SubtypingDefs.
Require Import IDDefs.
Require Import ValueDefs.
Require Import GammaDefs.
Require Import HeapDefs.

(* ======================================================= *)

Reserved Notation "'gh:' g '|-' h 'OK'" (at level 40).
Inductive Gamma_Heap_OK : Gamma -> Heap -> Prop :=
  | GH_Correspondence : forall (g : Gamma) (h : Heap),
    ( forall (f : ID), Gamma_Contains g f = true /\
      exists (Tf Tv : Unit) (z : nat),
      Gamma_Get g f = Some Tf /\ FieldType h f = Tf /\ Tv <: Tf = true /\ FieldValue h f = Val Tv z ) ->
    gh: g |- h OK
where "'gh:' g '|-' h 'OK'" := (Gamma_Heap_OK g h).
