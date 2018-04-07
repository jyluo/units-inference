Require Import UnitsDefs.
Require Import SubtypingDefs.
Require Import IDDefs.
Require Import ValueDefs.
Require Import GammaDefs.
Require Import HeapDefs.

(* ======================================================= *)

Reserved Notation "'gh:' g '|-' h 'OK'" (at level 40).
Inductive Gamma_Heap_OK : Gamma -> Heap -> Prop :=
  | GH_Correspond : forall (g : Gamma) (h : Heap),
    ( forall (f : ID) (Tf : Unit), Gamma_Contains g f = true /\ Gamma_Get g f = Some Tf /\
      exists (Tv : Unit) (z : nat),
      FieldType h f = Tf /\ FieldValue h f = Val Tv z /\ Tv <: Tf = true ) ->
    gh: g |- h OK
where "'gh:' g '|-' h 'OK'" := (Gamma_Heap_OK g h).

