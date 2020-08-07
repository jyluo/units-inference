From PUnits Require Import Units.
From PUnits Require Import Subtyping.
From PUnits Require Import IDs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import Gamma.
From PUnits Require Import StackFrame.

(* ======================================================= *)

(* If gamma g contains a variable v, then there exists Tl and Tv such that
Tl <: Tv,
Gamma(v) = VarType(f, v) = Tv, and
VarValue(f, v) = Tl z for some z. *)

Reserved Notation "'gf:' g '|-' f 'OK'" (at level 40).
Inductive Gamma_StackFrame_OK : Gamma -> StackFrame -> Prop :=
  | GF_Correspondence : forall (g : Gamma) (f : StackFrame),
    ( forall (v : ID), Gamma_Contains g v = true ->
      exists (Tv Tl : Unit) (z : nat),
        Gamma_Get g v = Some Tv /\
        VarType f v = Some Tv /\
        Tl <: Tv = true /\
        VarValue f v = Some (Lit Tl z) ) ->
    gf: g |- f OK
where "'gf:' g '|-' f 'OK'" := (Gamma_StackFrame_OK g f).
