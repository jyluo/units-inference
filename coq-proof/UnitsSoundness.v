Require Import Bool.
Require Import Lists.List.
Import List.ListNotations.
Require Import Lists.ListSet.
Require Import Arith.
Require Import Arith.EqNat.
Require Import Strings.String. Open Scope string_scope.
Open Scope core_scope.

Require Import TacticalLemmas.
Require Import UnitsDefs.
Require Import SubtypingDefs.
Require Import UnitsArithmetics.
Require Import IDDefs.
Require Import ValueDefs.
Require Import GammaDefs.
Require Import HeapDefs.
Require Import FieldsDefs.
Require Import ExpressionsDefs.
Require Import StatementDefs.
Require Import ProgramDefs.

(* ======================================================= *)

Definition relation (X:Type) := X -> X -> Prop.

(* a program p is in normal for if there does not exist an p' that p can step to *)
Definition normal_form {X:Type} (R:relation X) (p:X) : Prop :=
  ~ exists p', R p p'.

Notation step_normal_form := (normal_form prog_small_step).

Definition value (hp : prod Heap Program) : Prop :=
  match hp with
  | (_, p) => prog_normal_form p
  end.

Definition stuck (hp : prod Heap Program) : Prop :=
  step_normal_form hp /\ ~ value hp.

Hint Unfold stuck.

(* multi step is defined as the transitive closure of step *)
Inductive multi (X:Type) (R: relation X) : X -> X -> Prop :=
  | multi_refl : forall (x : X),
                 multi X R x x
  | multi_step : forall (x y z : X),
                 R x y ->
                 multi X R y z ->
                 multi X R x z.
Implicit Arguments multi [[X]].
Tactic Notation "multi_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl"
  | Case_aux c "multi_step"
  ].
Hint Constructors multi.

Definition multistep := (multi prog_small_step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Theorem soundness : forall (g : Gamma) (p p' : Program) (h h' : Heap),
  prog: empty_gamma |- p in g ->
  gh: g |- h OK ->
  (h, p) ==>* (h', p') ->
  ~(stuck (h', p')).
Proof with auto.
  (* by induction on (empty_heap, p) ==>* (h', p') *)
  intros g p p' h h' HT HGH HMS [HSNF HV].
  unfold normal_form in HSNF.
  unfold value in HV.
  multi_step_cases (induction HMS) Case.
  (* From hypothesis, we have that p is well typed. *)
  Case "multi_refl".
    (* If p ==>* p' via multi_refl, then p == p'.
       since e is well typed, by progress theorem, either e is a value or must take a step. *)
    eapply prog_progress in HT. destruct HT.
      (* If e is a value, then e' is also a value and e' is not stuck *)
      contradiction HV.
      (* If e can take a step, then e' can also take a step and e' is not stuck *)
      contradiction H.
  Case "multi_step".
    (* If e ==>* e' via multi_step, then e ==> y and y ==>* e'.
       From inductive hypothesis, if y is well typed then e' is not stuck *)
    apply IHHMS...
      (* Since e is well typed and e ==> y, by preservation lemma, y is well typed, thus e' is not stuck *)
      apply (prog_preservation e y T U HT H).
Qed.

