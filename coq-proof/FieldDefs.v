Require Import Strings.String.
Open Scope string_scope.
Open Scope core_scope.

From PUnits Require Import TacticalLemmas.
From PUnits Require Import UnitsDefs.
From PUnits Require Import SubtypingDefs.
From PUnits Require Import IDDefs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import GammaDefs.
From PUnits Require Import StackFrame.
From PUnits Require Import GammaStackFrameCorrespondence.

(* ======================================================= *)
Inductive Field_Declarations : Type :=
  | FD_Empty : Field_Declarations
  | FD_Decl : Unit -> ID -> nat -> Field_Declarations -> Field_Declarations.
Tactic Notation "fds_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "FD_Empty"
  | Case_aux c "FD_Decl"
  ].
Hint Constructors Field_Declarations : pUnitsHintDatabase.

(* ======================================================= *)
Reserved Notation "'fds:' g1 '|-' fds 'in' g2" (at level 40).
Inductive fds_has_type : Gamma -> Field_Declarations -> Gamma -> Prop :=
  | T_FD_Empty : forall (g : Gamma),
    fds: g |- FD_Empty in g
  | T_FD : forall (g1 g2 : Gamma) (tail : Field_Declarations) (T : Unit) (f : ID) (z : nat),
    Gamma_Contains g1 f = false ->
    Gamma_Contains g2 f = true ->
    Gamma_Get g2 f = Some T ->
    fds: Gamma_Extend g1 f T |- tail in g2 ->
    fds: g1 |- FD_Decl T f z tail in g2
where "'fds:' g1 '|-' fds 'in' g2" := (fds_has_type g1 fds g2).
Tactic Notation "fds_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_FD_Empty"
  | Case_aux c "T_FD"
  ].
Hint Constructors fds_has_type : pUnitsHintDatabase.

(* ======================================================= *)
Reserved Notation " fds1 'fds==>' fds2 " (at level 8).
Inductive fds_small_step : prod StackFrame Field_Declarations -> prod StackFrame Field_Declarations -> Prop :=
  | ST_FD : forall (h : StackFrame) (T : Unit) (f : ID) (z : nat) (fds : Field_Declarations),
    ( h, FD_Decl T f z fds ) fds==> ( (StackFrame_Update h f T T z), fds )
where " fds1 'fds==>' fds2 " := (fds_small_step fds1 fds2).
Tactic Notation "fds_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_FD"
  ].
Hint Constructors fds_small_step : pUnitsHintDatabase.

(* ======================================================= *)
(* step is deterministic *)
Theorem fds_small_step_deterministic:
  forall fds fds1 fds2,
    fds fds==> fds1 ->
    fds fds==> fds2 ->
    fds1 = fds2.
Proof.
  intros fds fds1 fds2 Hfds1.
  generalize dependent fds2.
  fds_small_step_cases (induction Hfds1) Case.
  Case "ST_FD".
    intros fds2 Hfds2.
    inversion Hfds2; subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive FD_Normal_Form : Field_Declarations -> Prop :=
  | V_FD_Empty : FD_Normal_Form FD_Empty.

(* ======================================================= *)
Theorem fds_progress : forall (g1 g2 : Gamma) (h : StackFrame) (fds : Field_Declarations),
  fds: g1 |- fds in g2 ->
  FD_Normal_Form fds \/ exists h' fds', (h, fds) fds==> (h', fds').
Proof.
  (* by induction on typing of fds *)
  intros g1 g2 h fds HT.
  fds_has_type_cases (induction HT) Case; subst.
  Case "T_FD_Empty".
    left. apply V_FD_Empty.
  Case "T_FD".
    right.
    destruct IHHT.
      inversion H2. exists (StackFrame_Update h f T T z). exists FD_Empty. apply ST_FD.
      exists (StackFrame_Update h f T T z). exists tail. apply ST_FD.
Qed.

(* ======================================================= *)

(* Extends g with the first field declaration in fds, or returns g unchanged if fds is empty *)
Definition Gamma_Extend_Fields (g : Gamma) (fds : Field_Declarations) : Gamma :=
  match fds with
  | FD_Decl T f z fds => Gamma_Extend g f T
  | FD_Empty => g
  end.

(* ======================================================= *)

Theorem fds_preservation : forall (g1 g2 : Gamma) (h h' : StackFrame) (fds fds' : Field_Declarations),
  fds: g1 |- fds in g2 ->
  gh: g2 |- h OK ->
  (h, fds) fds==> (h', fds') ->
  gh: g2 |- h' OK /\ fds: Gamma_Extend_Fields g1 fds |- fds' in g2.
Proof.
  intros g1 g2 h h' fds fds' HT HGH HS.
  generalize dependent fds'. generalize dependent h'.
  fds_has_type_cases (induction HT) Case; intros h' fds' HS; subst.
  Case "T_FD_Empty".
    inversion HS.
  Case "T_FD".
    inversion HS; subst.
    split.
    (* first prove that g2 |- h' OK *)
      apply GH_Correspondence.
      intros f' HGf'.
      inversion HGH; subst.
      destruct H2 with f' as [Tf']. apply HGf'. clear H2. destruct H3 as [Tv']. destruct H2 as [z']. Tactics.destruct_pairs.
      destruct (id_eq_dec f' f); subst.
      (* Case: f = f' : in h', the value of f' is T T z *)
        exists T, T, z.
        assert (T = Tf'). eapply Gamma_Get_Content_Eq. apply H1. apply H2. subst.
        split. apply H1.
        split. apply StackFrame_Update_VarType_Eq.
        split. apply subtype_reflexive.
        apply StackFrame_Update_VarValue_Eq.
      (* Case: f <> f' : in h' the value of f' is some Tv' z' *)
        exists Tf', Tv', z'.
        split. apply H2.
        split. rewrite <- H3. apply StackFrame_Update_VarType_Neq. apply n.
        split. apply H4.
        rewrite <- H5. apply StackFrame_Update_VarValue_Neq. apply n.
    (* then prove that fds: Gamma_Extend g1 f T |- fds' in g2 *)
      simpl. apply HT.
Qed.
