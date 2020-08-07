Require Import Bool.
Require Import Lists.List.
Import List.ListNotations.
Require Import Lists.ListSet.
Require Import Arith.
Require Import Arith.EqNat.
Require Import Strings.String.
Open Scope string_scope.
Open Scope core_scope.

From PUnits Require Import TacticalLemmas.
From PUnits Require Import Units.
From PUnits Require Import Subtyping.
From PUnits Require Import UnitsArithmetics.
From PUnits Require Import IDs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import Gamma.
From PUnits Require Import StackFrame.
From PUnits Require Import GammaStackFrameCorrespondence.
From PUnits Require Import VarDecls.
From PUnits Require Import Expressions.
From PUnits Require Import Statements.

(* Program P in the language. *)
Inductive Program : Type :=
  | program : Variable_Declarations -> Statements -> Program.
Tactic Notation "prog_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "program"
  ].
Hint Constructors Program : pUnitsHintDatabase.

Notation "{ vds s }" := (program vds s) (at level 1).

(* ======================================================= *)
Reserved Notation "'prog:' g '|-' p 'in' post_gamma" (at level 40).
Inductive prog_has_type : Gamma -> Program -> Gamma -> Prop :=
  | T_Program : forall (g post_gamma : Gamma) (vds : Variable_Declarations) (s : Statements),
    vds: g |- vds in post_gamma ->
    stmt: post_gamma |- s ->
    prog: g |- program vds s in post_gamma
where "'prog:' g '|-' p 'in' post_gamma" := (prog_has_type g p post_gamma).
Tactic Notation "prog_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Program"
  ].
Hint Constructors prog_has_type : pUnitsHintDatabase.

(* ======================================================= *)
Reserved Notation " p1 'prog==>' p2 " (at level 8).
Inductive prog_small_step : prod StackFrame Program -> prod StackFrame Program -> Prop :=
  | ST_PROG_VarDecl_Step : forall (f f' : StackFrame) (vds vds' : Variable_Declarations) (s : Statements),
    ( f, vds ) vds==> ( f', vds' ) ->
    ( f, program vds s ) prog==> ( f', program vds' s )
  | ST_PROG_Statements_Step : forall (f f' : StackFrame) (s s' : Statements),
    ( f, s ) stmt==> ( f', s' ) ->
    ( f, program VD_Empty s ) prog==> ( f', program VD_Empty s' )
where " p1 'prog==>' p2 " := (prog_small_step p1 p2).
Tactic Notation "prog_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PROG_VarDecl_Step"
  | Case_aux c "ST_PROG_Statements_Step"
  ].
Hint Constructors prog_small_step : pUnitsHintDatabase.

(* ======================================================= *)
(* step is deterministic *)
Theorem prog_small_step_deterministic:
  forall (p p1 p2 : prod StackFrame Program),
    p prog==> p1 ->
    p prog==> p2 ->
    p1 = p2.
Proof.
  intros p p1 p2 Hp1.
  generalize dependent p2.
  prog_small_step_cases (induction Hp1) Case.
  Case "ST_PROG_VarDecl_Step".
    intros p2 Hp2; inversion Hp2; subst.
      assert ((f', vds') = (f'0, vds'0)) as HvdsEQ. eapply vds_small_step_deterministic.
        apply H. apply H4. inversion HvdsEQ; subst. reflexivity.
      inversion H.
  Case "ST_PROG_Statements_Step".
    intros p2 Hp2; inversion Hp2; subst.
      inversion H4.
      assert ((f', s') = (f'0, s'0)) as HsEQ. eapply stmt_small_step_deterministic.
        apply H. apply H3. inversion HsEQ; subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive prog_normal_form : Program -> Prop :=
  | V_PROG_NF : prog_normal_form (program VD_Empty STMT_Empty).

(* ======================================================= *)
Theorem prog_progress : forall (g1 g2 : Gamma) (f : StackFrame) (p : Program),
  prog: g1 |- p in g2 ->
  gf: g2 |- f OK ->
  prog_normal_form p \/ exists (f' : StackFrame) (p' : Program), (f, p) prog==> (f', p').
Proof.
  (* by induction on typing of prog *)
  intros g1 g2 f p HT HGF.
  prog_has_type_cases (induction HT) Case; subst.
  Case "T_Program".
    assert (VD_Normal_Form vds \/ exists (f' : StackFrame) (vds' : Variable_Declarations), (f, vds) vds==> (f', vds')).
      eapply vds_progress. apply H.
    assert (STMT_Normal_Form s \/ exists (f' : StackFrame) (s' : Statements), (f, s) stmt==> (f', s')).
      eapply stmt_progress. apply H0. apply HGF.
    destruct H1; subst.
    (* Case : vds is normal form *)
      destruct H2; subst.
      (* Case : STMT is normal form *)
        destruct H1; subst. destruct H2; subst. left. apply V_PROG_NF.
      (* Case : STMT can take a step *)
        destruct H1; subst. right. destruct H2 as [f']. destruct H1 as [s'].
        exists f'. exists (program VD_Empty s').
        apply ST_PROG_Statements_Step. apply H1.
    (* Case : vds can take a step *)
      destruct H1 as [f']. destruct H1 as [vds']. right.
      exists f'. exists (program vds' s).
      apply ST_PROG_VarDecl_Step. apply H1.
Qed.

(* ======================================================= *)

Definition Gamma_Extend_Prog (g : Gamma) (p : Program) : Gamma :=
  match p with
  | program vds s => Gamma_Extend_Variables g vds
  end.

(* ======================================================= *)
Theorem prog_preservation : forall (g post_gamma : Gamma) (f f' : StackFrame) (p p' : Program),
  prog: g |- p in post_gamma ->
  gf: post_gamma |- f OK ->
  (f, p) prog==> (f', p') ->
  gf: post_gamma |- f' OK /\ prog: (Gamma_Extend_Prog g p) |- p' in post_gamma.
Proof.
  (* by induction on typing of program *)
  intros g post_gamma f f' p p' HT HGF HS.
  (* we prove for programs typed starting from empty gamma, rather than all
     possible gamma *)
  remember empty_gamma as Gamma.
  generalize dependent p'. generalize dependent f'.
  prog_has_type_cases (induction HT) Case; intros f' p' HS; subst.
  Case "T_Program".
    destruct p' as [vds' s'].
    prog_small_step_cases (inversion HS) SCase; subst.
    SCase "ST_PROG_VarDecl_Step".
      inversion H2; subst.
      unfold Gamma_Extend_Prog. simpl.
      eapply vds_preservation in H.
      destruct H.
        split.
        (* first prove that post_gamma |- f' OK *)
          apply H.
        (* then prove that prog: (Gamma_Extend_Prog empty_gamma p) |- p' in post_gamma. *)
          apply T_Program.
            apply H1.
            apply H0.
        apply HGF.
        apply H2.
    SCase "ST_PROG_Statements_Step".
      (* in statement step, the input gamma to type check p' does not change *)
      simpl. eapply stmt_preservation in H0.
        split.
        (* first prove that post_gamma |- f' OK *)
          apply H0.
        (* then prove that prog: g |- {VD_Empty s'} in post_gamma *)
          apply T_Program.
            apply H.
            apply H0.
        apply HGF.
        apply H2.
Qed.
