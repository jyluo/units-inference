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
Require Import GammaHeapCorrespondence.
Require Import FieldsDefs.
Require Import ExpressionsDefs.
Require Import StatementDefs.

(* ======================================================= *)
Inductive Program : Type :=
  | program : Field_Declaration -> Statement -> Program.
Tactic Notation "prog_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "program"
  ].
Hint Constructors Program.

Notation "{ fd s }" := (program fd s) (at level 1).

(* ======================================================= *)
Reserved Notation "'prog:' g '|-' p 'in' post_gamma" (at level 40).
Inductive prog_has_type : Gamma -> Program -> Gamma -> Prop :=
  | T_Program : forall (g post_gamma : Gamma) (fd : Field_Declaration) (s : Statement),
    fd: g |- fd in post_gamma ->
    stmt: post_gamma |- s ->
    prog: g |- program fd s in post_gamma
where "'prog:' g '|-' p 'in' post_gamma" := (prog_has_type g p post_gamma).
Tactic Notation "prog_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Program"
  ].
Hint Constructors prog_has_type.

(* ======================================================= *)
Reserved Notation " p1 'prog==>' p2 " (at level 8).
Inductive prog_small_step : prod Heap Program -> prod Heap Program -> Prop :=
  | ST_PROG_FieldDefs_Step : forall h h' fd fd' s,
    ( h, fd ) fd==> ( h', fd' ) ->
    ( h, program fd s ) prog==> ( h', program fd' s )
  | ST_PROG_Statements_Step : forall h h' s s',
    ( h, s ) stmt==> ( h', s' ) ->
    ( h, program FD_Empty s ) prog==> ( h', program FD_Empty s' )
where " p1 'prog==>' p2 " := (prog_small_step p1 p2).
Tactic Notation "prog_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PROG_FieldDefs_Step"
  | Case_aux c "ST_PROG_Statements_Step"
  ].
Hint Constructors prog_small_step.

(* ======================================================= *)
(* step is deterministic *)
Theorem prog_small_step_deterministic:
  forall p p1 p2,
    p prog==> p1 ->
    p prog==> p2 ->
    p1 = p2.
Proof.
  intros p p1 p2 Hp1.
  generalize dependent p2.
  prog_small_step_cases (induction Hp1) Case.
  Case "ST_PROG_FieldDefs_Step".
    intros p2 Hp2; inversion Hp2; subst.
      assert ((h', fd') = (h'0, fd'0)) as HfdEQ. eapply fd_small_step_deterministic.
        apply H. apply H4. inversion HfdEQ; subst. reflexivity.
      inversion H.
  Case "ST_PROG_Statements_Step".
    intros p2 Hp2; inversion Hp2; subst.
      inversion H4.
      assert ((h', s') = (h'0, s'0)) as HsEQ. eapply stmt_small_step_deterministic.
        apply H. apply H3. inversion HsEQ; subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive prog_normal_form : Program -> Prop :=
  | V_PROG_NF : prog_normal_form (program FD_Empty STMT_Empty).

(* ======================================================= *)
Theorem prog_progress : forall (g1 g2 : Gamma) (p : Program) (h : Heap),
  prog: g1 |- p in g2 ->
  gh: g2 |- h OK ->
  prog_normal_form p \/ exists (h' : Heap) (p' : Program), (h, p) prog==> (h', p').
Proof.
  (* by induction on typing of prog *)
  intros g1 g2 p h HT HGH.
  prog_has_type_cases (induction HT) Case; subst.
  Case "T_Program".
    assert (FD_Normal_Form fd \/ exists heap' fd', (h, fd) fd==> (heap', fd')).
      eapply fd_progress. apply H.
    assert (STMT_Normal_Form s \/ exists (h' : Heap) (s' : Statement), (h, s) stmt==> (h', s')).
      eapply stmt_progress. apply H0. apply HGH.
    destruct H1; subst.
    (* Case : FD is normal form *)
      destruct H2; subst.
      (* Case : STMT is normal form *)
        destruct H1; subst. destruct H2; subst. left. apply V_PROG_NF.
      (* Case : STMT can take a step *)
        destruct H1; subst. right. destruct H2 as [h']. destruct H1 as [s'].
        exists h'. exists (program FD_Empty s').
        apply ST_PROG_Statements_Step. apply H1.
    (* Case : FD can take a step *)
      destruct H1 as [h']. destruct H1 as [fd']. right.
      exists h'. exists (program fd' s).
      apply ST_PROG_FieldDefs_Step. apply H1.
Qed.

(* ======================================================= *)

Definition Gamma_Extend_Prog (g : Gamma) (p : Program) : Gamma :=
  match p with
  | program fd s => match First_FD fd with
                    | Some (T, f, z) => Gamma_Extend g f T
                    | None => g
                    end
  end.

(* ======================================================= *)
Theorem prog_preservation : forall (post_gamma : Gamma) (h' : Heap) (p p' : Program),
  prog: empty_gamma |- p in post_gamma ->
  gh: post_gamma |- empty_heap OK ->
  (empty_heap, p) prog==> (h', p') ->
  gh: post_gamma |- h' OK /\ prog: (Gamma_Extend_Prog empty_gamma p) |- p' in post_gamma.
Proof.
  (* by induction on typing of program *)
  intros post_gamma h' p p' HT HGH HS.
  (* we prove for programs typed starting from empty gamma, rather than all possible gamma *)
  remember empty_gamma as Gamma.
  generalize dependent p'. generalize dependent h'.
  prog_has_type_cases (induction HT) Case; intros h' p' HS; subst.
  Case "T_Program".
    destruct p' as [fd' s'].
    prog_small_step_cases (inversion HS) SCase; subst.
    SCase "ST_PROG_FieldDefs_Step".
      inversion H2; subst.
      unfold Gamma_Extend_Prog.
      eapply fd_preservation in H.
        split.
        (* first prove that post_gamma |- h' OK *)
          apply H.
        (* then prove that prog: (Gamma_Extend_Prog empty_gamma p) |- p' in post_gamma. *)
          simpl. apply T_Program.
            apply H.
            apply H0.
        apply HGH.
        apply H2.
        simpl. reflexivity.
    SCase "ST_PROG_Statements_Step".
      simpl. (* in statement step, the input gamma to type p' does not change *)
        eapply stmt_preservation in H0.
        split.
        (* first prove that post_gamma |- h' OK *)
          apply H0.
        (* then prove that prog: g |- {FD_Empty s'} in post_gamma *)
          apply T_Program. apply H. apply H0.
        apply HGH.
        apply H2.
Qed.
