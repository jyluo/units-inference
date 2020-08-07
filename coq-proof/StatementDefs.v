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
From PUnits Require Import UnitsDefs.
From PUnits Require Import SubtypingDefs.
From PUnits Require Import IDDefs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import GammaDefs.
From PUnits Require Import StackFrame.
From PUnits Require Import GammaStackFrameCorrespondence.
From PUnits Require Import ExpressionDefs.

(* ======================================================= *)
Inductive Statements : Type :=
  | STMT_Empty : Statements
  | STMT_Assign : ID -> Expression -> Statements -> Statements. (* f = e ; s *)
Tactic Notation "stmt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STMT_Empty"
  | Case_aux c "STMT_Assign"
  ].
Hint Constructors Statements : pUnitsHintDatabase.

(* ======================================================= *)
Reserved Notation "'stmt:' g '|-' s " (at level 40).
Inductive stmt_has_type : Gamma -> Statements -> Prop :=
  | T_STMT_Empty : forall (g : Gamma),
    stmt: g |- STMT_Empty
  | T_STMT_Assign : forall (g : Gamma) (f : ID) (Tf Te : Unit) (e : Expression) (s2 : Statements),
    Gamma_Contains g f = true ->
    Gamma_Get g f = Some Tf ->
    Te <: Tf = true ->
    expr: g |- e in Te ->
    stmt: g |- s2 ->
    stmt: g |- STMT_Assign f e s2
where "'stmt:' g '|-' s "  := (stmt_has_type g s).
Tactic Notation "stmt_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_STMT_Empty"
  | Case_aux c "T_STMT_Assign"
  ].
Hint Constructors stmt_has_type : pUnitsHintDatabase.

(* ======================================================= *)

Reserved Notation " s1 'stmt==>' s2 " (at level 8).
Inductive stmt_small_step : prod StackFrame Statements -> prod StackFrame Statements -> Prop :=
  | ST_STMT_Assign_Lit : forall (h : StackFrame) (f : ID) (Tf Tv : Unit) (z : nat) (s2 : Statements),
    VarType h f = Some Tf ->
    Tv <: Tf = true ->
    ( h, STMT_Assign f (E_Value (Lit Tv z)) s2 ) stmt==> ( (StackFrame_Update h f Tf Tv z), s2 )
  | ST_STMT_Assign_Exp : forall (h : StackFrame) (f : ID) (e e' : Expression) (s2 : Statements),
    ( h, e ) expr==> e' ->
    ( h, STMT_Assign f e s2 ) stmt==> ( h, STMT_Assign f e' s2 )
where " s1 'stmt==>' s2 " := (stmt_small_step s1 s2).
Tactic Notation "stmt_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_STMT_Assign_Val"
  | Case_aux c "ST_STMT_Assign_Exp"
  ].
Hint Constructors stmt_small_step : pUnitsHintDatabase.

(* ======================================================= *)
(* step is deterministic *)
Theorem stmt_small_step_deterministic:
  forall (s s1 s2 : prod StackFrame Statements),
    s stmt==> s1 ->
    s stmt==> s2 ->
    s1 = s2.
Proof.
  intros s s1 s2 Hs1 Hs2.
  generalize dependent s2.
  stmt_small_step_cases (induction Hs1) Case.
  Case "ST_STMT_Assign_Val".
    intros s3 Hs3; inversion Hs3; subst.
      assert (Tf = Tf0). eapply VarType_Content_Eq; eauto. subst. reflexivity.
      inversion H6.
  Case "ST_STMT_Assign_Exp".
    intros s3 Hs3; inversion Hs3; subst.
      inversion H.
      assert (e' = e'0). apply expr_small_step_deterministic with h e; eauto. subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive STMT_Normal_Form : Statements -> Prop :=
  | V_STMT_Value : STMT_Normal_Form STMT_Empty.

(* ======================================================= *)
Theorem stmt_progress : forall (g : Gamma) (h : StackFrame) (s : Statements),
  stmt: g |- s ->
  gh: g |- h OK ->
  STMT_Normal_Form s \/ exists (h' : StackFrame) (s' : Statements), (h, s) stmt==> (h', s').
Proof.
  intros g h s HT HGH.
  stmt_has_type_cases (induction HT) Case; subst.
  Case "T_STMT_Empty".
    left. apply V_STMT_Value.
  Case "T_STMT_Assign".
    (* Case: f = e *)
    right.
    inversion HGH; subst.
    destruct H3 with f as [Tf']. apply H. clear H3. destruct H4 as [Tv']. destruct H3 as [z']. Tactics.destruct_pairs.
    assert (Tf = Tf'). eapply Gamma_Get_Content_Eq; eauto. subst.
    assert (expr_normal_form e \/ exists e', (h, e) expr==> e'). apply expr_progress with g Te. apply H2. apply HGH.
    inversion H7; subst.
    (* Subcase: e is a value -> step by ST_STMT_Assign_Lit *)
      destruct H8; subst. inversion H2; subst. exists (StackFrame_Update h f Tf' Te z), s2.
      eapply ST_STMT_Assign_Val.
        apply H4.
        apply H1.
    (* Subcase : e can take a step -> step by ST_STMT_Assign_Exp *)
      destruct H8 as [e']; subst. exists h, (STMT_Assign f e' s2). apply ST_STMT_Assign_Exp. apply H8.
Qed.

(* ======================================================= *)
Theorem stmt_preservation : forall (g : Gamma) (s s' : Statements) (h h' : StackFrame),
  stmt: g |- s ->
  gh: g |- h OK ->
  (h, s) stmt==> (h', s') ->
  gh: g |- h' OK /\ stmt: g |- s'.
Proof.
  (* by induction on typing of stmts *)
  intros g s s' h h' HT HGH HS.
  generalize dependent s'. generalize dependent h'.
  stmt_has_type_cases (induction HT) Case; intros h' s' HS; subst.
  Case "T_STMT_Empty".
    inversion HS. (* empty stmt list does not step *)
  Case "T_STMT_Assign". (* s :=  f = e ; s2 *)
    stmt_small_step_cases (inversion HS) SCase; subst.
    SCase "ST_STMT_Assign_Val". (* f = v ; s2 *)
      split.
      (* first prove that g |- h' OK *)
        inversion H2; subst.
        apply GH_Correspondence.
        intros f' HGf'.
        inversion HGH; subst.
        destruct H3 with f' as [Tf']. apply HGf'. clear H3. destruct H4 as [Tv']. destruct H3 as [z']. Tactics.destruct_pairs.
        destruct (id_eq_dec f' f).
        (* Case: f = f' : in h', the value of f' is Tf Te z *)
          exists Tf, Te, z. rewrite -> e in H3.
          assert (Tf = Tf'). eapply Gamma_Get_Content_Eq; eauto. subst.
          assert (Tf' = Tf0). eapply VarType_Content_Eq; eauto. subst.
          split. apply H3.
          split. apply StackFrame_Update_VarType_Eq.
          split. apply H1.
          apply StackFrame_Update_VarValue_Eq.
        (* Case: f <> f' : in h' the value of f' is some Tf' Tv' z' *)
          exists Tf', Tv', z'. subst.
          split. apply H3.
          split. rewrite <- H4. apply StackFrame_Update_VarType_Neq. apply n.
          split. apply H6.
          rewrite <- H7. apply StackFrame_Update_VarValue_Neq. apply n.
      (* then prove that g |- s' *)
        apply HT.
    SCase "ST_STMT_Assign_Exp". (* f = e ; s2 , e --> e' *)
      split.
      (* first prove that g |- h' OK *)
        apply HGH.
      (* then prove that g |- f = e' ; s2 *)
        eapply expr_preservation in H2.
          destruct H2 as [T']. destruct H2.
          eapply T_STMT_Assign.
            apply H.
            apply H0.
            apply subtype_transitive with Te.
              apply H2. apply H1.
            apply H3.
            apply HT.
          apply HGH.
          apply H4.
Qed.
