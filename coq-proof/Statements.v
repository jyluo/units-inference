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
From PUnits Require Import IDs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import Gamma.
From PUnits Require Import StackFrame.
From PUnits Require Import GammaStackFrameCorrespondence.
From PUnits Require Import Expressions.

(* Assignment statement s in the language, modeled with an empty statement to
inductively define a sequence of statements. *)
Inductive Statements : Type :=
  | STMT_Empty : Statements
  | STMT_Assign : ID -> Expression -> Statements -> Statements. (* v = e ; s *)
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
  | T_STMT_Assign : forall (g : Gamma) (v : ID) (Tv Te : Unit) (e : Expression) (s2 : Statements),
    Gamma_Contains g v = true ->
    Gamma_Get g v = Some Tv ->
    Te <: Tv = true ->
    expr: g |- e in Te ->
    stmt: g |- s2 ->
    stmt: g |- STMT_Assign v e s2
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
  | ST_STMT_Assign_Lit : forall (f : StackFrame) (v : ID) (Tv Tl : Unit) (z : nat) (s2 : Statements),
    VarType f v = Some Tv ->
    Tl <: Tv = true ->
    ( f, STMT_Assign v (E_LabeledLiteral (Lit Tl z)) s2 ) stmt==> ( (StackFrame_Update f v Tv Tl z), s2 )
  | ST_STMT_Assign_Exp : forall (f : StackFrame) (v : ID) (e e' : Expression) (s2 : Statements),
    ( f, e ) expr==> e' ->
    ( f, STMT_Assign v e s2 ) stmt==> ( f, STMT_Assign v e' s2 )
where " s1 'stmt==>' s2 " := (stmt_small_step s1 s2).
Tactic Notation "stmt_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_STMT_Assign_Lit"
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
  Case "ST_STMT_Assign_Lit".
    intros s3 Hs3; inversion Hs3; subst.
      assert (Tv = Tv0). eapply VarType_Content_Eq; eauto. subst. reflexivity.
      inversion H6.
  Case "ST_STMT_Assign_Exp".
    intros s3 Hs3; inversion Hs3; subst.
      inversion H.
      assert (e' = e'0). apply expr_small_step_deterministic with f e; eauto. subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive STMT_Normal_Form : Statements -> Prop :=
  | V_STMT_Value : STMT_Normal_Form STMT_Empty.

(* ======================================================= *)
Theorem stmt_progress : forall (g : Gamma) (f : StackFrame) (s : Statements),
  stmt: g |- s ->
  gf: g |- f OK ->
  STMT_Normal_Form s \/ exists (f' : StackFrame) (s' : Statements), (f, s) stmt==> (f', s').
Proof.
  intros g f s HT HGF.
  stmt_has_type_cases (induction HT) Case; subst.
  Case "T_STMT_Empty".
    left. apply V_STMT_Value.
  Case "T_STMT_Assign".
    (* Case: v = e *)
    right.
    inversion HGF; subst.
    destruct H3 with v as [Tv']. apply H. clear H3. destruct H4 as [Tl']. destruct H3 as [z']. Tactics.destruct_pairs.
    assert (Tv = Tv'). eapply Gamma_Get_Content_Eq; eauto. subst.
    assert (expr_normal_form e \/ exists e', (f, e) expr==> e'). apply expr_progress with g Te. apply H2. apply HGF.
    inversion H7; subst.
    (* Subcase: e is a labeled value Te z and s takes a step by ST_STMT_Assign_Lit *)
      destruct H8; subst. inversion H2; subst. exists (StackFrame_Update f v Tv' Te z), s2.
      eapply ST_STMT_Assign_Lit.
        apply H4.
        apply H1.
    (* Subcase : e can reduce and s takes a step by ST_STMT_Assign_Exp, reducing e *)
      destruct H8 as [e']; subst. exists f, (STMT_Assign v e' s2). apply ST_STMT_Assign_Exp. apply H8.
Qed.

(* ======================================================= *)
Theorem stmt_preservation : forall (g : Gamma) (s s' : Statements) (f f' : StackFrame),
  stmt: g |- s ->
  gf: g |- f OK ->
  (f, s) stmt==> (f', s') ->
  gf: g |- f' OK /\ stmt: g |- s'.
Proof.
  (* by induction on typing of stmts *)
  intros g s s' f f' HT HGF HS.
  generalize dependent s'. generalize dependent f'.
  stmt_has_type_cases (induction HT) Case; intros f' s' HS; subst.
  Case "T_STMT_Empty".
    inversion HS. (* empty stmt list does not step *)
  Case "T_STMT_Assign". (* v = e ; s2 *)
    stmt_small_step_cases (inversion HS) SCase; subst.
    SCase "ST_STMT_Assign_Lit". (* v = l ; s2 *)
      split.
      (* first prove that g |- f' OK *)
        inversion H2; subst.
        apply GF_Correspondence.
        intros v' HGf'.
        inversion HGF; subst.
        destruct H3 with v' as [Tv']. apply HGf'. clear H3. destruct H4 as [Tl']. destruct H3 as [z']. Tactics.destruct_pairs.
        destruct (id_eq_dec v' v).
        (* Case: v = v' : in f', v' is mapped to Tv Te z *)
          exists Tv, Te, z. rewrite -> e in H3.
          assert (Tv = Tv'). eapply Gamma_Get_Content_Eq; eauto. subst.
          assert (Tv' = Tv0). eapply VarType_Content_Eq; eauto. subst.
          split. apply H3.
          split. apply StackFrame_Update_VarType_Eq.
          split. apply H1.
          apply StackFrame_Update_VarValue_Eq.
        (* Case: v <> v' : in f', v' is mapped to some Tv' Tl' z' *)
          exists Tv', Tl', z'. subst.
          split. apply H3.
          split. rewrite <- H4. apply StackFrame_Update_VarType_Neq. apply n.
          split. apply H6.
          rewrite <- H7. apply StackFrame_Update_VarValue_Neq. apply n.
      (* then prove that g |- s' *)
        apply HT.
    SCase "ST_STMT_Assign_Exp". (* v = e ; s2 and e --> e' *)
      split.
      (* first prove that g |- f' OK *)
        apply HGF.
      (* then prove that g |- v = e' ; s2 *)
        eapply expr_preservation in H2.
          destruct H2 as [T']. destruct H2.
          eapply T_STMT_Assign.
            apply H.
            apply H0.
            apply subtype_transitive with Te.
              apply H2. apply H1.
            apply H3.
            apply HT.
          apply HGF.
          apply H4.
Qed.
