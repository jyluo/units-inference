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
Require Import IDDefs.
Require Import ValueDefs.
Require Import GammaDefs.
Require Import HeapDefs.
Require Import GammaHeapCorrespondence.
Require Import ExpressionDefs.

(* ======================================================= *)
Inductive Statements : Type :=
  | STMT_Empty : Statements
  | STMT_Assign : ID -> Expression -> Statements -> Statements. (* f = e ; s *)
Tactic Notation "stmt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STMT_Empty"
  | Case_aux c "STMT_Assign"
  ].
Hint Constructors Statements.

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
Hint Constructors stmt_has_type.

(* ======================================================= *)

Reserved Notation " s1 'stmt==>' s2 " (at level 8).
Inductive stmt_small_step : prod Heap Statements -> prod Heap Statements -> Prop :=
  | ST_STMT_Assign_Val : forall (h : Heap) (f : ID) (Tf Tv : Unit) (z : nat) (s2 : Statements),
    FieldType h f = Tf ->
    Tv <: Tf = true ->
    ( h, STMT_Assign f (E_Value (Val Tv z)) s2 ) stmt==> ( (Heap_Update h f Tf Tv z), s2 )
  | ST_STMT_Assign_Exp : forall (h : Heap) (f : ID) (e e' : Expression) (s2 : Statements),
    ( h, e ) expr==> e' ->
    ( h, STMT_Assign f e s2 ) stmt==> ( h, STMT_Assign f e' s2 )
where " s1 'stmt==>' s2 " := (stmt_small_step s1 s2).
Tactic Notation "stmt_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_STMT_Assign_Val"
  | Case_aux c "ST_STMT_Assign_Exp"
  ].
Hint Constructors stmt_small_step.

(* ======================================================= *)
(* step is deterministic *)
Theorem stmt_small_step_deterministic:
  forall (s s1 s2 : prod Heap Statements),
    s stmt==> s1 ->
    s stmt==> s2 ->
    s1 = s2.
Proof.
  intros s s1 s2 Hs1 Hs2.
  generalize dependent s2.
  stmt_small_step_cases (induction Hs1) Case.
  Case "ST_STMT_Assign_Val".
    intros s3 Hs3; inversion Hs3; subst.
      reflexivity.
      inversion H6.
  Case "ST_STMT_Assign_Exp".
    intros s3 Hs3; inversion Hs3; subst.
      inversion H.
      assert (e' = e'0). apply expr_small_step_deterministic with h e.
        apply H. apply H5.
      subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive STMT_Normal_Form : Statements -> Prop :=
  | V_STMT_Value : STMT_Normal_Form STMT_Empty.

(* ======================================================= *)
Theorem stmt_progress : forall (g : Gamma) (h : Heap) (s : Statements),
  stmt: g |- s ->
  gh: g |- h OK ->
  STMT_Normal_Form s \/ exists (h' : Heap) (s' : Statements), (h, s) stmt==> (h', s').
Proof.
  intros g h s HT HGH.
  stmt_has_type_cases (induction HT) Case; subst.
  Case "T_STMT_Empty".
    left. apply V_STMT_Value.
  Case "T_STMT_Assign".
    right.
    inversion HGH; subst.
    destruct H3 with f. destruct H5 as [Tf']. destruct H5 as [Tv']. destruct H5 as [z'].
      destruct H5. destruct H6. destruct H7.
    assert (Tf = Tf').
      eapply Gamma_Get_Content_Eq. apply H0. apply H5. subst.
    assert (expr_normal_form e \/ exists e', (h, e) expr==> e').
      apply expr_progress with g Te.
        apply H2. apply HGH.
    inversion H6; subst.
    (* Case : e is normal form -> step by ST_STMT_Assign_Val *)
      destruct H9; subst. inversion H2; subst. exists (Heap_Update h f (FieldType h f) Te z). exists s2.
      eapply ST_STMT_Assign_Val.
        reflexivity.
        apply H1.
    (* Case : e can take a step -> step by ST_STMT_Assign_Exp *)
      destruct H9 as [e']; subst. exists h. exists (STMT_Assign f e' s2). apply ST_STMT_Assign_Exp. apply H9.
Qed.

(* ======================================================= *)
Theorem stmt_preservation : forall (g : Gamma) (s s' : Statements) (h h' : Heap),
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
        intros f'.
        inversion HGH; subst.
        destruct H3 with f'. destruct H5 as [Tf']. destruct H5 as [Tv']. destruct H5 as [z'].
          destruct H5. destruct H6. destruct H7.
        split. apply H4.
        destruct (id_eq_dec f' f).
        (* Case: f = f' : in h', the value of f' is Tf Te z *)
          exists Tf, Te, z. rewrite -> e in H5.
          assert (Tf = Tf'). eapply Gamma_Get_Content_Eq. apply H0. apply H5. subst.
          split. apply H5.
          split. apply Heap_Update_FieldType_Eq.
          split. apply H1.
          apply Heap_Update_FieldValue_Eq.
        (* Case: f <> f' : in h' the value of f' is some Tf' Tv' z' *)
          exists Tf', Tv', z'. subst.
          split. apply H5.
          split. apply Heap_Update_FieldType_Neq. apply n.
          split. apply H7.
          rewrite <- H8. apply Heap_Update_FieldValue_Neq. apply n.
      (* then prove that g |- s' *)
        apply HT.
    SCase "ST_STMT_Assign_Exp". (* f = e ; s2 , e --> e' *)
      split.
        apply HGH.
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
