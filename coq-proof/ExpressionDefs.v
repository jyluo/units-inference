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
From PUnits Require Import UnitsArithmetics.
From PUnits Require Import SubtypingDefs.
From PUnits Require Import IDDefs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import GammaDefs.
From PUnits Require Import StackFrame.
From PUnits Require Import GammaStackFrameCorrespondence.

(* Print Grammar pattern. *)

(* ======================================================= *)
Inductive Expression : Type :=
  | E_Value : Value -> Expression
  | E_Field_Lookup : ID -> Expression
  | E_Arith : Expression -> OpKind -> Expression -> Expression.
Tactic Notation "exp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Value"
  | Case_aux c "E_Field_Lookup"
  | Case_aux c "E_Arith"
  ].
Hint Constructors Expression : pUnitsHintDatabase.

Notation "e1 ':+' e2" := (E_Arith e1 op_add e2) (at level 2).
Notation "e1 ':*' e2" := (E_Arith e1 op_mul e2) (at level 2).
Notation "e1 ':%' e2" := (E_Arith e1 op_mod e2) (at level 2).

(* ======================================================= *)
Reserved Notation "'expr:' G '|-' e 'in' U" (at level 40).
Inductive expr_has_type : Gamma -> Expression -> Unit -> Prop :=
  | T_Value : forall (g : Gamma) (Tv : Unit) (z : nat),
    expr: g |- E_Value (Lit Tv z) in Tv
  | T_Field_Lookup : forall (g : Gamma) (f : ID) (Tf : Unit),
    Gamma_Contains g f = true ->
    Gamma_Get g f = Some Tf ->
    expr: g |- E_Field_Lookup f in Tf
  | T_Arith : forall (g : Gamma) (e1 e2 : Expression) (T1 T2 : Unit) (op : OpKind),
    expr: g |- e1 in T1 ->
    expr: g |- e2 in T2 ->
    expr: g |- E_Arith e1 op e2 in (computeUnit op T1 T2)
where "'expr:' g '|-' e 'in' T" := (expr_has_type g e T).
Tactic Notation "expr_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Value"
  | Case_aux c "T_Field_Lookup"
  | Case_aux c "T_Arith"
  ].
Hint Constructors expr_has_type : pUnitsHintDatabase.

(* ======================================================= *)
Reserved Notation " he1 'expr==>' e2 " (at level 8).
Inductive expr_small_step : prod StackFrame Expression -> Expression -> Prop :=
  | ST_Field_Lookup : forall (h : StackFrame) (f : ID) (T : Unit) (z : nat),
    VarValue h f = Some (Lit T z) ->
    ( h, E_Field_Lookup f ) expr==> (E_Value (Lit T z))
  | ST_Arith_Values : forall (h : StackFrame) (T1 T2 : Unit) (z1 z2 : nat) (op : OpKind),
    ( h, E_Arith (E_Value (Lit T1 z1)) op (E_Value (Lit T2 z2)) ) expr==> (E_Value (Lit (computeUnit op T1 T2) (computeNat op z1 z2)) )
  | ST_Arith_Left_Reduce : forall (h : StackFrame) (e1 e1' e2 : Expression) (op : OpKind),
    ( h, e1 ) expr==> e1' ->
    ( h, E_Arith e1 op e2 ) expr==> (E_Arith e1' op e2)
  | ST_Arith_Right_Reduce : forall (h : StackFrame) (v1 : Value) (e2 e2' : Expression) (op : OpKind),
    ( h, e2 ) expr==> e2' ->
    ( h, E_Arith (E_Value v1) op e2 ) expr==> (E_Arith (E_Value v1) op e2')
where " he1 'expr==>' e2 " := (expr_small_step he1 e2).
Tactic Notation "expr_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_Field_Lookup"
  | Case_aux c "ST_Arith_Values"
  | Case_aux c "ST_Arith_Left_Reduce"
  | Case_aux c "ST_Arith_Right_Reduce"
  ].
Hint Constructors expr_small_step : pUnitsHintDatabase.

(* ======================================================= *)
(* step is deterministic *)
Theorem expr_small_step_deterministic:
  forall (h : StackFrame) (e e1 e2 : Expression),
    (h, e) expr==> e1 ->
    (h, e) expr==> e2 ->
    e1 = e2.
Proof.
  intros h e e1 e2 He1.
  generalize dependent e2.
  expr_small_step_cases (induction He1) Case.
  Case "ST_Field_Lookup".
    intros e2 He2. inversion He2; subst.
    assert (Lit T z = Lit T0 z0). eapply VarValue_Content_Eq; eauto.
    destruct H0. reflexivity.
  Case "ST_Arith_Values".
    intros e2 He2. inversion He2; subst.
      reflexivity.
      inversion H4; subst.
      inversion H4; subst.
  Case "ST_Arith_Left_Reduce".
    intros e3 He3. inversion He3; subst.
      inversion He1.
      apply IHHe1 in H4. subst. reflexivity.
      inversion He1.
  Case "ST_Arith_Right_Reduce".
    intros e3 He3. inversion He3; subst.
      inversion He1.
      inversion H4.
      apply IHHe1 in H4. subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive expr_normal_form : Expression -> Prop :=
  | V_Expr_Value : forall (T : Unit) (z : nat), expr_normal_form (E_Value (Lit T z)).

(* ======================================================= *)
Theorem expr_progress : forall (g : Gamma) (h : StackFrame) (e : Expression) (T : Unit),
  expr: g |- e in T ->
  gf: g |- h OK ->
  expr_normal_form e \/ exists e', (h, e) expr==> e'.
Proof.
  (* by induction on typing of e *)
  intros g h e T HT HGH.
  expr_has_type_cases (induction HT) Case; subst.
  Case "T_Value".
    (* Case: e is a value v, and v is normal form. *)
    left. apply V_Expr_Value.
  Case "T_Field_Lookup".
    (* Case: e is a field lookup expression f. Since g |- e : Tf and g |- h OK,
       there exists a value in heap h for f, and f takes a step by looking up
       the value. *)
    right.
    inversion HGH; subst.
    destruct H1 with f as [Tf']. apply H. clear H1. destruct H2 as [Tv]. destruct H1 as [z]. Tactics.destruct_pairs.
    assert (Tf = Tf'). eapply Gamma_Get_Content_Eq; eauto. subst.
    exists (E_Value (Lit Tv z)). apply ST_Field_Lookup. apply H4.
  Case "T_Arith".
    (* Case: e is an arithmetic expression e1 op e2 for some op. We proceed by
       sub-case analysis on whether e1 is normal form or not *)
    right.
    destruct IHHT1 as [He1NF |He1STEP]. apply HGH.
    (* Case: e1 is normal form, we proceed by subcase analysis on whether e2 is
       normal form or not *)
      inversion He1NF; subst.
      inversion HT1; subst. rename z into z1.
      destruct IHHT2 as [He2NF | He2STEP]. apply HGH.
      (* Case: e2 is normal form, then there exists a value
         (T1 op T2) (z1 op z2) which e1 op e2 steps to *)
        inversion He2NF; subst. inversion HT2; subst. rename z into z2.
        exists (E_Value (Lit (computeUnit op T1 T2) (computeNat op z1 z2))). apply ST_Arith_Values.
      (* Case: e2 can take a step to e2', then e1 op e2 steps to e1 op e2' *)
        inversion He2STEP as [e2']; subst. exists (E_Arith (E_Value (Lit T1 z1)) op e2'). apply ST_Arith_Right_Reduce. apply H.
    (* Case: e1 can take a step to e1', then e1 op e2 steps to e1' op e2 *)
    inversion He1STEP as [e1']; subst. exists (E_Arith e1' op e2). apply ST_Arith_Left_Reduce. apply H.
Qed.

(* ======================================================= *)
Theorem expr_preservation : forall (g : Gamma) (h : StackFrame) (e e' : Expression) (T : Unit),
  expr: g |- e in T ->
  gf: g |- h OK ->
  (h, e) expr==> e' ->
  exists (T' : Unit), T' <: T = true /\ expr: g |- e' in T'.
Proof.
  (* by induction on typing of e *)
  intros g h e e' T HT HGH HS.
  generalize dependent e'.
  expr_has_type_cases (induction HT) Case; intros e' HS; subst.
  Case "T_Value".
    (* values do not step *)
    inversion HS.
  Case "T_Field_Lookup".
    (* given that h, f expr==> Tv' z' by looking up the value from heap h,
       we know from g |- h OK that Tv' <: Tf and thus g |- Tv' z' : Tv' as
       required *)
    inversion HS; subst.
    inversion HGH; subst.
    destruct H1 with f as [Tf']. apply H. destruct H2 as [Tv']. destruct H2 as [z']. Tactics.destruct_pairs.
    assert (Tf = Tf'). eapply Gamma_Get_Content_Eq; eauto. subst.
    assert (Lit T z = Lit Tv' z'). eapply VarValue_Content_Eq; eauto. inversion H7. subst.
    exists Tv'. split.
      apply H5.
      apply T_Value.
  Case "T_Arith".
    inversion HS; subst. (* e1 op e2 ==> e' in one of 3 ways *)
    SCase "ST_Arith_Values". (* v1 op v2 ==> v *)
      inversion HT1; subst.
      inversion HT2; subst.
      exists (computeUnit op T1 T2).
      split.
        apply subtype_reflexive. (* apply ST_Reflexive. *)
        apply T_Value.
    SCase "ST_Arith_Left_Reduce". (* e1 op e2 ==> e1' op e2 *)
      apply IHHT1 with e1' in HGH.
        destruct HGH as [T1'].
        destruct H.
        exists (computeUnit op T1' T2).
        split.
          apply computeUnit_Left_ST_Consistent. apply H.
          apply T_Arith.
            apply H0.
            apply HT2.
        apply H4.
    SCase "ST_Arith_Right_Reduce". (* v1 op e2 ==> v1 op e2' *)
      apply IHHT2 with e2' in HGH.
        destruct HGH as [T2'].
        destruct H.
        exists (computeUnit op T1 T2').
        split.
          apply computeUnit_Right_ST_Consistent. apply H.
          apply T_Arith.
            apply HT1.
            apply H0.
        apply H4.
Qed.
