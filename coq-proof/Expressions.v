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
From PUnits Require Import UnitsArithmetics.
From PUnits Require Import Subtyping.
From PUnits Require Import IDs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import Gamma.
From PUnits Require Import StackFrame.
From PUnits Require Import GammaStackFrameCorrespondence.

(* Expressions e in the language *)
Inductive Expression : Type :=
  | E_LabeledLiteral : LabeledLiteral -> Expression
  | E_Variable_Lookup : ID -> Expression
  | E_Arith : Expression -> OpKind -> Expression -> Expression.
Tactic Notation "exp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_LabeledLiteral"
  | Case_aux c "E_Variable_Lookup"
  | Case_aux c "E_Arith"
  ].
Hint Constructors Expression : pUnitsHintDatabase.

(* ======================================================= *)
Reserved Notation "'expr:' G '|-' e 'in' U" (at level 40).
Inductive expr_has_type : Gamma -> Expression -> Unit -> Prop :=
  | T_LabeledLiteral : forall (g : Gamma) (Tl : Unit) (z : nat),
    expr: g |- E_LabeledLiteral (Lit Tl z) in Tl
  | T_Variable_Lookup : forall (g : Gamma) (v : ID) (Tv : Unit),
    Gamma_Contains g v = true ->
    Gamma_Get g v = Some Tv ->
    expr: g |- E_Variable_Lookup v in Tv
  | T_Arith : forall (g : Gamma) (e1 e2 : Expression) (T1 T2 : Unit) (op : OpKind),
    expr: g |- e1 in T1 ->
    expr: g |- e2 in T2 ->
    expr: g |- E_Arith e1 op e2 in (computeUnit op T1 T2)
where "'expr:' g '|-' e 'in' T" := (expr_has_type g e T).
Tactic Notation "expr_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_LabeledLiteral"
  | Case_aux c "T_Variable_Lookup"
  | Case_aux c "T_Arith"
  ].
Hint Constructors expr_has_type : pUnitsHintDatabase.

(* ======================================================= *)
Reserved Notation " he1 'expr==>' e2 " (at level 8).
Inductive expr_small_step : prod StackFrame Expression -> Expression -> Prop :=
  | ST_Variable_Lookup : forall (f : StackFrame) (v : ID) (T : Unit) (z : nat),
    VarValue f v = Some (Lit T z) ->
    ( f, E_Variable_Lookup v ) expr==> (E_LabeledLiteral (Lit T z))
  | ST_Arith_LabeledLiterals : forall (f : StackFrame) (T1 T2 : Unit) (z1 z2 : nat) (op : OpKind),
    ( f, E_Arith (E_LabeledLiteral (Lit T1 z1)) op (E_LabeledLiteral (Lit T2 z2)) ) expr==> (E_LabeledLiteral (Lit (computeUnit op T1 T2) (computeNat op z1 z2)) )
  | ST_Arith_Left_Reduce : forall (f : StackFrame) (e1 e1' e2 : Expression) (op : OpKind),
    ( f, e1 ) expr==> e1' ->
    ( f, E_Arith e1 op e2 ) expr==> (E_Arith e1' op e2)
  | ST_Arith_Right_Reduce : forall (f : StackFrame) (l1 : LabeledLiteral) (e2 e2' : Expression) (op : OpKind),
    ( f, e2 ) expr==> e2' ->
    ( f, E_Arith (E_LabeledLiteral l1) op e2 ) expr==> (E_Arith (E_LabeledLiteral l1) op e2')
where " he1 'expr==>' e2 " := (expr_small_step he1 e2).
Tactic Notation "expr_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_Variable_Lookup"
  | Case_aux c "ST_Arith_LabeledLiterals"
  | Case_aux c "ST_Arith_Left_Reduce"
  | Case_aux c "ST_Arith_Right_Reduce"
  ].
Hint Constructors expr_small_step : pUnitsHintDatabase.

(* ======================================================= *)
(* step is deterministic *)
Theorem expr_small_step_deterministic:
  forall (f : StackFrame) (e e1 e2 : Expression),
    (f, e) expr==> e1 ->
    (f, e) expr==> e2 ->
    e1 = e2.
Proof.
  intros f e e1 e2 He1.
  generalize dependent e2.
  expr_small_step_cases (induction He1) Case.
  Case "ST_Variable_Lookup".
    intros e2 He2. inversion He2; subst.
    assert (Lit T z = Lit T0 z0). eapply VarValue_Content_Eq; eauto.
    destruct H0. reflexivity.
  Case "ST_Arith_LabeledLiterals".
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
  | V_Expr_LabeledLiteral : forall (T : Unit) (z : nat), expr_normal_form (E_LabeledLiteral (Lit T z)).

(* ======================================================= *)
Theorem expr_progress : forall (g : Gamma) (f : StackFrame) (e : Expression) (T : Unit),
  expr: g |- e in T ->
  gf: g |- f OK ->
  expr_normal_form e \/ exists e', (f, e) expr==> e'.
Proof.
  (* by induction on typing of e *)
  intros g f e T HT HGF.
  expr_has_type_cases (induction HT) Case; subst.
  Case "T_LabeledLiteral".
    (* Case: e is a labeled literal l, and l is normal form. *)
    left. apply V_Expr_LabeledLiteral.
  Case "T_Variable_Lookup".
    (* Case: e is a variable lookup expression v. Since g |- e : Tv and
       g |- f OK, there exists a labeled value in stack frame f for v, and v
       takes a step by looking up the labeled value. *)
    right.
    inversion HGF; subst.
    destruct H1 with v as [Tv']. apply H. clear H1. destruct H2 as [Tl]. destruct H1 as [z]. Tactics.destruct_pairs.
    assert (Tv = Tv'). eapply Gamma_Get_Content_Eq; eauto. subst.
    exists (E_LabeledLiteral (Lit Tl z)). apply ST_Variable_Lookup. apply H4.
  Case "T_Arith".
    (* Case: e is an arithmetic expression e1 op e2 for some op. We proceed by
       sub-case analysis on whether e1 is normal form or not *)
    right.
    destruct IHHT1 as [He1NF |He1STEP]. apply HGF.
    (* Case: e1 is normal form, we proceed by subcase analysis on whether e2 is
       normal form or not *)
      inversion He1NF; subst.
      inversion HT1; subst. rename z into z1.
      destruct IHHT2 as [He2NF | He2STEP]. apply HGF.
      (* Case: e2 is normal form, then there exists a labeled value
         (T1 op T2) (z1 op z2) which e1 op e2 steps to *)
        inversion He2NF; subst. inversion HT2; subst. rename z into z2.
        exists (E_LabeledLiteral (Lit (computeUnit op T1 T2) (computeNat op z1 z2))). apply ST_Arith_LabeledLiterals.
      (* Case: e2 can take a step to e2', then e1 op e2 steps to e1 op e2' *)
        inversion He2STEP as [e2']; subst. exists (E_Arith (E_LabeledLiteral (Lit T1 z1)) op e2'). apply ST_Arith_Right_Reduce. apply H.
    (* Case: e1 can take a step to e1', then e1 op e2 steps to e1' op e2 *)
    inversion He1STEP as [e1']; subst. exists (E_Arith e1' op e2). apply ST_Arith_Left_Reduce. apply H.
Qed.

(* ======================================================= *)
Theorem expr_preservation : forall (g : Gamma) (f : StackFrame) (e e' : Expression) (T : Unit),
  expr: g |- e in T ->
  gf: g |- f OK ->
  (f, e) expr==> e' ->
  exists (T' : Unit), T' <: T = true /\ expr: g |- e' in T'.
Proof.
  (* by induction on typing of e *)
  intros g f e e' T HT HGF HS.
  generalize dependent e'.
  expr_has_type_cases (induction HT) Case; intros e' HS; subst.
  Case "T_LabeledLiteral".
    (* values do not step *)
    inversion HS.
  Case "T_Variable_Lookup".
    (* given that f, v expr==> Tl' z' by looking up the labeled value from stack
       frame f, we know from g |- f OK that Tl' <: Tv and thus g |- Tl' z' : Tl'
       as required *)
    inversion HS; subst.
    inversion HGF; subst.
    destruct H1 with v as [Tv']. apply H. destruct H2 as [Tl']. destruct H2 as [z']. Tactics.destruct_pairs.
    assert (Tv = Tv'). eapply Gamma_Get_Content_Eq; eauto. subst.
    assert (Lit T z = Lit Tl' z'). eapply VarValue_Content_Eq; eauto. inversion H7. subst.
    exists Tl'. split.
      apply H5.
      apply T_LabeledLiteral.
  Case "T_Arith".
    inversion HS; subst. (* e1 op e2 ==> e' in one of 3 ways *)
    SCase "ST_Arith_LabeledLiterals". (* l1 op l2 ==> l *)
      inversion HT1; subst.
      inversion HT2; subst.
      exists (computeUnit op T1 T2).
      split.
        apply subtype_reflexive. (* apply ST_Reflexive. *)
        apply T_LabeledLiteral.
    SCase "ST_Arith_Left_Reduce". (* e1 op e2 ==> e1' op e2 *)
      apply IHHT1 with e1' in HGF.
        destruct HGF as [T1'].
        destruct H.
        exists (computeUnit op T1' T2).
        split.
          apply computeUnit_Left_ST_Consistent. apply H.
          apply T_Arith.
            apply H0.
            apply HT2.
        apply H4.
    SCase "ST_Arith_Right_Reduce". (* l1 op e2 ==> l1 op e2' *)
      apply IHHT2 with e2' in HGF.
        destruct HGF as [T2'].
        destruct H.
        exists (computeUnit op T1 T2').
        split.
          apply computeUnit_Right_ST_Consistent. apply H.
          apply T_Arith.
            apply HT1.
            apply H0.
        apply H4.
Qed.
