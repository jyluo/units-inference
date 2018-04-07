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
Require Import UnitsArithmetics.
Require Import SubtypingDefs.
Require Import IDDefs.
Require Import ValueDefs.
Require Import GammaDefs.
Require Import HeapDefs.
Require Import GammaHeapCorrespondence.

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
Hint Constructors Expression.

Notation "e1 ':+' e2" := (E_Arith e1 op_add e2) (at level 2).
Notation "e1 ':*' e2" := (E_Arith e1 op_mul e2) (at level 2).
Notation "e1 ':%' e2" := (E_Arith e1 op_mod e2) (at level 2).

(* ======================================================= *)
Reserved Notation "'expr:' G '|-' e 'in' U" (at level 40).
Inductive expr_has_type : Gamma -> Expression -> Unit -> Prop :=
  | T_Value : forall (g : Gamma) (Tv : Unit) (z : nat),
    expr: g |- E_Value (Val Tv z) in Tv
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
Hint Constructors expr_has_type.

(* ======================================================= *)
Reserved Notation " he1 'expr==>' e2 " (at level 8).
Inductive expr_small_step : prod Heap Expression -> Expression -> Prop :=
  | ST_Field_Lookup : forall (h : Heap) (f : ID),
    ( h, E_Field_Lookup f ) expr==> (E_Value (FieldValue h f))
  | ST_Arith_Values : forall (h : Heap) (T1 T2 : Unit) (z1 z2 : nat) (op : OpKind),
    ( h, E_Arith (E_Value (Val T1 z1)) op (E_Value (Val T2 z2)) ) expr==> (E_Value (Val (computeUnit op T1 T2) (computeNat op z1 z2)) )
  | ST_Arith_Left_Reduce : forall (h : Heap) (e1 e1' e2 : Expression) (op : OpKind),
    ( h, e1 ) expr==> e1' ->
    ( h, E_Arith e1 op e2 ) expr==> (E_Arith e1' op e2)
  | ST_Arith_Right_Reduce : forall (h : Heap) (v1 : Value) (e2 e2' : Expression) (op : OpKind),
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
Hint Constructors expr_small_step.

(* ======================================================= *)
(* step is deterministic *)
Theorem expr_small_step_deterministic:
  forall (h : Heap) (e e1 e2 : Expression),
    (h, e) expr==> e1 ->
    (h, e) expr==> e2 ->
    e1 = e2.
Proof.
  intros h e e1 e2 He1.
  generalize dependent e2.
  expr_small_step_cases (induction He1) Case.
  Case "ST_Field_Lookup".
    intros e2 He2. inversion He2; subst. reflexivity.
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
  | V_Expr_Value : forall (T : Unit) (z : nat), expr_normal_form (E_Value (Val T z)).

(* ======================================================= *)
Theorem expr_progress : forall (g : Gamma) (e : Expression) (u : Unit) (h : Heap),
  expr: g |- e in u ->
  gh: g |- h OK ->
  expr_normal_form e \/ exists e', (h, e) expr==> e'.
Proof.
  (* by induction on typing of expr *)
  intros g e u h HT HGH.
  expr_has_type_cases (induction HT) Case; subst.
  Case "T_Value".
    left. apply V_Expr_Value.
  Case "T_Field_Lookup".
    right. exists (E_Value (FieldValue h f)). apply ST_Field_Lookup.
  Case "T_Arith".
    right.
    destruct IHHT1 as [He1NF |He1STEP]. apply HGH.
    (* Case: e1 is normal form *)
      inversion He1NF; subst.
      destruct IHHT2 as [He2NF | He2STEP]. apply HGH.
      (* Case: e2 is normal form *)
        inversion He2NF; subst. exists (E_Value (Val (computeUnit op T T0) (computeNat op z z0))). apply ST_Arith_Values.
      (* Case: e2 can take a step *)
        inversion He2STEP as [e2']; subst. exists (E_Arith (E_Value (Val T z)) op e2'). apply ST_Arith_Right_Reduce. apply H.
    (* Case: e1 can take a step *)
    inversion He1STEP as [e1']; subst. exists (E_Arith e1' op e2). apply ST_Arith_Left_Reduce. apply H.
Qed.

(* ======================================================= *)

(* TODO: split into proper subproofs *)

Theorem CU_Left_ST_Consistent:
  forall op T1 T1' T2,
  T1' <: T1 = true ->
  (computeUnit op T1' T2) <: (computeUnit op T1 T2) = true.
Proof.
  intros. unfold computeUnit.
  induction T1', T1; subst.
    apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    induction op; subst.
      rewrite -> addUnit_top_T_is_top. apply top_is_always_supertype.
      simpl. apply top_is_always_supertype.
      simpl. reflexivity.
    apply subtype_reflexive.
    induction op; subst.
      rewrite -> addUnit_bottom_T_is_T. unfold addUnit. unfold LUB. induction T2.
          simpl. rewrite -> unit_eq_dec_true. reflexivity.
          simpl. rewrite -> unit_eq_dec_false. reflexivity. discriminate.
          destruct (unit_eq_dec (declaredUnit n0) (declaredUnit n)).
            inversion e; subst. rewrite -> subtype_reflexive. rewrite -> subtype_reflexive. reflexivity.
            simpl. rewrite -> unit_eq_dec_false. rewrite -> unit_eq_dec_false. reflexivity. apply n1. intros contra. apply n1. symmetry. apply contra.
      simpl. induction T2.
        apply subtype_reflexive.
        apply subtype_reflexive.
        apply bottom_is_always_subtype.
      simpl. reflexivity.
    induction op; subst.
      rewrite -> addUnit_top_T_is_top. apply top_is_always_supertype.
      simpl. apply top_is_always_supertype.
      simpl. reflexivity.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H; subst. destruct (unit_eq_dec (declaredUnit n) (declaredUnit n0)).
      inversion e; subst. apply subtype_reflexive.
      inversion H1.
Qed.

(* TODO: split into proper subproofs *)

Theorem CU_Right_ST_Consistent:
  forall op T1 T2 T2',
  T2' <: T2 = true ->
  (computeUnit op T1 T2') <: (computeUnit op T1 T2) = true.
Proof.
  intros. unfold computeUnit.
  induction T2', T2; subst.
    apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    induction op; subst.
      rewrite -> addUnit_T_top_is_top. apply top_is_always_supertype.
      induction T1; subst; simpl.
        rewrite -> unit_eq_dec_true. reflexivity.
        reflexivity.
        reflexivity.
      unfold modUnit. apply subtype_reflexive.
    apply subtype_reflexive.
    induction op; subst.
      rewrite -> addUnit_T_bottom_is_T. induction T1; subst.
        rewrite -> addUnit_top_T_is_top. apply subtype_reflexive.
        apply bottom_is_always_subtype.
        destruct (unit_eq_dec (declaredUnit n0) (declaredUnit n)).
          destruct e; subst. rewrite -> addUnit_reflexive. apply subtype_reflexive.
          unfold addUnit. unfold LUB. simpl. rewrite -> unit_eq_dec_false. rewrite -> unit_eq_dec_false.
            reflexivity.
            intros contra. apply n1. symmetry. apply contra.
            apply n1.
      unfold mulUnit. induction T1; subst.
        apply subtype_reflexive.
        apply subtype_reflexive.
        apply bottom_is_always_subtype.
      unfold modUnit. apply subtype_reflexive.
    induction op; subst.
      rewrite -> addUnit_T_top_is_top. apply top_is_always_supertype.
      unfold mulUnit. induction T1; subst.
        apply subtype_reflexive.
        apply top_is_always_supertype.
        apply top_is_always_supertype.
      unfold modUnit. apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H; subst. destruct (unit_eq_dec (declaredUnit n) (declaredUnit n0)).
      inversion e; subst. apply subtype_reflexive.
      inversion H1.
Qed.

(* ======================================================= *)
Theorem expr_preservation : forall (g : Gamma) (h : Heap) (e e' : Expression) (T : Unit),
  expr: g |- e in T ->
  gh: g |- h OK ->
  (h, e) expr==> e' ->
  exists (T' : Unit), T' <: T = true /\ expr: g |- e' in T'.
Proof.
  (* by induction on typing of exprs *)
  intros g h e e' T HT HGH HS.
  generalize dependent e'.
  expr_has_type_cases (induction HT) Case; intros e' HS; subst.
  Case "T_Value".
    inversion HS. (* empty expr list does not step *)
  Case "T_Field_Lookup".
    inversion HS; subst.
    inversion HGH; subst.
    destruct H1 with f Tf. destruct H3. destruct H4 as [Tv']. destruct H4 as [z'].
      destruct H4. destruct H5.
    exists Tv'. split.
      apply H6.
      rewrite -> H5. apply T_Value.
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
        destruct HGH.
        destruct H.
        exists (computeUnit op x T2).
        split.
          eapply CU_Left_ST_Consistent in H. apply H.
          apply T_Arith.
            apply H0. apply HT2.
        apply H4.
    SCase "ST_Arith_Right_Reduce". (* v1 op e2 ==> v1 op e2' *)
      apply IHHT2 with e2' in HGH.
        destruct HGH.
        destruct H.
        exists (computeUnit op T1 x).
        split.
          eapply CU_Right_ST_Consistent in H. apply H.
          apply T_Arith.
            apply HT1. apply H0.
        apply H4.
Qed.

