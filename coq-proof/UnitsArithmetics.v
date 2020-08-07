Require Import Nat.
Require Import List.
Import List.ListNotations.
Require Import Lists.ListSet.

From PUnits Require Import UnitsDefs.
From PUnits Require Import SubtypingDefs.
From PUnits Require Import LabeledLiterals.

(* Defines supported arithmetic operations *)

(* ======================================================= *)
Inductive OpKind : Type :=
  | op_add : OpKind
  | op_mul : OpKind
  | op_mod : OpKind.

Theorem opkind_eq_dec :
  forall (o1 o2 : OpKind), {o1 = o2} + {o1 <> o2}.
Proof.
  intros. induction o1, o2; subst;
    try (left; reflexivity);
    try (right; discriminate).
Qed.

(* ======================================================= *)
Definition addUnit(u1 u2 : Unit) : Unit :=
  LUB u1 u2.

Theorem addUnit_reflexive :
  forall (u : Unit), addUnit u u = u.
Proof.
  intros. unfold addUnit. apply LUB_reflexive.
Qed.

Theorem addUnit_commutative :
  forall (u1 u2 : Unit), addUnit u1 u2 = addUnit u2 u1.
Proof.
  intros. unfold addUnit. apply LUB_commutative.
Qed.

Theorem addUnit_top_T_is_top :
  forall (T : Unit), addUnit top T = top.
Proof.
  intros. unfold addUnit. apply LUB_top_T_is_top.
Qed.

Theorem addUnit_T_top_is_top :
  forall (T : Unit), addUnit T top = top.
Proof.
  intros.
  rewrite -> addUnit_commutative.
  apply addUnit_top_T_is_top.
Qed.

Theorem addUnit_bottom_T_is_T :
  forall (T : Unit), addUnit bottom T = T.
Proof.
  intros. unfold addUnit. apply LUB_bottom_T_is_T.
Qed.

Theorem addUnit_T_bottom_is_T :
  forall (T : Unit), addUnit T bottom = T.
Proof.
  intros.
  rewrite -> addUnit_commutative.
  apply addUnit_bottom_T_is_T.
Qed.

(* ======================================================= *)
(* assuming Coq's set is unordered *)
Fixpoint mulSetBCElem(bc1 : BaseUnitComponent)(s : set BaseUnitComponent) : BaseUnitComponent :=
  match s with
    | bc2 :: s' =>
      match bc1, bc2 with
        | bc bu1 n1, bc bu2 n2 =>
          if baseUnit_eq_dec bu1 bu2 then
            bc bu1 (n1 + n2)
          else
            mulSetBCElem bc1 s'
      end
    | empty_set => bc1
  end.

Module MulSetBCElem_Test.
Example example1 : mulSetBCElem (bc meter 1) [(bc meter 1)] = (bc meter 2).
Proof. simpl. rewrite -> (baseUnit_eq_dec_true meter). reflexivity. Qed.
Example example2 : mulSetBCElem (bc meter 1) [(bc second 1)] = (bc meter 1).
Proof. simpl. rewrite -> (baseUnit_eq_dec_false meter second). reflexivity. discriminate. Qed.
End MulSetBCElem_Test.

Fixpoint mulSetBC(s1 s2 : set BaseUnitComponent) : set BaseUnitComponent :=
  match s1 with
    | bc1 :: s1' => mulSetBCElem bc1 s2 :: mulSetBC s1' s2
    | empty_set => empty_set
  end.

Module MulSetBC_Test.
Example example1 : mulSetBC [(bc meter 1)] [(bc meter 1)] = [(bc meter 2)].
Proof. simpl. rewrite -> (baseUnit_eq_dec_true meter). reflexivity. Qed.
Example example2 : mulSetBC [(bc meter 1)] [(bc second 1)] = [(bc meter 1)].
Proof. simpl. rewrite -> (baseUnit_eq_dec_false meter second). reflexivity. discriminate. Qed.
End MulSetBC_Test.

Definition mulNormalizedUnit(nu1 nu2 : NormalizedUnit) : NormalizedUnit :=
  match nu1, nu2 with
  | normUnit pc1 s1, normUnit pc2 s2 =>
    match pc1, pc2 with
      | pc ten p1, pc ten p2 => normUnit (pc ten (p1 + p2)) (mulSetBC s1 s2)
    end
  end.

Module MulNormalizedUnit_Test.
Example example1 : mulNormalizedUnit m m = m2.
Proof. simpl.
  rewrite -> (baseUnit_eq_dec_true meter);
  rewrite -> (baseUnit_eq_dec_true second);
  rewrite -> (baseUnit_eq_dec_true gram);
  try(rewrite -> (baseUnit_eq_dec_false second meter));
  try(rewrite -> (baseUnit_eq_dec_false gram meter));
  try(rewrite -> (baseUnit_eq_dec_false gram second));
  try(reflexivity);
  try(discriminate).
Qed.
Example example2 : mulNormalizedUnit m s = normUnit (pc ten 0) [bc meter 1 ; bc second 1 ; bc gram 0].
Proof. simpl.
  rewrite -> (baseUnit_eq_dec_true meter);
  rewrite -> (baseUnit_eq_dec_true second);
  rewrite -> (baseUnit_eq_dec_true gram);
  try(rewrite -> (baseUnit_eq_dec_false second meter));
  try(rewrite -> (baseUnit_eq_dec_false gram meter));
  try(rewrite -> (baseUnit_eq_dec_false gram second));
  try(reflexivity);
  try(discriminate).
Qed.
End MulNormalizedUnit_Test.

Definition mulUnit(u1 u2 : Unit) : Unit :=
  match u1, u2 with
    | top, _ => top
    | _, top => top
    | bottom, _ => bottom
    | _, bottom => bottom
    | declaredUnit nu1, declaredUnit nu2 => declaredUnit (mulNormalizedUnit nu1 nu2)
  end.

Module MulUnit_Test.
Example example1 : mulUnit mUnit mUnit = m2Unit.
Proof. simpl.
  rewrite -> (baseUnit_eq_dec_true meter);
  rewrite -> (baseUnit_eq_dec_true second);
  rewrite -> (baseUnit_eq_dec_true gram);
  try(rewrite -> (baseUnit_eq_dec_false second meter));
  try(rewrite -> (baseUnit_eq_dec_false gram meter));
  try(rewrite -> (baseUnit_eq_dec_false gram second));
  try(reflexivity);
  try(discriminate).
Qed.
Example example2 : mulUnit dimensionlessUnit mUnit = mUnit.
Proof. simpl.
  rewrite -> (baseUnit_eq_dec_true meter);
  rewrite -> (baseUnit_eq_dec_true second);
  rewrite -> (baseUnit_eq_dec_true gram);
  try(rewrite -> (baseUnit_eq_dec_false second meter));
  try(rewrite -> (baseUnit_eq_dec_false gram meter));
  try(rewrite -> (baseUnit_eq_dec_false gram second));
  try(reflexivity);
  try(discriminate).
Qed.
Example example3 : mulUnit top dimensionlessUnit = top.
Proof. simpl. reflexivity. Qed.
Example example4 : mulUnit dimensionlessUnit top = top.
Proof. simpl. reflexivity. Qed.
Example example5 : mulUnit top mUnit = top.
Proof. simpl. reflexivity. Qed.
Example example6 : mulUnit mUnit top = top.
Proof. simpl. reflexivity. Qed.
Example example7 : mulUnit bottom mUnit = bottom.
Proof. simpl. reflexivity. Qed.
Example example8 : mulUnit mUnit bottom = bottom.
Proof. simpl. reflexivity. Qed.
Example example9 : mulUnit top bottom = top.
Proof. simpl. reflexivity. Qed.
Example example10: mulUnit bottom top = top.
Proof. simpl. reflexivity. Qed.
End MulUnit_Test.


(* ======================================================= *)
Definition modUnit(u1 u2 : Unit) : Unit :=
  u1.

(* ======================================================= *)

Theorem addUnit_Left_ST_Consistent:
  forall T1 T1' T2,
  T1' <: T1 = true ->
  (addUnit T1' T2) <: (addUnit T1 T2) = true.
Proof.
  intros. induction T1', T1; subst.
    apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    rewrite -> addUnit_top_T_is_top. apply top_is_always_supertype.
    apply subtype_reflexive.
    rewrite -> addUnit_bottom_T_is_T. unfold addUnit. unfold LUB. induction T2; subst.
      simpl. rewrite -> unit_eq_dec_true. reflexivity.
      simpl. rewrite -> unit_eq_dec_false. reflexivity. discriminate.
      destruct (unit_eq_dec (declaredUnit n0) (declaredUnit n)).
        inversion e; subst. rewrite -> subtype_reflexive. apply subtype_reflexive.
        simpl. rewrite -> unit_eq_dec_false. rewrite -> unit_eq_dec_false. reflexivity.
          apply n1.
          intros contra. apply n1. symmetry. apply contra.
    rewrite -> addUnit_top_T_is_top. apply top_is_always_supertype.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H; subst. destruct (unit_eq_dec (declaredUnit n) (declaredUnit n0)).
      inversion e; subst. apply subtype_reflexive.
      inversion H1.
Qed.

Theorem addUnit_Right_ST_Consistent:
  forall T1 T2 T2',
  T2' <: T2 = true ->
  (addUnit T1 T2') <: (addUnit T1 T2) = true.
Proof.
  intros. induction T2', T2; subst.
    apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    rewrite -> addUnit_T_top_is_top. apply top_is_always_supertype.
    apply subtype_reflexive.
    rewrite -> addUnit_T_bottom_is_T. induction T1; subst.
      rewrite -> addUnit_top_T_is_top. apply subtype_reflexive.
      rewrite -> addUnit_bottom_T_is_T. apply bottom_is_always_subtype.
      destruct (unit_eq_dec (declaredUnit n0) (declaredUnit n)).
        inversion e; subst. rewrite -> addUnit_reflexive. apply subtype_reflexive.
        unfold addUnit. unfold LUB. simpl. rewrite -> unit_eq_dec_false. rewrite -> unit_eq_dec_false. reflexivity.
          intros contra. apply n1. symmetry. apply contra.
          apply n1.
    rewrite -> addUnit_T_top_is_top. apply top_is_always_supertype.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H; subst. destruct (unit_eq_dec (declaredUnit n) (declaredUnit n0)).
      inversion e; subst. apply subtype_reflexive.
      inversion H1.
Qed.

Theorem mulUnit_Left_ST_Consistent:
  forall T1 T1' T2,
  T1' <: T1 = true ->
  (mulUnit T1' T2) <: (mulUnit T1 T2) = true.
Proof.
  intros. induction T1', T1; subst.
    apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    simpl. apply top_is_always_supertype.
    apply subtype_reflexive.
    simpl. induction T2.
      apply subtype_reflexive.
      apply subtype_reflexive.
      apply bottom_is_always_subtype.
    simpl. apply top_is_always_supertype.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H; subst. destruct (unit_eq_dec (declaredUnit n) (declaredUnit n0)).
      inversion e; subst. apply subtype_reflexive.
      inversion H1.
Qed.

Theorem mulUnit_Right_ST_Consistent:
  forall T1 T2 T2',
  T2' <: T2 = true ->
  (mulUnit T1 T2') <: (mulUnit T1 T2) = true.
Proof.
  intros. induction T2', T2; subst.
    apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    induction T1; subst; simpl.
      rewrite -> unit_eq_dec_true. reflexivity.
      reflexivity.
      reflexivity.
    apply subtype_reflexive.
    unfold mulUnit. induction T1; subst.
      apply subtype_reflexive.
      apply subtype_reflexive.
      apply bottom_is_always_subtype.
    unfold mulUnit. induction T1; subst.
      apply subtype_reflexive.
      apply top_is_always_supertype.
      apply top_is_always_supertype.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H; subst. destruct (unit_eq_dec (declaredUnit n) (declaredUnit n0)).
      inversion e; subst. apply subtype_reflexive.
      inversion H1.
Qed.

Theorem modUnit_Left_ST_Consistent:
  forall T1 T1' T2,
  T1' <: T1 = true ->
  (modUnit T1' T2) <: (modUnit T1 T2) = true.
Proof.
  intros. induction T1', T1; subst.
    apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    simpl. reflexivity.
    apply subtype_reflexive.
    simpl. reflexivity.
    simpl. reflexivity.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H; subst. destruct (unit_eq_dec (declaredUnit n) (declaredUnit n0)).
      inversion e; subst. apply subtype_reflexive.
      inversion H1.
Qed.

Theorem modUnit_Right_ST_Consistent:
  forall T1 T2 T2',
  T2' <: T2 = true ->
  (modUnit T1 T2') <: (modUnit T1 T2) = true.
Proof.
  intros. induction T2', T2; subst.
    apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    unfold modUnit. apply subtype_reflexive.
    apply subtype_reflexive.
    unfold modUnit. apply subtype_reflexive.
    unfold modUnit. apply subtype_reflexive.
    inversion H. rewrite -> unit_eq_dec_false in H1. inversion H1. discriminate.
    inversion H; subst. destruct (unit_eq_dec (declaredUnit n) (declaredUnit n0)).
      inversion e; subst. apply subtype_reflexive.
      inversion H1.
Qed.

(* ======================================================= *)

Definition computeUnit (op : OpKind) (u1 u2 : Unit) : Unit :=
  match op with
  | op_add => addUnit u1 u2
  | op_mul => mulUnit u1 u2
  | op_mod => modUnit u1 u2
  end.

Theorem alwaysAResultUnit:
  forall (op : OpKind) (T1 T2 : Unit),
  exists (T3 : Unit), computeUnit op T1 T2 = T3.
Proof.
  intros.
  induction op.
    exists (addUnit T1 T2). reflexivity.
    exists (mulUnit T1 T2). reflexivity.
    exists (modUnit T1 T2). reflexivity.
Qed.

Definition computeNat (op : OpKind) (z1 z2 : nat) : nat :=
  match op with
  | op_add => z1 + z2
  | op_mul => z1 * z2
  | op_mod => z1 mod z2
  end.

Definition computeValue (op : OpKind) (v1 v2 : Value) : Value :=
  match v1, v2 with
  | Lit u1 z1, Lit u2 z2 => Lit (computeUnit op u1 u2) (computeNat op z1 z2)
  end.

(* ======================================================= *)

Theorem computeUnit_Left_ST_Consistent:
  forall op T1 T1' T2,
  T1' <: T1 = true ->
  (computeUnit op T1' T2) <: (computeUnit op T1 T2) = true.
Proof.
  intros. unfold computeUnit.
  induction op; subst.
    apply addUnit_Left_ST_Consistent. apply H.
    apply mulUnit_Left_ST_Consistent. apply H.
    apply modUnit_Left_ST_Consistent. apply H.
Qed.

Theorem computeUnit_Right_ST_Consistent:
  forall op T1 T2 T2',
  T2' <: T2 = true ->
  (computeUnit op T1 T2') <: (computeUnit op T1 T2) = true.
Proof.
  intros. unfold computeUnit.
  induction op; subst.
    apply addUnit_Right_ST_Consistent. apply H.
    apply mulUnit_Right_ST_Consistent. apply H.
    apply modUnit_Right_ST_Consistent. apply H.
Qed.

