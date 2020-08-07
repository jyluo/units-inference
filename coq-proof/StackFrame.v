From PUnits Require Import UnitsDefs.
From PUnits Require Import IDDefs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import MapsDefs.

(* Stack Frame F is a map from Variable Identifiers v to pairs of its static
type Tv and labeled value l = Tl z. Formally v is mapped to a tuple, but for
implementation convenience we model l explicitly as a term and use Coq's
built-in pair data structure: F = v -> Tv, (Tl, n) .
*)
Definition StackFrameValue : Type := prod Unit Value.

Definition StackFrameValue_beq ( fv1 fv2 : StackFrameValue ) : bool :=
  match fv1, fv2 with
  | (u1, l1), (u2, l2) => if unit_beq u1 u2 then if Value_beq l1 l2 then true else false else false
  end.

Definition StackFrame := Map ID StackFrameValue.

Definition empty_heap := Empty_Map ID StackFrameValue.
Definition StackFrame_Update (f : StackFrame) (v : ID) (Tv Tl : Unit) (z : nat) : StackFrame := Map_Add id_beq h v (Tv, Val Tl z).
Definition StackFrame_Get (h : StackFrame) (v : ID) : option StackFrameValue := Map_Get id_beq h v.
Definition StackFrame_Contains (h : StackFrame) (v : ID) : bool := Map_Contains id_beq h v.
Definition StackFrame_IsSubMap (h1 h2 : StackFrame) : bool := Map_IsSubMap id_beq StackFrameValue_beq h1 h2.
Hint Unfold StackFrame_Update : pUnitsHintDatabase.

Theorem StackFrame_Get_Content_Eq :
  forall (h : StackFrame) (v : ID) (l1 l2 : option StackFrameValue),
  StackFrame_Get h v = l1 ->
  StackFrame_Get h v = l2 ->
  l1 = l2.
Proof.
  unfold StackFrame_Get.
  intros.
  eapply Map_Get_Value_Eq.
    apply H.
    apply H0.
Qed.

(* Function for looking up the static type of a variable.
If v exists in F, it returns the type otherwise it returns None *)
Definition FieldType (h : StackFrame) (v : ID) : option Unit :=
  match StackFrame_Get h v with
  | Some (pair u v) => Some u
  | None => None
  end.

Theorem FieldType_Content_Eq:
  forall (h : StackFrame) (v : ID) (T1 T2 : Unit),
  FieldType h v = Some T1 ->
  FieldType h v = Some T2 ->
  T1 = T2.
Proof.
  intros.
  rewrite -> H in H0. inversion H0. reflexivity.
Qed.

(* function for looking up the field value of a field *)
Definition FieldValue (h : StackFrame) (v : ID) : option Value :=
  match StackFrame_Get h v with
  | Some (pair u v) => Some v
  | None => None
  end.

Theorem FieldValue_Content_Eq:
  forall (h : StackFrame) (v : ID) (l1 l2 : Value),
  FieldValue h v = Some l1 ->
  FieldValue h v = Some l2 ->
  l1 = l2.
Proof.
  intros.
  rewrite -> H in H0. inversion H0. reflexivity.
Qed.

Theorem StackFrame_Contains_Implies_Get :
  forall (h : StackFrame) (v : ID),
  StackFrame_Contains h v = true ->
  exists (Tv Tl : Unit) (z : nat), StackFrame_Get h v = Some (Tv, Val Tl z).
Proof.
  unfold StackFrame_Contains.
  unfold StackFrame_Get.
  intros.
  unfold Map_Contains in H.
  destruct (Map_Get id_beq h v).
    destruct h0. destruct v.
    exists u. exists u0. exists n. reflexivity.
    inversion H.
Qed.

Theorem StackFrame_Contains_Implies_FieldType :
  forall (h : StackFrame) (v : ID),
  StackFrame_Contains h v = true ->
  exists (Tv : Unit), FieldType h v = Some Tv.
Proof.
  intros.
  unfold FieldType.
  apply StackFrame_Contains_Implies_Get in H.
  inversion H as [Tv]. inversion H0 as [Tl]. inversion H1 as [z].
  rewrite -> H2.
  exists Tv. reflexivity.
Qed.

Theorem StackFrame_Contains_Implies_FieldValue :
  forall (h : StackFrame) (v : ID),
  StackFrame_Contains h v = true ->
  exists (Tl : Unit) (z : nat), FieldValue h v = Some (Val Tl z).
Proof.
  intros.
  unfold FieldValue.
  apply StackFrame_Contains_Implies_Get in H.
  inversion H as [Tv]. inversion H0 as [Tl]. inversion H1 as [z].
  rewrite -> H2.
  exists Tl, z. reflexivity.
Qed.

Theorem StackFrame_Update_FieldType_Eq :
  forall (h : StackFrame) (v : ID) (Tv Tl : Unit) (z : nat),
  FieldType (StackFrame_Update h v Tv Tl z) v = Some Tv.
Proof.
  intros.
  unfold FieldType. unfold StackFrame_Update. unfold StackFrame_Get.
  induction h; subst; simpl.
  (* Case : h is empty *)
    rewrite -> id_beq_true. reflexivity.
  (* Case : h has one or more elements *)
    destruct a as [v' hv']. destruct hv' as [Tl' z'].
    destruct (id_eq_dec v v'); subst.
      rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      rewrite -> id_beq_false. simpl.
        rewrite -> id_beq_false.
          apply IHh.
          apply n.
        apply n.
Qed.

Theorem StackFrame_Update_FieldType_Neq :
  forall (h : StackFrame) (f1 f2 : ID) (Tv Tl : Unit) (z : nat),
  f2 <> f1 ->
  FieldType (StackFrame_Update h f1 Tv Tl z) f2 = FieldType h f2.
Proof.
  intros.
  unfold FieldType. unfold StackFrame_Update. unfold StackFrame_Get.
  induction h; subst; simpl.
  (* Case : h is empty *)
    rewrite -> id_beq_false. reflexivity. apply H.
  (* Case : h has one or more elements *)
    destruct a as [v' hv']. destruct hv' as [Tl' z'].
    destruct (id_eq_dec f1 v'); subst.
      rewrite -> id_beq_true. simpl. rewrite -> id_beq_false.
        rewrite -> id_beq_false.
          reflexivity.
          apply H.
        apply H.
      rewrite -> id_beq_false. simpl.
        destruct (id_eq_dec f2 v'); subst.
          rewrite -> id_beq_true. rewrite -> id_beq_true. reflexivity.
          rewrite -> id_beq_false.
            rewrite -> id_beq_false.
              apply IHh.
              apply n0.
            apply n0.
        apply n.
Qed.

Theorem StackFrame_Update_FieldValue_Eq :
  forall (h : StackFrame) (v : ID) (Tv Tl : Unit) (z : nat),
  FieldValue (StackFrame_Update h v Tv Tl z) v = Some (Val Tl z).
Proof.
  intros.
  unfold FieldValue. unfold StackFrame_Update. unfold StackFrame_Get.
  induction h; subst; simpl.
  (* Case : h is empty *)
    rewrite -> id_beq_true. reflexivity.
  (* Case : h has one or more elements *)
    destruct a as [f' hv']. destruct hv' as [Tl' z'].
    destruct (id_eq_dec f f'); subst.
      rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      rewrite -> id_beq_false. simpl.
        rewrite -> id_beq_false.
          apply IHh.
          apply n.
        apply n.
Qed.

Theorem StackFrame_Update_FieldValue_Neq :
  forall (h : StackFrame) (f1 f2 : ID) (Tv Tl : Unit) (z : nat),
  f2 <> f1 ->
  FieldValue (StackFrame_Update h f1 Tv Tl z) f2 = FieldValue h f2.
Proof.
  intros.
  unfold FieldValue. unfold StackFrame_Update. unfold StackFrame_Get.
  induction h; subst; simpl.
  (* Case : h is empty *)
    rewrite -> id_beq_false. reflexivity. apply H.
  (* Case : h has one or more elements *)
    destruct a as [f' hv']. destruct hv' as [Tl' z'].
    destruct (id_eq_dec f1 f'); subst.
      rewrite -> id_beq_true. simpl. rewrite -> id_beq_false.
        rewrite -> id_beq_false.
          reflexivity.
          apply H.
        apply H.
      rewrite -> id_beq_false. simpl.
        destruct (id_eq_dec f2 f'); subst.
          rewrite -> id_beq_true. rewrite -> id_beq_true. reflexivity.
          rewrite -> id_beq_false.
            rewrite -> id_beq_false.
              apply IHh.
              apply n0.
            apply n0.
        apply n.
Qed.
