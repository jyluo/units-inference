From PUnits Require Import UnitsDefs.
From PUnits Require Import IDDefs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import MapsDefs.

(* Stack Frame F is a map from Variable Identifiers v to pairs of its static
type Tv and labeled value l = Tl z. Formally v is mapped to a tuple, but for
implementation convenience we model l explicitly as a term and use Coq's
built-in pair data structure: F = v -> Tv, (Tl, n) .
*)
Definition StackFrameValue : Type := prod Unit LabeledLiteral.

Definition StackFrameValue_beq ( fv1 fv2 : StackFrameValue ) : bool :=
  match fv1, fv2 with
  | (u1, l1), (u2, l2) => if unit_beq u1 u2 then if LabeledLiteral_beq l1 l2 then true else false else false
  end.

Definition StackFrame := Map ID StackFrameValue.

Definition empty_stackframe := Empty_Map ID StackFrameValue.
Definition StackFrame_Update (f : StackFrame) (v : ID) (Tv Tl : Unit) (z : nat) : StackFrame := Map_Add id_beq f v (Tv, Val Tl z).
Definition StackFrame_Get (f : StackFrame) (v : ID) : option StackFrameValue := Map_Get id_beq f v.
Definition StackFrame_Contains (f : StackFrame) (v : ID) : bool := Map_Contains id_beq f v.
Definition StackFrame_IsSubMap (f1 f2 : StackFrame) : bool := Map_IsSubMap id_beq StackFrameValue_beq f1 f2.
Hint Unfold StackFrame_Update : pUnitsHintDatabase.

Theorem StackFrame_Get_Content_Eq :
  forall (f : StackFrame) (v : ID) (l1 l2 : option StackFrameValue),
  StackFrame_Get f v = l1 ->
  StackFrame_Get f v = l2 ->
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
Definition VarType (f : StackFrame) (v : ID) : option Unit :=
  match StackFrame_Get f v with
  | Some (pair u v) => Some u
  | None => None
  end.

Theorem VarType_Content_Eq:
  forall (f : StackFrame) (v : ID) (T1 T2 : Unit),
  VarType f v = Some T1 ->
  VarType f v = Some T2 ->
  T1 = T2.
Proof.
  intros.
  rewrite -> H in H0. inversion H0. reflexivity.
Qed.

(* function for looking up the labeled value of a variable *)
Definition VarValue (f : StackFrame) (v : ID) : option LabeledLiteral :=
  match StackFrame_Get f v with
  | Some (pair u v) => Some v
  | None => None
  end.

Theorem VarValue_Content_Eq:
  forall (f : StackFrame) (v : ID) (l1 l2 : LabeledLiteral),
  VarValue f v = Some l1 ->
  VarValue f v = Some l2 ->
  l1 = l2.
Proof.
  intros.
  rewrite -> H in H0. inversion H0. reflexivity.
Qed.

Theorem StackFrame_Contains_Implies_Get :
  forall (f : StackFrame) (v : ID),
  StackFrame_Contains f v = true ->
  exists (Tv Tl : Unit) (z : nat), StackFrame_Get f v = Some (Tv, Val Tl z).
Proof.
  unfold StackFrame_Contains.
  unfold StackFrame_Get.
  intros.
  unfold Map_Contains in H.
  destruct (Map_Get id_beq f v).
    destruct s. destruct l.
    exists u. exists u0. exists n. reflexivity.
    inversion H.
Qed.

Theorem StackFrame_Contains_Implies_VarType :
  forall (f : StackFrame) (v : ID),
  StackFrame_Contains f v = true ->
  exists (Tv : Unit), VarType f v = Some Tv.
Proof.
  intros.
  unfold VarType.
  apply StackFrame_Contains_Implies_Get in H.
  inversion H as [Tv]. inversion H0 as [Tl]. inversion H1 as [z].
  rewrite -> H2.
  exists Tv. reflexivity.
Qed.

Theorem StackFrame_Contains_Implies_VarValue :
  forall (f : StackFrame) (v : ID),
  StackFrame_Contains f v = true ->
  exists (Tl : Unit) (z : nat), VarValue f v = Some (Val Tl z).
Proof.
  intros.
  unfold VarValue.
  apply StackFrame_Contains_Implies_Get in H.
  inversion H as [Tv]. inversion H0 as [Tl]. inversion H1 as [z].
  rewrite -> H2.
  exists Tl, z. reflexivity.
Qed.

Theorem StackFrame_Update_VarType_Eq :
  forall (f : StackFrame) (v : ID) (Tv Tl : Unit) (z : nat),
  VarType (StackFrame_Update f v Tv Tl z) v = Some Tv.
Proof.
  intros.
  unfold VarType. unfold StackFrame_Update. unfold StackFrame_Get.
  induction f; subst; simpl.
  (* Case : f is empty *)
    rewrite -> id_beq_true. reflexivity.
  (* Case : f has one or more elements *)
    destruct a as [v' hv']. destruct hv' as [Tl' z'].
    destruct (id_eq_dec v v'); subst.
      rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      rewrite -> id_beq_false. simpl.
        rewrite -> id_beq_false.
          apply IHf.
          apply n.
        apply n.
Qed.

Theorem StackFrame_Update_VarType_Neq :
  forall (f : StackFrame) (f1 f2 : ID) (Tv Tl : Unit) (z : nat),
  f2 <> f1 ->
  VarType (StackFrame_Update f f1 Tv Tl z) f2 = VarType f f2.
Proof.
  intros.
  unfold VarType. unfold StackFrame_Update. unfold StackFrame_Get.
  induction f; subst; simpl.
  (* Case : f is empty *)
    rewrite -> id_beq_false. reflexivity. apply H.
  (* Case : f has one or more elements *)
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
              apply IHf.
              apply n0.
            apply n0.
        apply n.
Qed.

Theorem StackFrame_Update_VarValue_Eq :
  forall (f : StackFrame) (v : ID) (Tv Tl : Unit) (z : nat),
  VarValue (StackFrame_Update f v Tv Tl z) v = Some (Val Tl z).
Proof.
  intros.
  unfold VarValue. unfold StackFrame_Update. unfold StackFrame_Get.
  induction f; subst; simpl.
  (* Case : f is empty *)
    rewrite -> id_beq_true. reflexivity.
  (* Case : f has one or more elements *)
    destruct a as [v' hv']. destruct hv' as [Tl' z'].
    destruct (id_eq_dec v v'); subst.
      rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      rewrite -> id_beq_false. simpl.
        rewrite -> id_beq_false.
          apply IHf.
          apply n.
        apply n.
Qed.

Theorem StackFrame_Update_VarValue_Neq :
  forall (f : StackFrame) (f1 f2 : ID) (Tv Tl : Unit) (z : nat),
  f2 <> f1 ->
  VarValue (StackFrame_Update f f1 Tv Tl z) f2 = VarValue f f2.
Proof.
  intros.
  unfold VarValue. unfold StackFrame_Update. unfold StackFrame_Get.
  induction f; subst; simpl.
  (* Case : f is empty *)
    rewrite -> id_beq_false. reflexivity. apply H.
  (* Case : f has one or more elements *)
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
              apply IHf.
              apply n0.
            apply n0.
        apply n.
Qed.
