From PUnits Require Import UnitsDefs.
From PUnits Require Import IDDefs.
From PUnits Require Import ValueDefs.
From PUnits Require Import MapsDefs.

(* Heap is a map from IDs to pairs of its field type and value
we use Coq's built in pair data structure
h = f -> Tf, (Tv, n)
*)
Definition HeapValue : Type := prod Unit Value.

Definition HeapValue_beq ( hv1 hv2 : HeapValue ) : bool :=
  match hv1, hv2 with
  | (u1, v1), (u2, v2) => if unit_beq u1 u2 then if Value_beq v1 v2 then true else false else false
  end.

Definition Heap := Map ID HeapValue.
Definition empty_heap := Empty_Map ID HeapValue.
Definition Heap_Update (h : Heap) (f : ID) (Tf Tv : Unit) (z : nat) : Heap := Map_Add id_beq h f (Tf, Val Tv z).
Definition Heap_Get (h : Heap) (f : ID) : option HeapValue := Map_Get id_beq h f.
Definition Heap_Contains (h : Heap) (f : ID) : bool := Map_Contains id_beq h f.
Definition Heap_IsSubMap (h1 h2 : Heap) : bool := Map_IsSubMap id_beq HeapValue_beq h1 h2.
Hint Unfold Heap_Update.

Theorem Heap_Get_Content_Eq :
  forall (h : Heap) (f : ID) (v1 v2 : option HeapValue),
  Heap_Get h f = v1 ->
  Heap_Get h f = v2 ->
  v1 = v2.
Proof.
  unfold Heap_Get.
  intros.
  eapply Map_Get_Value_Eq.
    apply H.
    apply H0.
Qed.

(* function for looking up the field type of a field
  if f exists in the heap, it returns the type
  otherwise it returns None
 *)
Definition FieldType (h : Heap) (f : ID) : option Unit :=
  match Heap_Get h f with
  | Some (pair u v) => Some u
  | None => None
  end.

Theorem FieldType_Content_Eq:
  forall (h : Heap) (f : ID) (T1 T2 : Unit),
  FieldType h f = Some T1 ->
  FieldType h f = Some T2 ->
  T1 = T2.
Proof.
  intros.
  rewrite -> H in H0. inversion H0. reflexivity.
Qed.

(* function for looking up the field value of a field *)
Definition FieldValue (h : Heap) (f : ID) : option Value :=
  match Heap_Get h f with
  | Some (pair u v) => Some v
  | None => None
  end.

Theorem FieldValue_Content_Eq:
  forall (h : Heap) (f : ID) (v1 v2 : Value),
  FieldValue h f = Some v1 ->
  FieldValue h f = Some v2 ->
  v1 = v2.
Proof.
  intros.
  rewrite -> H in H0. inversion H0. reflexivity.
Qed.

Theorem Heap_Contains_Implies_Get :
  forall (h : Heap) (f : ID),
  Heap_Contains h f = true ->
  exists (Tf Tv : Unit) (z : nat), Heap_Get h f = Some (Tf, Val Tv z).
Proof.
  unfold Heap_Contains.
  unfold Heap_Get.
  intros.
  unfold Map_Contains in H.
  destruct (Map_Get id_beq h f).
    destruct h0. destruct v.
    exists u. exists u0. exists n. reflexivity.
    inversion H.
Qed.

Theorem Heap_Contains_Implies_FieldType :
  forall (h : Heap) (f : ID),
  Heap_Contains h f = true ->
  exists (Tf : Unit), FieldType h f = Some Tf.
Proof.
  intros.
  unfold FieldType.
  apply Heap_Contains_Implies_Get in H.
  inversion H as [Tf]. inversion H0 as [Tv]. inversion H1 as [z].
  rewrite -> H2.
  exists Tf. reflexivity.
Qed.

Theorem Heap_Contains_Implies_FieldValue :
  forall (h : Heap) (f : ID),
  Heap_Contains h f = true ->
  exists (Tv : Unit) (z : nat), FieldValue h f = Some (Val Tv z).
Proof.
  intros.
  unfold FieldValue.
  apply Heap_Contains_Implies_Get in H.
  inversion H as [Tf]. inversion H0 as [Tv]. inversion H1 as [z].
  rewrite -> H2.
  exists Tv, z. reflexivity.
Qed.

Theorem Heap_Update_FieldType_Eq :
  forall (h : Heap) (f : ID) (Tf Tv : Unit) (z : nat),
  FieldType (Heap_Update h f Tf Tv z) f = Some Tf.
Proof.
  intros.
  unfold FieldType. unfold Heap_Update. unfold Heap_Get.
  induction h; subst; simpl.
  (* Case : h is empty *)
    rewrite -> id_beq_true. reflexivity.
  (* Case : h has one or more elements *)
    destruct a as [f' hv']. destruct hv' as [Tv' z'].
    destruct (id_eq_dec f f'); subst.
      rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      rewrite -> id_beq_false. simpl.
        rewrite -> id_beq_false.
          apply IHh.
          apply n.
        apply n.
Qed.

Theorem Heap_Update_FieldType_Neq :
  forall (h : Heap) (f1 f2 : ID) (Tf Tv : Unit) (z : nat),
  f2 <> f1 ->
  FieldType (Heap_Update h f1 Tf Tv z) f2 = FieldType h f2.
Proof.
  intros.
  unfold FieldType. unfold Heap_Update. unfold Heap_Get.
  induction h; subst; simpl.
  (* Case : h is empty *)
    rewrite -> id_beq_false. reflexivity. apply H.
  (* Case : h has one or more elements *)
    destruct a as [f' hv']. destruct hv' as [Tv' z'].
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

Theorem Heap_Update_FieldValue_Eq :
  forall (h : Heap) (f : ID) (Tf Tv : Unit) (z : nat),
  FieldValue (Heap_Update h f Tf Tv z) f = Some (Val Tv z).
Proof.
  intros.
  unfold FieldValue. unfold Heap_Update. unfold Heap_Get.
  induction h; subst; simpl.
  (* Case : h is empty *)
    rewrite -> id_beq_true. reflexivity.
  (* Case : h has one or more elements *)
    destruct a as [f' hv']. destruct hv' as [Tv' z'].
    destruct (id_eq_dec f f'); subst.
      rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      rewrite -> id_beq_false. simpl.
        rewrite -> id_beq_false.
          apply IHh.
          apply n.
        apply n.
Qed.

Theorem Heap_Update_FieldValue_Neq :
  forall (h : Heap) (f1 f2 : ID) (Tf Tv : Unit) (z : nat),
  f2 <> f1 ->
  FieldValue (Heap_Update h f1 Tf Tv z) f2 = FieldValue h f2.
Proof.
  intros.
  unfold FieldValue. unfold Heap_Update. unfold Heap_Get.
  induction h; subst; simpl.
  (* Case : h is empty *)
    rewrite -> id_beq_false. reflexivity. apply H.
  (* Case : h has one or more elements *)
    destruct a as [f' hv']. destruct hv' as [Tv' z'].
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
