Require Import Bool.
Require Import UnitsDefs.
Require Import IDDefs.
Require Import MapsDefs.

(* Gamma is a map from IDs to Types *)

Definition Gamma := Map ID Unit.
Definition empty_gamma := Empty_Map ID Unit.
Definition Gamma_Extend (g : Gamma) (f : ID) (T : Unit) : Gamma := Map_Append id_beq g f T.
Definition Gamma_Get (g : Gamma) (f : ID) : option Unit := Map_Get id_beq g f.
Definition Gamma_Contains (g : Gamma) (f : ID) : bool := Map_Contains id_beq g f.
Definition Gamma_IsSTbMap (g1 g2 : Gamma) : bool := Map_IsSubMap id_beq unit_beq g1 g2.
Hint Unfold Gamma_Extend.

Theorem Gamma_Get_Content_Eq :
  forall (g : Gamma) (f : ID) (T1 T2 : Unit),
  Gamma_Get g f = Some T1 ->
  Gamma_Get g f = Some T2 ->
  T1 = T2.
Proof.
  unfold Gamma_Get.
  intros.
  assert (Some T1 = Some T2).
  eapply Map_Get_Value_Eq.
    apply H.
    apply H0.
  inversion H1. reflexivity.
Qed.


Theorem Gamma_Get_No_Shadow:
  forall (g : Gamma) (f : ID) (T1 T2 : Unit),
  Gamma_Extend (Gamma_Extend g f T1) f T2 = Gamma_Extend g f T1.
Proof.
  intros.
  unfold Gamma_Extend.
  apply Map_Append_No_Shadow. apply id_eq_true.
Qed.

(*
Theorem Gamma_Get_Extend_Same :
  forall (g : Gamma) (f : ID) (T : Unit),
  Gamma_Get (Gamma_Extend g f T) f = Some T.
Proof.
  intros.
  unfold Gamma_Get. unfold Gamma_Extend.
  induction g; subst.
    simpl. rewrite -> id_beq_true. reflexivity.
    destruct a as [f' T'].
    destruct (id_eq_dec f f'); subst.
      simpl. rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      simpl. rewrite -> id_beq_false. simpl. rewrite -> id_beq_false. apply IHg.
        apply n. apply n.
Qed.
*)

Theorem Gamma_Get_Extend_Not_Same :
  forall (g : Gamma) (f f' : ID) (T' : Unit),
  f <> f' ->
  Gamma_Get (Gamma_Extend g f' T') f = Gamma_Get g f.
Proof.
  intros.
  unfold Gamma_Get. unfold Gamma_Extend.
  induction g; subst.
    simpl. apply id_beq_false. apply H.
    destruct a as [fa Ta]; subst.
    destruct (id_eq_dec f fa); subst.
      simpl. rewrite -> id_beq_false. simpl. rewrite -> id_beq_true. rewrite -> id_beq_true. reflexivity. intuition.
      destruct (id_eq_dec f' fa); subst.
        simpl. rewrite -> id_beq_true. simpl. rewrite -> id_beq_false. reflexivity. auto.
        simpl. rewrite -> id_beq_false. simpl. rewrite -> id_beq_false. rewrite -> id_beq_false. apply IHg. auto. auto. auto.
Qed.

Theorem Gamma_Contains_Extend_Same :
  forall (g : Gamma) (f : ID) (T : Unit),
  Gamma_Contains (Gamma_Extend g f T) f = true.
Proof.
  intros.
  unfold Gamma_Contains. unfold Gamma_Extend.
  induction g; subst.
    unfold Map_Contains. simpl. rewrite -> id_beq_true. reflexivity.
    destruct a as [f' T'].
    destruct (id_eq_dec f f'); subst.
      unfold Map_Contains. simpl. rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      unfold Map_Contains. simpl. rewrite -> id_beq_false. simpl. rewrite -> id_beq_false. apply IHg.
        apply n. apply n.
Qed.

Theorem Gamma_Contains_Extend_Not_Same :
  forall (g : Gamma) (f f' : ID) (T' : Unit),
  f <> f' ->
  Gamma_Contains (Gamma_Extend g f' T') f = Gamma_Contains g f.
Proof.
  intros.
  unfold Gamma_Contains. unfold Gamma_Extend. unfold Map_Contains.
  induction g; subst.
    simpl. rewrite -> id_beq_false. reflexivity. apply H.
    destruct a as [fa Ta]; subst.
    destruct (id_eq_dec f fa); subst.
      simpl. rewrite -> id_beq_false. simpl. rewrite -> id_beq_true. rewrite -> id_beq_true. reflexivity. intuition.
      destruct (id_eq_dec f' fa); subst.
        simpl. rewrite -> id_beq_true. simpl. rewrite -> id_beq_false. reflexivity. auto.
        simpl. rewrite -> id_beq_false. simpl. rewrite -> id_beq_false. rewrite -> id_beq_false. apply IHg. auto. auto. auto.
Qed.

Theorem Gamma_Contains_Implies_Get :
  forall (g : Gamma) (f : ID),
  Gamma_Contains g f = true <->
  exists (T : Unit), Gamma_Get g f = Some T.
Proof.
  unfold Gamma_Contains.
  unfold Gamma_Get.
  apply Map_Contains_Implies_Get.
Qed.

(*
Theorem Gamma_Extend_Shadow :
  forall (g : Gamma) (f : ID) (T1 T2 : Unit),
  Gamma_Extend (Gamma_Extend g f T1) f T2 = Gamma_Extend g f T2.
Proof.
  intros.
  unfold Gamma_Extend.
  induction g.
    simpl. rewrite -> id_beq_true. reflexivity.
    destruct a as [f' T'].
    destruct (id_eq_dec f f'); subst.
      simpl. rewrite -> id_beq_true. rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      simpl. rewrite -> id_beq_false. rewrite -> id_beq_false. simpl. rewrite -> id_beq_false. rewrite -> IHg. reflexivity.
        apply n. apply n. apply n.
Qed.
*)

Theorem Gamma_Extend_Contains :
  forall (g : Gamma) (f f' : ID) (T' : Unit),
  Gamma_Contains g f = true ->
  Gamma_Contains (Gamma_Extend g f' T') f = true.
Proof.
  intros.
  destruct (id_eq_dec f' f); subst.
    apply Gamma_Contains_Extend_Same.
    rewrite <- H. apply Gamma_Contains_Extend_Not_Same. intuition.
Qed.
