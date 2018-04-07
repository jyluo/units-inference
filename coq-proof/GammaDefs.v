Require Import Bool.
Require Import UnitsDefs.
Require Import IDDefs.
Require Import MapsDefs.

(* Gamma is a map from IDs to Types *)

Definition Gamma := Map ID Unit.
Definition empty_gamma := Empty_Map ID Unit.
Definition Gamma_Extend (g : Gamma) (f : ID) (T : Unit) : Gamma := Map_Add id_beq g f T.
Definition Gamma_Get (g : Gamma) (f : ID) : option Unit := Map_Get id_beq g f.
Definition Gamma_Contains (g : Gamma) (f : ID) : bool := Map_Contains id_beq g f.
Definition Gamma_IsSTbMap (g1 g2 : Gamma) : bool := Map_IsSubMap id_beq unit_beq g1 g2.
Hint Unfold Gamma_Extend.

Theorem Gamma_Get_Content_Eq :
  forall (g : Gamma) (f : ID) (T1 T2 : option Unit),
  Gamma_Get g f = T1 ->
  Gamma_Get g f = T2 ->
  T1 = T2.
Proof.
  unfold Gamma_Get.
  intros.
  eapply Map_Get_Value_Eq.
    apply H.
    apply H0.
Qed.

Theorem Gamma_Contains_Implies_Get :
  forall (g : Gamma) (f : ID),
  Gamma_Contains g f = true ->
  exists (T : Unit), Gamma_Get g f = Some T.
Proof.
  unfold Gamma_Contains.
  unfold Gamma_Get.
  apply Map_Contains_Implies_Get.
Qed.

Theorem Gamma_Extend_Shadow :
  forall (g : Gamma) (f : ID) (T : Unit),
  Gamma_Extend (Gamma_Extend g f T) f T = Gamma_Extend g f T.
Proof.
  intros.
  unfold Gamma_Extend.
  induction g.
    simpl. rewrite -> id_beq_true. reflexivity.
    destruct a as [f' T'].
    destruct (id_eq_dec f f'); subst.
      simpl. rewrite -> id_beq_true. simpl. rewrite -> id_beq_true. reflexivity.
      simpl. rewrite -> id_beq_false. simpl. rewrite -> id_beq_false. rewrite -> IHg. reflexivity. apply n. apply n.
Qed.
