From PUnits Require Import UnitsDefs.

(* Print Visibility. *)

(* Subtype and LUB definitions. *)

Definition isSubtype(u1 u2 : Unit) : bool :=
  match u1, u2 with
    | bottom, top => true
    | declaredUnit nu, top => true
    | bottom, declaredUnit nu => true
    | _, _ => if unit_eq_dec u1 u2 then true else false
  end.
Notation "Q <: T" := (isSubtype Q T) (at level 0) : core_scope.

Module Subtype_Test.
Example top_not_subtype_of_bottom : top <: bottom = false.
Proof. simpl. destruct unit_eq_dec. inversion e. reflexivity. Qed.

Example meter_not_subtype_of_second : (declaredUnit m) <: (declaredUnit s) = false.
Proof. simpl. destruct unit_eq_dec. inversion e. reflexivity. Qed.
End Subtype_Test.

Theorem top_is_always_supertype : forall u : Unit, u <: top = true.
Proof. intros u. induction u; simpl. destruct unit_eq_dec. reflexivity. destruct n. reflexivity. reflexivity. reflexivity. Qed.

Theorem bottom_is_always_subtype : forall u : Unit, bottom <: u = true.
Proof. intros u. induction u; simpl. reflexivity. destruct unit_eq_dec. reflexivity. destruct n. reflexivity. reflexivity. Qed.

Theorem same_unit_is_subtype : forall nu : NormalizedUnit, (declaredUnit nu) <: (declaredUnit nu) = true.
Proof. intros nu. simpl. destruct unit_eq_dec. reflexivity. destruct n. reflexivity. Qed.

Theorem subtype_reflexive :
  forall u : Unit, u <: u = true.
Proof.
  intros u.
  induction u.
    apply top_is_always_supertype.
    apply bottom_is_always_subtype.
    apply same_unit_is_subtype.
Qed.

Theorem subtype_true_iff_unit_equal :
  forall nu1 nu2 : NormalizedUnit, (declaredUnit nu1) <: (declaredUnit nu2) = true <-> nu1 = nu2.
Proof.
  intros. simpl. split.
  (* Case -> *)
    intros Hsub.
      destruct unit_eq_dec in Hsub.
        inversion e. reflexivity.
        inversion Hsub.
  (* Case <- *)
    intros Heq; subst.
      apply same_unit_is_subtype.
Qed.

Theorem subtype_transitive :
  forall u v w : Unit, u <: v = true -> v <: w = true -> u <: w = true.
Proof.
  intros u v w Huv Hvw.
  induction u, v, w; simpl;
    try reflexivity;
    try inversion Hvw;
    try inversion Huv.
      rewrite -> H1. rewrite -> H1. apply H1.
      rewrite -> H1. rewrite -> H0. apply H0.
      rewrite -> H1. rewrite -> H0. apply H0.
      rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H1. rewrite -> H0. apply H1.
      rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H1. rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H1. rewrite -> H0. destruct unit_eq_dec. inversion e. subst. apply H1. inversion H0.
      rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H1. rewrite -> H1. apply H1.
      rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H1. rewrite -> H0. apply H1.
      rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H1. rewrite -> H0. destruct unit_eq_dec. inversion e. inversion H0.
      rewrite -> H1. rewrite -> H0. destruct unit_eq_dec. inversion e. subst. apply H1. inversion H0.
Qed.

(* LUB definition *)
Definition LUB(u1 u2 : Unit) : Unit :=
  if u1 <: u2 then u2
  else if u2 <: u1 then u1
  else top. (* the only case where u1 is not a subtype of u2 is if both are different declared units *)

Theorem LUB_reflexive :
  forall u : Unit, LUB u u = u.
Proof.
  intros.
  unfold LUB; simpl.
  rewrite -> subtype_reflexive. reflexivity.
Qed.

Theorem LUB_commutative :
  forall u1 u2 : Unit, LUB u1 u2 = LUB u2 u1.
Proof.
  intros.
  induction u1, u2; try reflexivity; try unfold LUB; simpl.
    destruct unit_eq_dec. inversion e. reflexivity.
    destruct unit_eq_dec. inversion e. reflexivity.
    destruct unit_eq_dec. inversion e. reflexivity.
    destruct unit_eq_dec. inversion e. reflexivity.
    destruct unit_eq_dec. inversion e. reflexivity.
    destruct unit_eq_dec. inversion e. reflexivity.
    destruct unit_eq_dec. 
      destruct unit_eq_dec. apply e0. reflexivity.
      reflexivity.
Qed.

Theorem LUB_top_T_is_top :
  forall T : Unit, LUB top T = top.
Proof.
  intros.
  induction T; subst; try unfold LUB; try simpl.
    rewrite -> unit_eq_dec_true. reflexivity.
    rewrite -> unit_eq_dec_false. reflexivity. discriminate.
    rewrite -> unit_eq_dec_false. reflexivity. discriminate.
Qed.

Theorem LUB_bottom_T_is_T :
  forall T : Unit, LUB bottom T = T.
Proof.
  intros.
  induction T; subst; try unfold LUB; try simpl.
    reflexivity.
    rewrite -> unit_eq_dec_true. reflexivity.
    reflexivity.
Qed.
