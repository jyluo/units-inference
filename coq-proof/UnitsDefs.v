Require Import Bool.
Require Import Arith.
Require Import EqNat.
Require Import List.
Import List.ListNotations.
Require Import Lists.ListSet.

(* Print Visibility. *)

(* Base units, here we instantiate with all 7 base SI units *)
Inductive BaseUnit : Type :=
  | meter : BaseUnit
  | second : BaseUnit
  | gram : BaseUnit
  | ampere : BaseUnit
  | kelvin : BaseUnit
  | candela : BaseUnit
  | mole : BaseUnit.

Inductive BaseUnitComponent : Type :=
  | bc : BaseUnit -> nat -> BaseUnitComponent.

(* Base 10 prefix *)
Inductive PrefixBases : Type :=
  | ten : PrefixBases.

Inductive PrefixComponent : Type :=
  | pc : PrefixBases -> nat -> PrefixComponent.

(* A normalized unit is a prefix component + a set of base unit components *)
Inductive NormalizedUnit : Type :=
  | normUnit: PrefixComponent -> set BaseUnitComponent -> NormalizedUnit.

(* Some example definitions of units *)
Definition m := normUnit (pc ten 0) [bc meter 1 ; bc second 0 ; bc gram 0].
Definition km := normUnit (pc ten 3) [bc meter 1 ; bc second 0 ; bc gram 0].
Definition m2 := normUnit (pc ten 0) [bc meter 2 ; bc second 0 ; bc gram 0].
Definition s := normUnit (pc ten 0) [bc meter 0 ; bc second 1 ; bc gram 0].
Definition g := normUnit (pc ten 0) [bc meter 0 ; bc second 0 ; bc gram 1].
Definition dimensionless := normUnit (pc ten 0) [bc meter 0 ; bc second 0 ; bc gram 0].

(* Units qualifiers *)
Inductive Unit : Type :=
  | top : Unit
  | bottom : Unit
  | declaredUnit : NormalizedUnit -> Unit.

(* equality definitions *)

(* ======================================================================= *)

Module buEqualTest.
Example test1 : meter = meter. reflexivity. Qed.
Example test2 : meter <> gram. discriminate. Qed.
End buEqualTest.

Theorem baseUnit_eq_dec :
  forall bu1 bu2 : BaseUnit,
  {bu1 = bu2} + {bu1 <> bu2}.
Proof.
  intros.
  induction bu1, bu2; subst;
    try (left; reflexivity);
    try (right; discriminate).
Qed.

Theorem baseUnit_eq_dec_true :
  forall (bu : BaseUnit) (T : Type) (t f : T),
  (if baseUnit_eq_dec bu bu then t else f) = t.
Proof.
  intros.
  destruct baseUnit_eq_dec.
    reflexivity.
    contradiction n. reflexivity.
Qed.

Theorem baseUnit_eq_dec_false :
  forall (bu1 bu2 : BaseUnit) (T : Type) (t f : T),
  bu1 <> bu2 ->
  (if baseUnit_eq_dec bu1 bu2 then t else f) = f.
Proof.
  intros.
  destruct baseUnit_eq_dec; subst.
    contradiction H. reflexivity.
    reflexivity.
Qed.

(* ======================================================================= *)

Module bcEqualTest.
Example test1 : (bc meter 5) = (bc meter 5). reflexivity. Qed.
Example test2 : (bc meter 5) <> (bc meter 4). intros contra. inversion contra. Qed.
Example test3 : (bc meter 5) <> (bc second 5). intros contra. inversion contra. Qed.
End bcEqualTest.

Theorem baseUnitComponent_eq_dec :
  forall bc1 bc2 : BaseUnitComponent,
  {bc1 = bc2} + {bc1 <> bc2}.
Proof.
  intros.
  destruct bc1, bc2; simpl; subst.
  destruct (eq_nat_dec n n0) as [HnEQ | HnNEQ]; destruct (baseUnit_eq_dec b b0) as [HbuEQ | HbuNEQ].
    left. rewrite -> HnEQ. rewrite -> HbuEQ. reflexivity.
    right. rewrite -> HnEQ. intros contra. inversion contra. apply HbuNEQ. apply H0.
    right. rewrite -> HbuEQ. intros contra. inversion contra. apply HnNEQ. apply H0.
    right.
      unfold not in HnNEQ. unfold not in HbuNEQ. unfold not.
      intros contra. inversion contra.
      apply HnNEQ. apply H1.
Qed.

Theorem baseUnitComponent_eq_dec_true :
  forall (bc : BaseUnitComponent) (T : Type) (t f : T),
  (if baseUnitComponent_eq_dec bc bc then t else f) = t.
Proof.
  intros.
  destruct baseUnitComponent_eq_dec.
    reflexivity.
    contradiction n. reflexivity.
Qed.

Theorem baseUnitComponent_eq_dec_false :
  forall (bc1 bc2 : BaseUnitComponent) (T : Type) (t f : T),
  bc1 <> bc2 ->
  (if baseUnitComponent_eq_dec bc1 bc2 then t else f) = f.
Proof.
  intros.
  destruct baseUnitComponent_eq_dec; subst.
    contradiction H. reflexivity.
    reflexivity.
Qed.

(* ======================================================================= *)

Module setBcEqualTest.
Example test1 : [bc meter 1 ; bc second 0 ; bc gram 0] = [bc meter 1 ; bc second 0 ; bc gram 0]. reflexivity. Qed.
Example test2 : [bc meter 1 ; bc second 0] <> [bc meter 1 ; bc second 0 ; bc gram 0]. intros contra. inversion contra. Qed.
Example test3 : [bc meter 1 ; bc second 0 ; bc gram 0] <> [bc meter 1 ; bc second 0]. intros contra. inversion contra. Qed.
Example test4 : [bc meter 1 ; bc second 0 ; bc gram 0] <> [bc meter 2 ; bc second 0 ; bc gram 0]. intros contra. inversion contra. Qed.
Example test5 : [bc meter 1 ; bc second 0 ; bc gram 0] <> [bc meter 1 ; bc second 0 ; bc gram 3]. intros contra. inversion contra. Qed.
End setBcEqualTest.

Theorem baseComponentSet_eq_dec :
  forall bcs1 bcs2 : set BaseUnitComponent,
  {bcs1 = bcs2} + {bcs1 <> bcs2}.
Proof.
  intros.
  destruct (list_eq_dec baseUnitComponent_eq_dec bcs1 bcs2) as [Heq | Hneq]; subst.
    left. reflexivity.
    right. apply Hneq.
Qed.

Theorem baseComponentSet_eq_dec_true :
  forall (bcs : set BaseUnitComponent) (T : Type) (t f : T),
  (if baseComponentSet_eq_dec bcs bcs then t else f) = t.
Proof.
  intros.
  destruct baseComponentSet_eq_dec.
    reflexivity.
    contradiction n. reflexivity.
Qed.

Theorem baseComponentSet_eq_dec_false :
  forall (bcs1 bcs2 : set BaseUnitComponent) (T : Type) (t f : T),
  bcs1 <> bcs2 ->
  (if baseComponentSet_eq_dec bcs1 bcs2 then t else f) = f.
Proof.
  intros.
  destruct baseComponentSet_eq_dec; subst.
    contradiction H. reflexivity.
    reflexivity.
Qed.

(* ======================================================================= *)

Module pcEqualTest.
Example test1 : (pc ten 5) = (pc ten 5). reflexivity. Qed.
Example test2 : (pc ten 5) <> (pc ten 4). intros contra. inversion contra. Qed.
End pcEqualTest.

Theorem prefixComponent_eq_dec :
  forall pc1 pc2 : PrefixComponent,
  {pc1 = pc2} + {pc1 <> pc2}.
Proof.
  intros.
  destruct pc1, pc2; simpl; subst.
  destruct p, p0.
  destruct (eq_nat_dec n n0) as [HnEQ | HnNEQ]; subst.
    left. reflexivity.
    right. intros contra. inversion contra. apply HnNEQ. apply H0.
Qed.

Theorem prefixComponent_eq_dec_true :
  forall (pc : PrefixComponent) (T : Type) (t f : T),
  (if prefixComponent_eq_dec pc pc then t else f) = t.
Proof.
  intros.
  destruct prefixComponent_eq_dec.
    reflexivity.
    contradiction n. reflexivity.
Qed.

Theorem prefixComponent_eq_dec_false :
  forall (pc1 pc2 : PrefixComponent) (T : Type) (t f : T),
  pc1 <> pc2 -> (if prefixComponent_eq_dec pc1 pc2 then t else f) = f.
Proof.
  intros.
  destruct prefixComponent_eq_dec; subst.
    contradiction H. reflexivity.
    reflexivity.
Qed.

(* ======================================================================= *)

Module nuEqualTest.
Example test1 : m = m. reflexivity. Qed.
Example test2 : m <> km. intros contra. inversion contra. Qed.
Example test3 : m <> m2. intros contra. inversion contra. Qed.
Example test4 : g <> dimensionless. intros contra. inversion contra. Qed.
End nuEqualTest.

Theorem normalizedUnit_eq_dec :
  forall nu1 nu2 : NormalizedUnit,
  {nu1 = nu2} + {nu1 <> nu2}.
Proof.
  intros.
  destruct nu1, nu2; simpl.
  destruct (prefixComponent_eq_dec p p0) as [HpEQ | HpNEQ]; destruct (baseComponentSet_eq_dec s0 s1) as [HlEQ | HlNEQ]; subst.
    left. reflexivity.
    right. intros contra. inversion contra. apply HlNEQ. apply H0.
    right. intros contra. inversion contra. apply HpNEQ. apply H0.
    right. intros contra. inversion contra. apply HpNEQ. apply H0.
Qed.

Theorem normalizedUnit_eq_dec_true :
  forall (nu : NormalizedUnit) (T : Type) (t f : T),
  (if normalizedUnit_eq_dec nu nu then t else f) = t.
Proof.
  intros.
  destruct normalizedUnit_eq_dec.
    reflexivity.
    contradiction n. reflexivity.
Qed.

Theorem normalizedUnit_eq_dec_false :
  forall (nu1 nu2 : NormalizedUnit) (T : Type) (t f : T), nu1 <> nu2 -> (if normalizedUnit_eq_dec nu1 nu2 then t else f) = f.
Proof.
  intros.
  destruct normalizedUnit_eq_dec; subst.
    contradiction H. reflexivity.
    reflexivity.
Qed.

(* ======================================================================= *)

Module uEqualTest.
Example test1 : top = top. reflexivity. Qed.
Example test2 : bottom = bottom. reflexivity. Qed.
Example test3 : (declaredUnit m) = (declaredUnit m). reflexivity. Qed.
Example test4 : top <> bottom. intros contra. inversion contra. Qed.
Example test5 : bottom <> top. intros contra. inversion contra. Qed.
Example test6 : top <> (declaredUnit m). intros contra. inversion contra. Qed.
Example test7 : (declaredUnit m) <> top. intros contra. inversion contra. Qed.
Example test8 : bottom <> (declaredUnit m). intros contra. inversion contra. Qed.
Example test9 : (declaredUnit m) <> bottom. intros contra. inversion contra. Qed.
Example test10: (declaredUnit m) <> (declaredUnit g). intros contra. inversion contra. Qed.
End uEqualTest.

Theorem unit_eq_dec :
  forall u1 u2 : Unit,
  {u1 = u2} + {u1 <> u2}.
Proof.
  intros.
  destruct u1, u2; subst.
    left; reflexivity.
    right; intros contra; inversion contra.
    right; intros contra; inversion contra.
    right; intros contra; inversion contra.
    left; reflexivity.
    right; intros contra; inversion contra.
    right; intros contra; inversion contra.
    right; intros contra; inversion contra.
    destruct (normalizedUnit_eq_dec n n0) as [HnEQ | HnNEQ]; subst.
      left; reflexivity.
      right; intros contra; inversion contra.
      apply HnNEQ. apply H0.
Qed.

Theorem unit_eq_dec_true :
  forall (u : Unit) (T : Type) (t f : T),
  (if unit_eq_dec u u then t else f) = t.
Proof.
  intros.
  destruct unit_eq_dec.
    reflexivity.
    contradiction n. reflexivity.
Qed.

Theorem unit_eq_dec_false :
  forall (T : Type) (u1 u2 : Unit) (t f : T),
  u1 <> u2 ->
  (if unit_eq_dec u1 u2 then t else f) = f.
Proof.
  intros.
  destruct unit_eq_dec; subst.
    contradiction H. reflexivity.
    reflexivity.
Qed.

Definition unit_beq (u1 u2 : Unit) : bool :=
  if unit_eq_dec u1 u2 then true else false.
Hint Unfold unit_beq : pUnitsHintDatabase.

Theorem unit_beq_true :
  forall (u : Unit),
  unit_beq u u = true.
Proof.
  intros. unfold unit_beq. apply unit_eq_dec_true.
Qed.

Theorem unit_beq_false :
  forall (u1 u2 : Unit),
  u1 <> u2 ->
  unit_beq u1 u2 = false.
Proof.
  intros. unfold unit_beq. apply unit_eq_dec_false. apply H.
Qed.

(* ======================================================================= *)

Definition dimensionlessUnit := declaredUnit dimensionless.
Definition mUnit := declaredUnit m.
Definition sUnit := declaredUnit s.
Definition gUnit := declaredUnit g.
Definition m2Unit := declaredUnit m2.

