Require Import Bool.
Require Import List.
Import List.ListNotations.
Require Import Lists.ListSet.
Require Import EqNat.

(* Map data structure consistsing of a set of pairs. *)
Definition Map (K V : Type) := set (prod K V).
Definition Empty_Map (K V : Type) := empty_set (prod K V).

(* All key equality functions are decideable. *)
Theorem key_eq_dec :
  forall {K : Type} (key_eq : K -> K -> bool) (k1 k2 : K),
  {key_eq k1 k2 = true} + {key_eq k1 k2 <> true}.
Proof.
  intros.
  destruct (key_eq k1 k2).
    left. reflexivity.
    right. discriminate.
Qed.

(* Inserts or replaces k -> v into map m, given key_eq as a comparison
function. *)
Fixpoint Map_Add {K V : Type} (key_eq : K -> K -> bool) (m : Map K V) (k : K) (v : V) : Map K V :=
  match m with
  | [] => [ (k, v) ]
  | (k1, v1) :: m' => if key_eq k k1 then
                        (k, v) :: m'
                      else
                        (k1, v1) :: Map_Add key_eq m' k v
  end.

(* Gets the value v for given key k if k -> v is in the map, otherwise returns
None. *)
Fixpoint Map_Get {K V : Type} (key_eq : K -> K -> bool) (m : Map K V) (k : K) : option V :=
  match m with
  | [] => None
  | (k1, v1) :: m' => if key_eq k k1 then Some v1 else Map_Get key_eq m' k
  end.


Theorem Map_Get_Value_Eq :
  forall {K V : Type} (key_eq : K -> K -> bool) (m : Map K V) (k : K) (v1 v2 : option V),
  Map_Get key_eq m k = v1 ->
  Map_Get key_eq m k = v2 ->
  v1 = v2.
Proof.
  intros.
  rewrite H in H0. apply H0.
Qed.

Definition Map_Contains {K V : Type} (key_eq : K -> K -> bool) (m : Map K V) (k : K) : bool :=
  match Map_Get key_eq m k with
  | None => false
  | Some v1 => true
  end.

Theorem Map_Contains_Implies_Get :
  forall {K V : Type} (key_eq : K -> K -> bool) (m : Map K V) (k : K),
  Map_Contains key_eq m k = true ->
  exists (v : V), Map_Get key_eq m k = Some v.
Proof.
  intros.
  unfold Map_Contains in H.
  destruct (Map_Get key_eq m k).
    exists v. reflexivity.
    inversion H.
Qed.

Fixpoint Map_IsSubMap {K V : Type} (key_eq : K -> K -> bool) (val_eq : V -> V -> bool) (mSub mSuper : Map K V) : bool :=
  match mSub with
  | [] => true
  | (k, v) :: mSub' => (Map_Contains key_eq mSuper k) && Map_IsSubMap key_eq val_eq mSub' mSuper
  end.

(* Tests of Map definition through instantiating a Map withnat keys and values
and beq_nat comparison function. *)
Module Map_Tests.
Definition NatMap := Map nat nat.
Definition Empty_NatMap := Empty_Map nat nat.
Definition NatMap_Add (m : NatMap) (k v : nat) : NatMap := Map_Add beq_nat m k v.
Definition NatMap_Get (m : NatMap) (k : nat) : option nat := Map_Get beq_nat m k.
Definition NatMap_Contains (m : NatMap) (k : nat) : bool := Map_Contains beq_nat m k.
Definition NatMap_IsSubMap (m1 m2 : NatMap) : bool := Map_IsSubMap beq_nat beq_nat m1 m2.

(* add to empty map creates 1 element *)
Example addTest1: NatMap_Add Empty_NatMap 5 10 = [(5, 10)].
Proof. reflexivity. Qed.

(* replacement is permitted *)
Example addTest2: NatMap_Add [(5, 10)] 5 20 = [(5, 20)].
Proof. reflexivity. Qed.

(* adding distint keys adds new elements *)
Example addTest3: NatMap_Add [(5, 10)] 10 20 = [(5, 10); (10, 20)].
Proof. reflexivity. Qed.

(* get true *)
Example getTest1: NatMap_Get [(5, 10)] 5 = Some 10.
Proof. reflexivity. Qed.

(* get false *)
Example getTest2: NatMap_Get [(5, 10)] 3 = None.
Proof. reflexivity. Qed.

(* get false *)
Example getTest3: NatMap_Get [(5, 10); (10, 20)] 10 = Some 20.
Proof. reflexivity. Qed.

(* get false *)
Example getTest4: NatMap_Get Empty_NatMap 3 = None.
Proof. reflexivity. Qed.

(* contains true *)
Example containsTest1: NatMap_Contains [(5, 10)] 5 = true.
Proof. reflexivity. Qed.

(* contains false *)
Example containsTest2: NatMap_Contains [(5, 10)] 5 = true.
Proof. reflexivity. Qed.

(* contains false *)
Example containsTest3: NatMap_Contains [(5, 10)] 8 = false.
Proof. reflexivity. Qed.

(* contains empty *)
Example containsTest4: NatMap_Contains Empty_NatMap 2 = false.
Proof. reflexivity. Qed.

(* contains bigmap *)
Example containsTest5: NatMap_Contains [(5, 10); (10, 20)] 10 = true.
Proof. reflexivity. Qed.

(* submap empty *)
Example submapTest1: NatMap_IsSubMap Empty_NatMap Empty_NatMap = true.
Proof. reflexivity. Qed.

(* submap empty *)
Example submapTest2: NatMap_IsSubMap Empty_NatMap [(5, 10); (10, 20)] = true.
Proof. reflexivity. Qed.

(* submap first true *)
Example submapTest3: NatMap_IsSubMap [(5, 10)] [(5, 10); (10, 20)] = true.
Proof. reflexivity. Qed.

(* submap latter true *)
Example submapTest4: NatMap_IsSubMap [(10, 20)] [(5, 10); (10, 20)] = true.
Proof. reflexivity. Qed.

(* submap latter false *)
Example submapTest5: NatMap_IsSubMap [(100, 30)] [(5, 10); (10, 20)] = false.
Proof. reflexivity. Qed.
End Map_Tests.
