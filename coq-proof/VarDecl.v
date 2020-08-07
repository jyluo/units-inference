Require Import Strings.String.
Open Scope string_scope.
Open Scope core_scope.

From PUnits Require Import TacticalLemmas.
From PUnits Require Import UnitsDefs.
From PUnits Require Import SubtypingDefs.
From PUnits Require Import IDDefs.
From PUnits Require Import LabeledLiterals.
From PUnits Require Import GammaDefs.
From PUnits Require Import StackFrame.
From PUnits Require Import GammaStackFrameCorrespondence.

(* ======================================================= *)
Inductive Variable_Declarations : Type :=
  | VD_Empty : Variable_Declarations
  | VD_Decl : Unit -> ID -> nat -> Variable_Declarations -> Variable_Declarations.
Tactic Notation "vds_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "VD_Empty"
  | Case_aux c "VD_Decl"
  ].
Hint Constructors Variable_Declarations : pUnitsHintDatabase.

(* ======================================================= *)
Reserved Notation "'vds:' g1 '|-' vds 'in' g2" (at level 40).
Inductive vds_has_type : Gamma -> Variable_Declarations -> Gamma -> Prop :=
  | T_VD_Empty : forall (g : Gamma),
    vds: g |- VD_Empty in g
  | T_VD : forall (g1 g2 : Gamma) (tail : Variable_Declarations) (T : Unit) (v : ID) (z : nat),
    Gamma_Contains g1 v = false ->
    Gamma_Contains g2 v = true ->
    Gamma_Get g2 v = Some T ->
    vds: Gamma_Extend g1 v T |- tail in g2 ->
    vds: g1 |- VD_Decl T v z tail in g2
where "'vds:' g1 '|-' vds 'in' g2" := (vds_has_type g1 vds g2).
Tactic Notation "vds_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_VD_Empty"
  | Case_aux c "T_VD"
  ].
Hint Constructors vds_has_type : pUnitsHintDatabase.

(* ======================================================= *)
Reserved Notation " vds1 'vds==>' vds2 " (at level 8).
Inductive vds_small_step : prod StackFrame Variable_Declarations -> prod StackFrame Variable_Declarations -> Prop :=
  | ST_VD : forall (f : StackFrame) (T : Unit) (v : ID) (z : nat) (vds : Variable_Declarations),
    ( f, VD_Decl T v z vds ) vds==> ( (StackFrame_Update f v T T z), vds )
where " vds1 'vds==>' vds2 " := (vds_small_step vds1 vds2).
Tactic Notation "vds_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_VD"
  ].
Hint Constructors vds_small_step : pUnitsHintDatabase.

(* ======================================================= *)
(* step is deterministic *)
Theorem vds_small_step_deterministic:
  forall vds vds1 vds2,
    vds vds==> vds1 ->
    vds vds==> vds2 ->
    vds1 = vds2.
Proof.
  intros vds vds1 vds2 Hvds1.
  generalize dependent vds2.
  vds_small_step_cases (induction Hvds1) Case.
  Case "ST_VD".
    intros vds2 Hvds2.
    inversion Hvds2; subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive VD_Normal_Form : Variable_Declarations -> Prop :=
  | V_VD_Empty : VD_Normal_Form VD_Empty.

(* ======================================================= *)
Theorem vds_progress : forall (g1 g2 : Gamma) (f : StackFrame) (vds : Variable_Declarations),
  vds: g1 |- vds in g2 ->
  VD_Normal_Form vds \/ exists f' vds', (f, vds) vds==> (f', vds').
Proof.
  (* by induction on typing of vds *)
  intros g1 g2 f vds HT.
  vds_has_type_cases (induction HT) Case; subst.
  Case "T_VD_Empty".
    left. apply V_VD_Empty.
  Case "T_VD".
    right.
    destruct IHHT.
      inversion H2. exists (StackFrame_Update f v T T z). exists VD_Empty. apply ST_VD.
      exists (StackFrame_Update f v T T z). exists tail. apply ST_VD.
Qed.

(* ======================================================= *)

(* Extends g with the first field declaration in vds, or returns g unchanged if vds is empty *)
Definition Gamma_Extend_Variables (g : Gamma) (vds : Variable_Declarations) : Gamma :=
  match vds with
  | VD_Decl T v z vds => Gamma_Extend g v T
  | VD_Empty => g
  end.

(* ======================================================= *)

Theorem vds_preservation : forall (g1 g2 : Gamma) (f f' : StackFrame) (vds vds' : Variable_Declarations),
  vds: g1 |- vds in g2 ->
  gf: g2 |- f OK ->
  (f, vds) vds==> (f', vds') ->
  gf: g2 |- f' OK /\ vds: Gamma_Extend_Variables g1 vds |- vds' in g2.
Proof.
  intros g1 g2 f f' vds vds' HT HGF HS.
  generalize dependent vds'. generalize dependent f'.
  vds_has_type_cases (induction HT) Case; intros f' vds' HS; subst.
  Case "T_VD_Empty".
    inversion HS.
  Case "T_VD".
    inversion HS; subst.
    split.
    (* first prove that g2 |- f' OK *)
      apply GF_Correspondence.
      intros v' HGv'.
      inversion HGF; subst.
      destruct H2 with v' as [Tv']. apply HGv'. clear H2. destruct H3 as [Tl']. destruct H2 as [z']. Tactics.destruct_pairs.
      destruct (id_eq_dec v' v); subst.
      (* Case: v = v' : in f', the value of v' is T T z *)
        exists T, T, z.
        assert (T = Tv'). eapply Gamma_Get_Content_Eq. apply H1. apply H2. subst.
        split. apply H1.
        split. apply StackFrame_Update_VarType_Eq.
        split. apply subtype_reflexive.
        apply StackFrame_Update_VarValue_Eq.
      (* Case: v <> v' : in f' the value of v' is some Tl' z' *)
        exists Tv', Tl', z'.
        split. apply H2.
        split. rewrite <- H3. apply StackFrame_Update_VarType_Neq. apply n.
        split. apply H4.
        rewrite <- H5. apply StackFrame_Update_VarValue_Neq. apply n.
    (* then prove that vds: Gamma_Extend g1 v T |- vds' in g2 *)
      simpl. apply HT.
Qed.
