Require Import TacticalLemmas.
Require Import UnitsDefs.
Require Import SubtypingDefs.
Require Import IDDefs.
Require Import ValueDefs.
Require Import GammaDefs.
Require Import HeapDefs.
Require Import GammaHeapCorrespondence.

(* ======================================================= *)
Inductive Field_Declarations : Type :=
  | FD_Empty : Field_Declarations
  | FD_Decl : Unit -> ID -> nat -> Field_Declarations -> Field_Declarations.
Tactic Notation "fds_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "FD_Empty"
  | Case_aux c "FD_Decl"
  ].
Hint Constructors Field_Declarations.

(* ======================================================= *)
Reserved Notation "'fds:' g1 '|-' fds 'in' g2" (at level 40).
Inductive fds_has_type : Gamma -> Field_Declarations -> Gamma -> Prop :=
  | T_FD_Empty : forall (g : Gamma),
    fds: g |- FD_Empty in g
  | T_FD : forall (g1 g2 : Gamma) (tail : Field_Declarations) (T : Unit) (f : ID) (z : nat),
    Gamma_Contains g1 f = false ->
    Gamma_Contains g2 f = true ->
    Gamma_Get g2 f = Some T ->
    fds: Gamma_Extend g1 f T |- tail in g2 ->
    fds: g1 |- FD_Decl T f z tail in g2
where "'fds:' g1 '|-' fds 'in' g2" := (fds_has_type g1 fds g2).
Tactic Notation "fds_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_FD_Empty"
  | Case_aux c "T_FD"
  ].
Hint Constructors fds_has_type.

(* ======================================================= *)
Reserved Notation " fds1 'fds==>' fds2 " (at level 8).
Inductive fds_small_step : prod Heap Field_Declarations -> prod Heap Field_Declarations -> Prop :=
  | ST_FD : forall (h : Heap) (T : Unit) (f : ID) (z : nat) (fds : Field_Declarations),
    ( h, FD_Decl T f z fds ) fds==> ( (Heap_Update h f T T z), fds )
where " fds1 'fds==>' fds2 " := (fds_small_step fds1 fds2).
Tactic Notation "fds_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_FD"
  ].
Hint Constructors fds_small_step.

(* ======================================================= *)
(* step is deterministic *)
Theorem fds_small_step_deterministic:
  forall fds fds1 fds2,
    fds fds==> fds1 ->
    fds fds==> fds2 ->
    fds1 = fds2.
Proof.
  intros fds fds1 fds2 Hfds1.
  generalize dependent fds2.
  fds_small_step_cases (induction Hfds1) Case.
  Case "ST_FD".
    intros fds2 Hfds2.
    inversion Hfds2; subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive FD_Normal_Form : Field_Declarations -> Prop :=
  | V_FD_Empty : FD_Normal_Form FD_Empty.

(* ======================================================= *)
Theorem fds_progress : forall (fds : Field_Declarations) (g1 g2 : Gamma) (h : Heap),
  fds: g1 |- fds in g2 ->
  FD_Normal_Form fds \/ exists h' fds', (h, fds) fds==> (h', fds').
Proof.
  (* by induction on typing of fds *)
  intros fds g1 g2 h HT.
  fds_has_type_cases (induction HT) Case; subst.
  Case "T_FD_Empty".
    left. apply V_FD_Empty.
  Case "T_FD".
    right.
    destruct IHHT.
      inversion H2. exists (Heap_Update h f T T z). exists FD_Empty. apply ST_FD.
      exists (Heap_Update h f T T z). exists tail. apply ST_FD.
Qed.

(* ======================================================= *)

(* Returns the first field definition in the list of field definitions fds, or None if the list is empty *)
Definition First_FD (fds : Field_Declarations) : option (prod (prod Unit ID) nat) :=
  match fds with
  | FD_Decl T f z fds => Some (T, f, z)
  | FD_Empty => None
  end.

(* ======================================================= *)

Theorem fds_preservation : forall (g1 g2 : Gamma) (h h' : Heap) (fds fds' : Field_Declarations) (T : Unit) (f : ID) (z : nat),
  fds: g1 |- fds in g2 ->
  gh: g2 |- h OK ->
  (h, fds) fds==> (h', fds') ->
  First_FD fds = Some (T, f, z) ->
  gh: g2 |- h' OK /\ fds: Gamma_Extend g1 f T |- fds' in g2.
Proof.
  intros g1 g2 h h' fds fds' T f z HT HGH HS Hfst.
  generalize dependent fds'. generalize dependent h'.
  fds_has_type_cases (induction HT) Case; intros h' fds' HS; subst.
  Case "T_FD_Empty".
    inversion HS.
  Case "T_FD".
    inversion HS; subst.
    inversion Hfst; subst.
    split.
    (* first prove that g2 |- h' OK *)
      apply GH_Correspondence.
      intros f'.
      inversion HGH; subst.
      destruct H2 with f'. destruct H4 as [Tf']. destruct H4 as [Tv']. destruct H4 as [z'].
        destruct H4. destruct H5. destruct H6.
      split. apply H3.
      destruct (id_eq_dec f' f).
      (* Case: f = f' : in h', the value of f' is T T z *)
        exists T, T, z.
        rewrite -> e in H4. assert (T = Tf'). eapply Gamma_Get_Content_Eq. apply H1. apply H4. subst.
        split. apply H1.
        split. apply Heap_Update_FieldType_Eq.
        split. apply subtype_reflexive.
        apply Heap_Update_FieldValue_Eq.
      (* Case: f <> f' : in h' the value of f' is some Tv' z' *)
        exists Tf', Tv', z'.
        split. apply H4.
        split. rewrite <- H5. apply Heap_Update_FieldType_Neq. apply n.
        split. apply H6. rewrite <- H7. apply Heap_Update_FieldValue_Neq. apply n.
    (* then prove that fds: Gamma_Extend g1 f T |- fds' in g2 *)
      apply HT.
Qed.
