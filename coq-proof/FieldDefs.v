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
Theorem fds_progress : forall (g1 g2 : Gamma) (h : Heap) (fds : Field_Declarations),
  fds: g1 |- fds in g2 ->
  FD_Normal_Form fds \/ exists h' fds', (h, fds) fds==> (h', fds').
Proof.
  (* by induction on typing of fds *)
  intros g1 g2 h fds HT.
  fds_has_type_cases (induction HT) Case; subst.
  Case "T_FD_Empty".
    left. apply V_FD_Empty.
  Case "T_FD".
  (* fds is T = f z ; tail *)
    right.
    exists (Heap_Update h f T T z), tail. apply ST_FD.
Qed.

(* ======================================================= *)

(* Extends g with the first field declaration in fds, or returns g unchanged if fds is empty *)
Definition Gamma_Extend_Fields (g : Gamma) (fds : Field_Declarations) : Gamma :=
  match fds with
  | FD_Decl T f z fds => Gamma_Extend g f T
  | FD_Empty => g
  end.

(* ======================================================= *)

Theorem fds_heap_correspond_to_original_gamma : forall (g1 g2 : Gamma) (h h' : Heap) (fds fds' : Field_Declarations),
  fds: g1 |- fds in g2 ->
  gh: g1 |- h OK ->
  (h, fds) fds==> (h', fds') ->
  gh: g1 |- h' OK.
Proof.
  intros g1 g2 h h' fds fds' HT HGH HS.
  generalize dependent fds'. generalize dependent h'.
  fds_has_type_cases (induction HT) Case; intros h' fds' HS; subst.
  Case "T_FD_Empty".
    inversion HS.
  Case "T_FD".
    inversion HS; subst.
    apply GH_Correspondence.
    intros f' HGf'.
    destruct (id_eq_dec f' f).
    (* Case: f = f' *)
      subst. rewrite -> H in HGf'. inversion HGf'.
    (* Case: f <> f' *)
      inversion HGH; subst.
      destruct H2 with f' as [Tf']. apply HGf'. clear H2. destruct H3 as [Tv']. destruct H2 as [z']. Tactics.destruct_pairs.
      exists Tf', Tv', z'.
      split. apply H2.
      split. rewrite <- H3. apply Heap_Update_FieldType_Neq. apply n.
      split. apply H4.
      rewrite <- H5. apply Heap_Update_FieldValue_Neq. apply n.
Qed.

Theorem fds_gamma_contains_all_original_fields : forall (g1 g2 : Gamma) (f : ID) (fds : Field_Declarations),
  Gamma_Contains g1 f = true ->
  fds: g1 |- fds in g2 ->
  Gamma_Contains g2 f = true.
Proof.
  intros g1 g2 f fds HGF HT.
  fds_has_type_cases (induction HT) Case; subst.
  Case "T_FD_Empty".
    apply HGF.
  Case "T_FD".
    destruct (id_eq_dec f0 f).
    (* Case: f = f0 *)
      subst. apply H0.
    (* Case: f <> f0 *)
      apply IHHT. apply Gamma_Extend_Contains. apply HGF.
Qed.


Theorem fds_gamma_contains_all_original_fields' : forall (g g1 g2 : Gamma) (f f' : ID) (fds : Field_Declarations) (T' : Unit) (z' : nat),
  fds: g |- fds in g1 ->
  fds: g1 |- FD_Decl T' f' z' fds in g2 ->
  Gamma_Contains g2 f = true ->
  f' <> f ->
  Gamma_Contains g1 f = true.
Proof.
  intros.
  generalize d

  generalize dependent f.
  induction H.
    intros f HGF HFF'; subst.
      auto.
    intros f2 HGF2 HF2F'; subst.
      eapply IHfds_has_type in HGF2; auto.
      destruct (id_eq_dec f f2); subst.
        rewrite -> Gamma_Contains_Extend_Same in HGF2.
      rewrite <- HGF2. symmetry. eapply Gamma_Contains_Extend_Same. apply Gamma_Contains_Extend_Not_Same.
Qed.

Theorem fds_preservation : forall (g1 g2 : Gamma) (h h' : Heap) (fds fds' : Field_Declarations),
  fds: g1 |- fds in g2 ->
  gh: g1 |- h OK ->
  (h, fds) fds==> (h', fds') ->
  gh: g2 |- h' OK /\ fds: Gamma_Extend_Fields g1 fds |- fds' in g2.
Proof.
  intros g1 g2 h h' fds fds' HT HGH HS.
  generalize dependent fds'. generalize dependent h'. generalize dependent h.
  fds_has_type_cases (induction HT) Case; intros h HGH h' fds' HS; subst.
  Case "T_FD_Empty".
    inversion HS.
  Case "T_FD".
    assert (gh: g1 |- h' OK). eapply fds_heap_correspond_to_original_gamma. apply T_FD; eauto. apply HGH. apply HS.
    rename H2 into HGH'.
    inversion HS; subst.
    split.
    apply GH_Correspondence.
    intros f' HGf'.
    destruct (id_eq_dec f' f).
    (* Case: f = f' *)
      subst. exists T, T, z.
      split. auto.
      split. apply Heap_Update_FieldType_Eq.
      split. apply subtype_reflexive.
      apply Heap_Update_FieldValue_Eq.
    (* Case: f <> f' *)
      inversion HGH'; subst.
      destruct H2 with f' as [Tf'].
      



apply 

Case "T_FD_Empty".
    inversion HS.
  Case "T_FD".
    inversion HS; subst.
    apply GH_Correspondence.
    intros f' HGf'.
    destruct (id_eq_dec f' f).
    (* Case: f = f' *)
      subst. rewrite -> H in HGf'. inversion HGf'.
    (* Case: f <> f' *)
      inversion HGH; subst.
      destruct H2 with f' as [Tf']. apply HGf'. clear H2. destruct H3 as [Tv']. destruct H2 as [z']. Tactics.destruct_pairs.
      exists Tf', Tv', z'.
      split. apply H2.
      split. rewrite <- H3. apply Heap_Update_FieldType_Neq. apply n.
      split. apply H4.
      rewrite <- H5. apply Heap_Update_FieldValue_Neq. apply n.


    eapply IHHT.

    split.
    (* first prove that g2 |- h' OK *)
      eapply IHHT.
        apply GH_Correspondence.
        intros f' HGf'.
        inversion HGH'; subst. destruct H2 with f' as [Tf'].
          destruct (id_eq_dec f' f); subst. rewrite -> Gamma_Contains_Extend_Same in HGf'. simpl in HGf'.

        (* Case: f = f' : in h', the value of f' is T T z *)
          subst.
          exists T, T, z.
          split. apply Gamma_Get_Extend_Same.


      apply GH_Correspondence.
      intros f' HGf'.
      destruct (id_eq_dec f' f).
      (* Case: f = f' : in h', the value of f' is T T z *)
        subst.
        exists T, T, z.
        split. apply Gamma_Get_Extend_Same.
        split. apply Heap_Update_FieldType_Eq.
        split. apply subtype_reflexive.
        apply Heap_Update_FieldValue_Eq.
      (* Case: f <> f' : in h' the value of f' is some Tv' z' *)
        inversion HGH'; subst. destruct H2 with f' as [Tf].
        eapply fds_gamma_contains_all_original_fields. apply HGf'.

        eapply Gamma_Contains_Implies_Get in HGf'. destruct HGf' as [Tf'].
        exists Tf', Tf', z.
        split. apply H2.

      inversion HGH; subst.
      destruct H2 with f' as [Tf'].


  apply HT.

Qed.


Theorem fds_preservation' : forall (g1 g2 : Gamma) (h h' : Heap) (fds fds' : Field_Declarations),
  fds: g1 |- fds in g2 ->
  gh: g2 |- h OK ->
  (h, fds) fds==> (h', fds') ->
  gh: g2 |- h' OK /\ fds: Gamma_Extend_Fields g1 fds |- fds' in g2.
Proof.
  intros g1 g2 h h' fds fds' HT HGH HS.
  generalize dependent fds'. generalize dependent h'. generalize dependent h.
  fds_has_type_cases (induction HT) Case; intros h HGH h' fds' HS; subst.
  Case "T_FD_Empty".
    inversion HS.
  Case "T_FD".
    inversion HS; subst.
    split.
    (* first prove that g2 |- h' OK *)
      apply GH_Correspondence.
      intros f' HGf'.
      inversion HGH; subst.
      destruct H2 with f' as [Tf']. apply HGf'. clear H2. destruct H3 as [Tv']. destruct H2 as [z']. Tactics.destruct_pairs.
      destruct (id_eq_dec f' f).
      (* Case: f = f' : in h', the value of f' is T T z *)
        exists T, T, z.
        rewrite -> e in H2. assert (T = Tf'). eapply Gamma_Get_Content_Eq. apply H1. apply H2. subst.
        split. apply H1.
        split. apply Heap_Update_FieldType_Eq.
        split. apply subtype_reflexive.
        apply Heap_Update_FieldValue_Eq.
      (* Case: f <> f' : in h' the value of f' is some Tv' z' *)
        exists Tf', Tv', z'.
        split. apply H2.
        split. rewrite <- H3. apply Heap_Update_FieldType_Neq. apply n.
        split. apply H4.
        rewrite <- H5. apply Heap_Update_FieldValue_Neq. apply n.
    (* then prove that fds: Gamma_Extend g1 f T |- fds' in g2 *)
      simpl. apply HT.
Qed.
