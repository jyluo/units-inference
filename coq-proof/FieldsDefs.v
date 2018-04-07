Require Import TacticalLemmas.
Require Import UnitsDefs.
Require Import SubtypingDefs.
Require Import IDDefs.
Require Import ValueDefs.
Require Import GammaDefs.
Require Import HeapDefs.
Require Import GammaHeapCorrespondence.

(* ======================================================= *)
Inductive Field_Declaration : Type :=
  | FD_Empty : Field_Declaration
  | FD_Decl : Unit -> ID -> nat -> Field_Declaration -> Field_Declaration.
Tactic Notation "fd_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "FD_Empty"
  | Case_aux c "FD_Decl"
  ].
Hint Constructors Field_Declaration.

(* ======================================================= *)
Reserved Notation "'fd:' g1 '|-' fds 'in' g2" (at level 40).
Inductive fd_has_type : Gamma -> Field_Declaration -> Gamma -> Prop :=
  | T_FD_Empty : forall (g : Gamma),
    fd: g |- FD_Empty in g
  | T_FD : forall (g1 g2 : Gamma) (tail : Field_Declaration) (T : Unit) (f : ID) (z : nat),
    fd: Gamma_Extend g1 f T |- tail in g2 ->
    fd: g1 |- FD_Decl T f z tail in g2
where "'fd:' g1 '|-' fds 'in' g2" := (fd_has_type g1 fds g2).
Tactic Notation "fd_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_FD_Empty"
  | Case_aux c "T_FD"
  ].
Hint Constructors fd_has_type.

(* ======================================================= *)
Reserved Notation " fd1 'fd==>' fd2 " (at level 8).
Inductive fd_small_step : prod Heap Field_Declaration -> prod Heap Field_Declaration -> Prop :=
  | ST_FD : forall (h : Heap) (T : Unit) (f : ID) (z : nat) (fds : Field_Declaration),
    ( h, FD_Decl T f z fds ) fd==> ( (Heap_Update h f T T z), fds )
where " fd1 'fd==>' fd2 " := (fd_small_step fd1 fd2).
Tactic Notation "fd_small_step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_FD"
  ].
Hint Constructors fd_small_step.

(* ======================================================= *)
(* step is deterministic *)
Theorem fd_small_step_deterministic:
  forall fd fd1 fd2,
    fd fd==> fd1 ->
    fd fd==> fd2 ->
    fd1 = fd2.
Proof.
  intros fd fd1 fd2 Hfd1.
  generalize dependent fd2.
  fd_small_step_cases (induction Hfd1) Case.
  Case "ST_FD".
    intros fd2 Hfd2.
    inversion Hfd2; subst. reflexivity.
Qed.

(* ======================================================= *)
Inductive FD_Normal_Form : Field_Declaration -> Prop :=
  | V_FD_Empty : FD_Normal_Form FD_Empty.

(* ======================================================= *)
Theorem fd_progress : forall (fd : Field_Declaration) (g1 g2 : Gamma) (h : Heap),
  fd: g1 |- fd in g2 ->
  FD_Normal_Form fd \/ exists h' fd', (h, fd) fd==> (h', fd').
Proof.
  (* by induction on typing of fd *)
  intros fd g1 g2 h HT.
  fd_has_type_cases (induction HT) Case; subst.
  Case "T_FD_Empty".
    left. apply V_FD_Empty.
  Case "T_FD".
    right.
    destruct IHHT.
      inversion H. exists (Heap_Update h f T T z). exists FD_Empty. apply ST_FD.
      exists (Heap_Update h f T T z). exists tail. apply ST_FD.
Qed.

(* ======================================================= *)

(* Returns the first field definition in the list of field definitions fd, or None if the list is empty *)
Definition First_FD (fd : Field_Declaration) : option (prod (prod Unit ID) nat) :=
  match fd with
  | FD_Decl T f z fd => Some (T, f, z)
  | FD_Empty => None
  end.

(* ======================================================= *)

Theorem fd_preservation : forall (g1 g2 : Gamma) (h h' : Heap) (fd fd' : Field_Declaration) (T : Unit) (f : ID) (z : nat),
  fd: g1 |- fd in g2 ->
  gh: g2 |- h OK ->
  (h, fd) fd==> (h', fd') ->
  First_FD fd = Some (T, f, z) ->
  gh: g2 |- h' OK /\ fd: Gamma_Extend g1 f T |- fd' in g2.
Proof.
  intros g1 g2 h h' fd fd' T f z HT HGH HS Hfst.
  generalize dependent fd'. generalize dependent h'.
  fd_has_type_cases (induction HT) Case; intros h' fd' HS; subst.
  Case "T_FD_Empty".
    inversion HS.
  Case "T_FD".
    inversion HS; subst.
    inversion Hfst; subst.
    split.
    (* first prove that g2 |- h' OK *)
      apply GH_Correspond.
      intros f' Tf'.
      inversion HGH; subst.
      destruct H with f T. destruct H1. destruct H2 as [Tv']. destruct H2 as [z']. destruct H2. destruct H3.
      destruct H with f' Tf'. destruct H6. destruct H7 as [Tv'']. destruct H7 as [z'']. destruct H7. destruct H8.
      split. apply H5.
      split. apply H6.
      destruct (id_eq_dec f' f).
      (* Case: f = f' : in h', the value of f' is T z *)
        exists T. exists z.
        split. subst. apply Heap_Update_FieldType_Eq.
        split. subst. apply Heap_Update_FieldValue_Eq.
        subst. apply subtype_reflexive.
      (* Case: f <> f' : in h' the value of f' is some Tv' z' *)
        exists Tv''. exists z''.
        split. subst. apply Heap_Update_FieldType_Neq. apply n.
        split. rewrite <- H8. apply Heap_Update_FieldValue_Neq. apply n.
        apply H9.
    (* then prove that fd: Gamma_Extend g1 f T |- fd' in g2 *)
      apply HT.
Qed.
