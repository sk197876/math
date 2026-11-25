(** Opaque exact higher-differential graph for Federer (1969),
    3.1.11, pp. 218–219. The public laws retain the
    recursive domain and approximation, while hiding the witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP PartialFunctionUP
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type NormHigherDifferentialSignature.
(** Source for [value]: the exact partial higher differential
    D^k f in Federer 3.1.11, pp. 218–219. *)
Parameter value : forall (R : realType) (X Y : lmodType R)
  (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
  (Z : nat->lmodType R)
  (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
  (ZN : forall k, Z k->R)
  (hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k))
  (A : X->Prop) (f : X->Y) (k : nat), partial_function X (Z k).
(** Source for [laws]: the recursive approximation and exact
    domain characterise the graph D^k f, Federer 3.1.11,
    pp. 218–219. *)
Parameter laws : forall (R : realType) (X Y : lmodType R)
  (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
  (Z : nat->lmodType R)
  (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
  (ZN : forall k, Z k->R)
  (hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k))
  (A : X->Prop) (f : X->Y) (k : nat),
  is_norm_higher_differential_graph NX evaluation ZN A f
    (@value R X Y NX NY hNX hNY Z evaluation ZN hZ A f k).
End NormHigherDifferentialSignature.

Module NormHigherDifferential : NormHigherDifferentialSignature.
(** Source for [value]: a proved witness for the exact
    graph of Federer 3.1.11, pp. 218–219, selected
    privately and hidden by module ascription. *)
Definition value (R : realType) (X Y : lmodType R)
  (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
  (Z : nat->lmodType R)
  (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
  (ZN : forall k, Z k->R)
  (hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k))
  (A : X->Prop) (f : X->Y) (k : nat) : partial_function X (Z k) :=
  projT1 (cid (@norm_higher_differential_graph_exists R X Y NX NY
    hNX hNY Z evaluation ZN hZ A f k)).
(** Source for [laws]: the private witness fulfils all
    recursive graph laws, Federer 3.1.11, pp. 218–219. *)
Lemma laws (R : realType) (X Y : lmodType R)
  (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
  (Z : nat->lmodType R)
  (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
  (ZN : forall k, Z k->R)
  (hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k))
  (A : X->Prop) (f : X->Y) (k : nat) :
  is_norm_higher_differential_graph NX evaluation ZN A f
    (@value R X Y NX NY hNX hNY Z evaluation ZN hZ A f k).
Proof.
exact: projT2 (cid (@norm_higher_differential_graph_exists R X Y NX NY
  hNX hNY Z evaluation ZN hZ A f k)).
Qed.
End NormHigherDifferential.
