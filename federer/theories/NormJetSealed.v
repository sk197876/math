(** Opaque kth jet for Federer (1969), 3.1.11,
    p. 221. The public interface exposes
    only the polynomial, its defining laws,
    and continuity of its coefficient forms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP SymmetricFormSum PolynomialFunctions
  ContinuousMultilinearUP ContinuousSymmetricFormAdapter
  NormHigherDifferentialUP NormJetUP NormJetConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type NormJetSignature.
(** Source for [value]: the polynomial F_a
    specified as the kth jet in Federer
    3.1.11, p. 221. *)
Parameter value : forall (R : realType) (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (z : Z k)
    (hz : has_norm_higher_differential NX ev ZN A f k a z), PolynomialFunction X Y.
(** Source for [laws]: the jet's degree
    and exact differential-coefficient expansion,
    Federer 3.1.11, p. 221, are proved. *)
Parameter laws : forall (R : realType) (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (z : Z k)
    (hz : has_norm_higher_differential NX ev ZN A f k a z),
  is_norm_jet_polynomial NX ev ZN A f k a (@value R X Y NX NY hNX hNY Z ev ZN hZ A f k a z hz).
(** Source for [coefficient_bound]: the coefficient
    forms of the jet are continuous,
    supporting its calculus in Federer 3.1.11, p. 221. *)
Parameter coefficient_bound : forall (R : realType) (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (z : Z k)
    (hz : has_norm_higher_differential NX ev ZN A f k a z) i,
  norm_bounded_symmetric_form NX NY
    (sform_component i (polynomial_to_forms (@value R X Y NX NY hNX hNY Z ev ZN hZ A f k a z hz))).
End NormJetSignature.

Module NormJet : NormJetSignature.
(** Source for [value]: the privately proved
    existence witness for F_a, Federer 3.1.11,
    p. 221; its construction remains opaque. *)
Definition value (R : realType) (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (z : Z k)
    (hz : has_norm_higher_differential NX ev ZN A f k a z) : PolynomialFunction X Y :=
  projT1 (cid (@norm_jet_polynomial_exists R X Y NX NY hNX hNY Z ev ZN hZ A f k a z hz)).
(** Source for [laws]: proof of the
    public jet specification, Federer 3.1.11, p. 221. *)
Lemma laws (R : realType) (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (z : Z k)
    (hz : has_norm_higher_differential NX ev ZN A f k a z) :
  is_norm_jet_polynomial NX ev ZN A f k a (@value R X Y NX NY hNX hNY Z ev ZN hZ A f k a z hz).
Proof. exact: (projT2 (cid (@norm_jet_polynomial_exists R X Y NX NY hNX hNY Z ev ZN hZ A f k a z hz))).1. Qed.
(** Source for [coefficient_bound]: proved continuity
    of the coefficient forms, Federer 3.1.11, p. 221. *)
Lemma coefficient_bound (R : realType) (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (z : Z k)
    (hz : has_norm_higher_differential NX ev ZN A f k a z) i :
  norm_bounded_symmetric_form NX NY
    (sform_component i (polynomial_to_forms (@value R X Y NX NY hNX hNY Z ev ZN hZ A f k a z hz))).
Proof. exact: (projT2 (cid (@norm_jet_polynomial_exists R X Y NX NY hNX hNY Z ev ZN hZ A f k a z hz))).2 i. Qed.
End NormJet.
