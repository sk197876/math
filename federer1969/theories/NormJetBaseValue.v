(** Federer (1969), 3.1.11, p. 221: every jet has the same
    value as its function at the base point. This consequence uses
    only the abstract jet laws and the zeroth-differential graph. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP PolynomialFunctions ContinuousMultilinearUP
  NormHigherDifferentialUP NormJetUP NormJet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_jet_base_value]: F_a(a)=f(a), the constant
    term of the displayed jet polynomial in Federer 3.1.11, p. 221.
    The assertion includes a jet of order zero. *)
Lemma norm_jet_base_value (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (P : PolynomialFunction X Y) :
  is_norm_jet_polynomial NX ev ZN A f k a P -> P a=f a.
Proof.
move=>hP; have [D [hD he]] := norm_jet_polynomial_expansion hP.
have hz := hD 0%N (leq0n k).
have hp := @norm_jet_differential_at_base R X Y NX NY hNX hNY
  Z ev ZN hZ A f k a P hP 0%N (D 0%N) (leq0n k) hz.
exact (eq_trans (esym hp.2) hz.2).
Qed.
