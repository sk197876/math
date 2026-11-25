(** Federer (1969), 3.1.11, pp. 219–220:
    each higher differential is a continuous symmetric
    form in the existing Chapter 1 interface,
    with the same norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherDifferentialSymmetry
  SymmetricForms SymmetricOperatorNorm MultilinearTupleForm
  ContinuousMultilinearSymmetricNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_symmetric_form_exists]:
    the symmetric k-form asserted in Federer
    3.1.11, p. 220, agrees with
    the Chapter 1 symmetric-form interface on
    every tuple, and its operator norm is
    the corrected finite norm of p. 219. *)
Theorem norm_higher_differential_symmetric_form_exists (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (A : X->Prop) (f : X->Y) a (z : Z k) :
  has_norm_higher_differential NX ez ZN A f k a z ->
  exists phi : S_m X Y k,
    (forall t, phi t=@ez k [ffun i=>tnth t i] z) /\
    symmetric_operator_norm hNX.1 NY phi=(@ZN k z)%:E.
Proof.
move=> hz.
have hsym := @norm_higher_differential_symmetric R X Y NX NY hNX hNY
  Z ez ZN hZ A f k a z hz.
have [phi he] := symmetric_multilinear_tuple_form_exists
  (continuous_multilinear_evaluation (@hZ k) z) hsym.
exists phi; split; first exact he.
exact (@continuous_multilinear_symmetric_norm R k X Y (Z k) NX NY
  hNX hNY (@ez k) (@ZN k) (@hZ k) z phi he).
Qed.
