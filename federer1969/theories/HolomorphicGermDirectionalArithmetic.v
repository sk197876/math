(** Federer (1969), 3.4.12, p. 339, extending the
    Taylor argument of 3.4.8(5), p. 328: actual original
    complex directional coefficients preserve zero, addition and
    finite sums. Reuse actual germ-jet arithmetic and scalar restriction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermJetsSealed HolomorphicGermJetArithmetic
  HolomorphicGermJetZeroNegate HolomorphicGermDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Arithmetic.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Variable a:X.
Variable k:nat.
Variable v:X.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)].
Local Notation c:=(@holomorphic_germ_directional_coefficient R X NX hNX a k).

(** Source for [holomorphic_germ_directional_zero]: every actual
    divided coefficient of zero is zero, extending 3.4.5, p. 319. *)
Lemma holomorphic_germ_directional_zero:c 0 v=0.
Proof.
by rewrite holomorphic_germ_directional_coefficient_real_value holomorphic_germ_jet_zero linear0 scaler0.
Qed.

(** Source for [holomorphic_germ_directional_add]: actual divided
    derivatives preserve the original germ sum, extending
    3.4.5, p. 319, under 3.4.12, p. 339. *)
Lemma holomorphic_germ_directional_add (alpha beta:G):c (alpha+beta) v=c alpha v+c beta v.
Proof.
by rewrite !holomorphic_germ_directional_coefficient_real_value holomorphic_germ_jet_add linearD scalerDr.
Qed.

(** Source for [holomorphic_germ_directional_sum]: finite original
    germ sums have the corresponding coefficient sums, supporting
    the complex Taylor argument of 3.4.8(5), p. 328. *)
Lemma holomorphic_germ_directional_sum (T:finType) (F:T->G):
  c (\sum_(i:T) F i) v=\sum_(i:T) c (F i) v.
Proof.
exact:(big_morph (fun alpha:G=>c alpha v) holomorphic_germ_directional_add holomorphic_germ_directional_zero).
Qed.
End Arithmetic.
