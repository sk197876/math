(** Federer (1969), 1.8.2, p. 40, the mu=1 calculation: for orthonormal v,w,
    A(v,w)=(iv).w <= 1, with equality exactly when w=iv. The supporting
    result below needs only that the two vectors have unit norm, a slight
    strengthening of that step. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarSealed HermitianUP
  HermitianRealImaginary HermitianRotation InnerProductUP InnerNorm
  InnerCauchy InnerNormInequalities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Pair.
Variable R : rcfType.
Variable V : lmodType (ComplexScalars.C R).
Variable H : V -> V -> ComplexScalars.C R.
Hypothesis hH : is_hermitian_product H.
Local Notation hB := (hermitian_real_inner_product hH).
Local Notation B := (hermitian_real_part H).
Local Notation J := (@hermitian_rotation R V).
Variables v w : V.
Hypothesis hv : inner_norm hB v = 1.
Hypothesis hw : inner_norm hB w = 1.

(** Source for [hermitian_unit_pair_bound]: Federer 1.8.2,
    p. 40, the unit-pair upper bound, also applied to each
    pair in the normal form on the associated space. *)
Lemma hermitian_unit_pair_bound : hermitian_imaginary_part H v w <= 1.
Proof.
rewrite (hermitian_imaginary_rotation hH).
have hh := inner_cauchy_upper hB (J v) w.
by rewrite (hermitian_rotation_norm hH) hv hw mul1r in hh.
Qed.

(** Source for [hermitian_unit_pair_equality]: Federer 1.8.2,
    p. 40, equality in that bound forces the second member of
    the pair to be i times the first, and conversely. *)
Theorem hermitian_unit_pair_equality :
  hermitian_imaginary_part H v w = 1 <-> w = J v.
Proof.
have hww : B w w = 1 by rewrite -(inner_norm_sqr hB w) hw expr1n.
have hvv : B (J v) (J v) = 1.
  by rewrite -(inner_norm_sqr hB (J v)) (hermitian_rotation_norm hH) hv expr1n.
have hw0 : w != 0.
  by rewrite -(inner_norm_eq0 hB) hw oner_eq0.
split.
- move=> ha; have hpair : B (J v) w = 1 by rewrite -(hermitian_imaginary_rotation hH).
  have heq : B (J v) w ^+2 = B (J v) (J v) * B w w by rewrite hpair hvv hww expr1n mul1r.
  have hh := (proj1 (inner_cauchy_equality hB (J v) hw0)) heq.
  rewrite hpair hww divr1 scale1r in hh; exact: esym hh.
- move=> ->; rewrite (hermitian_imaginary_rotation hH); exact hvv.
Qed.
End Pair.
