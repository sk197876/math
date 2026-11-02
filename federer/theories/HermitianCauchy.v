(** Federer (1969), 1.8.2, p. 39: Hermitian Cauchy's inequality, proved as
    in the book by multiplying the second vector by a unit complex scalar so
    that the pairing is real. The real Cauchy inequality is 1.7.1, p. 28 *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexModulusUP ComplexModulus ComplexUnitPhase HermitianUP HermitianRealImaginary
  HermitianComplexLinearity InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Cauchy.
Variable R : rcfType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Variable V : lmodType C.
Variable H : V -> V -> C.
Hypothesis hH : is_hermitian_product H.
Local Notation B := (hermitian_real_part H).
Local Notation hB := (hermitian_real_inner_product hH).
Local Notation N := (inner_norm hB).

(** Source for [hermitian_norm_scale]: Federer 1.8.2,
    p. 39, supporting norm identity |cv|=|c||v|, used for a unit phase. *)
Lemma hermitian_norm_scale (c : C) (v : V) : N (c *: v) = complex_modulus c * N v.
Proof.
apply: inner_norm_value; first exact: mulr_ge0 (complex_modulus_ge0 c) (inner_norm_nonnegative hB v).
by rewrite exprMn complex_modulus_sqr inner_norm_sqr hermitian_scale_diagonal.
Qed.

(** Source for [hermitian_cauchy]: Federer 1.8.2, p. 39,
    the displayed inequality |H(v,w)| <= |v||w|, with no
    finite-dimensional hypothesis. *)
Theorem hermitian_cauchy (v w : V) : complex_modulus (H v w) <= N v * N w.
Proof.
have [hz|hz] := eqVneq (H v w) 0.
- have hn : complex_modulus (H v w) = 0.
    apply/eqP; by rewrite complex_modulus_eq0 hz.
  rewrite hn; exact: mulr_ge0 (inner_norm_nonnegative hB v) (inner_norm_nonnegative hB w).
have [c [hc hp]] := complex_positive_phase_exists hz.
have hh := @inner_cauchy_upper R (restricted_space embed V) B hB v (c *: w : V).
have hphase : H v (c *: w) = embed (complex_modulus (H v w)).
  by rewrite (hermitian_scale_right hH) mulrC.
change (is_true (ComplexScalars.re (H v (c *: w)) <= N v * N (c *: w))) in hh.
by rewrite hphase re_embed hermitian_norm_scale hc mul1r in hh.
Qed.
End Cauchy.
