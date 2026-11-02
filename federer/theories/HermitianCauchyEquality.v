(** Federer (1969), 1.8.2, p. 39: equality in Hermitian Cauchy's inequality
    holds exactly for complex-linearly dependent vectors. The phase argument
    reduces this to the real criterion in 1.7.1, p. 28 *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear ScalarRestriction ComplexScalarSealed
  ComplexScalarLaws ComplexModulus ComplexUnitPhase HermitianUP HermitianRealImaginary
  HermitianComplexLinearity HermitianCauchy InnerProductUP InnerProductLaws InnerNorm
  InnerCauchyEquality IndependentPair DependentPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [hermitian_cauchy_equality]: Federer 1.8.2,
    p. 39, equality criterion following the displayed Cauchy inequality.
    The dependence is over C; zero vectors are included. *)
Theorem hermitian_cauchy_equality (R : rcfType)
    (V : lmodType (ComplexScalars.C R)) (H : V -> V -> ComplexScalars.C R)
    (hH : is_hermitian_product H) (v w : V) :
  complex_modulus (H v w) = inner_norm (hermitian_real_inner_product hH) v *
    inner_norm (hermitian_real_inner_product hH) w <->
  ~ @independent_pair (ComplexScalars.C R) V v w.
Proof.
pose hB := hermitian_real_inner_product hH.
pose B := hermitian_real_part H.
pose N := inner_norm hB.
split.
- move=> heq hi.
  have hv := independent_pair_left_nonzero hi.
  have hw := independent_pair_right_nonzero hi.
  have hn : H v w != 0.
    apply/eqP=> hz.
    have hm : complex_modulus (H v w) = 0 by apply/eqP; rewrite complex_modulus_eq0 hz.
    have hpos : 0 < N v * N w.
      apply: mulr_gt0; by rewrite /N inner_norm_gt0.
    by rewrite -heq hm ltxx in hpos.
  have [c [hc hp]] := complex_positive_phase_exists hn.
  have hphase : H v (c *: w) = ComplexScalars.embed R (complex_modulus (H v w)).
    by rewrite (hermitian_scale_right hH) mulrC.
  have heqR : `|B v (c *: w)| = N v * N (c *: w).
    rewrite /B /hermitian_real_part hphase re_embed
      (ger0_norm (complex_modulus_ge0 _)) heq.
    by rewrite /N (hermitian_norm_scale hH) hc mul1r.
  have hdep := (proj1 (@inner_cauchy_equality_dependent R
    (restricted_space (ComplexScalars.embed R) V) B hB v (c *: w))) heqR.
  case: (proj1 (@dependent_pair_cases R (restricted_space (ComplexScalars.embed R) V) v (c *: w)) hdep) => [hz|[a hscaled]].
  + have hc0 : c != 0 by rewrite -complex_modulus_eq0 hc oner_eq0.
    have hcw : c *: w != 0 by rewrite scaler_eq0 negb_or hc0 hw.
    by rewrite hz eqxx in hcw.
  + have hx : v = (ComplexScalars.embed R a * c) *: w.
      change (v = ComplexScalars.embed R a *: (c *: w)) in hscaled.
      by rewrite scalerA in hscaled.
    have hno := independent_pair_not_scaled hi (ComplexScalars.embed R a * c).
    by rewrite hx eqxx in hno.
- move/(proj1 (dependent_pair_cases v w))=> [->|[c ->]].
  + rewrite (bil0r (hermitian_real_bilinear hH)) inner_norm0 mulr0.
    apply/eqP; by rewrite complex_modulus_eq0.
  + rewrite (hermitian_scale_left hH) complex_modulus_mul complex_modulus_conjugate
      (hermitian_diagonal_real hH) complex_modulus_real
      (ger0_norm (inner_nonnegative hB w)) (hermitian_norm_scale hH).
    by rewrite -inner_norm_sqr expr2 mulrA.
Qed.
