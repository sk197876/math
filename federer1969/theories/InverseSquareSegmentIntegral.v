(** Supporting inverse-square integral in Federer (1969), 2.6.3(2), p. 118.
    This module proves the finite-interval calculation using the local
    primitive laws and the actual sealed Lebesgue measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype ring.
From Federer Require Import RealMetricBackground UniformPrimitiveUP UniformPrimitiveAlgebra
  UniformPrimitivePowers UniformPrimitiveIntegral ClippedReciprocal StieltjesIntegral
  LebesgueScalarMeasure LebesgueRiemannContinuous MeasureSubsetRealTransfer
  MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_square_riemann_segment]: supporting finite formula
    integral_1^b x^-2 dx = 1-1/b for the improper integral used in Federer
    2.6.3(2), p. 118 The continuous reciprocal is clipped below one,
    preserving its original values throughout the interval. *)
Lemma inverse_square_riemann_segment (R : realType) (b : R) :
  1 <= b -> stieltjes_integral (fun x => x)
    (fun x => (clipped_reciprocal 1 0 x)^+2) 1 b = 1-b^-1.
Proof.
move=> hb; have h10 : (0 : R) < 1+0 by rewrite addr0 ltr01.
pose U := clipped_reciprocal (1 : R) 0.
have hU : continuous U := @clipped_reciprocal_continuous R 1 0 h10.
have h2 : continuous (fun x => (U x)^+2) := continuous_real_square hU.
have hbase := @clipped_reciprocal_uniform_primitive R 1 b 0 h10.
have hs := @uniform_primitive_scale R _ _ 1 b (-1) hbase.
have hp : is_uniform_primitive_on (fun x => (U x)^+2) (fun x => -U x) 1 b.
  apply: (@uniform_primitive_ext R _ _ _ _ 1 b _ hs)=> x _; rewrite /U; split; ring.
have hi := @uniform_primitive_riemann_integral R _ _ 1 b h2 hb hp.
rewrite /U (@clipped_reciprocal_on R 1 0 b hb) (@clipped_reciprocal_on R 1 0 1 (lexx (1 : R))) !addr0 invr1 in hi.
rewrite -hi; ring.
Qed.

(** Source for [inverse_square_lebesgue_segment]: the finite
    Lebesgue-integral calculation underlying integral_1^infinity x^-2 dx=1
    in Federer 2.6.3(2), p. 118 No improper integral value is assumed in
    this finite calculation. *)
Theorem inverse_square_lebesgue_segment (R : realType) (b : R) :
  1 < b -> is_measure_subset_integral (@lebesgue_scalar_measure R) `[1,b]
    (real_total_integrand (fun x => (x^-1)^+2)) (1-b^-1)%:E.
Proof.
move=> hb; have h10 : (0 : R) < 1+0 by rewrite addr0 ltr01.
have hU : continuous (clipped_reciprocal (1 : R) 0) := @clipped_reciprocal_continuous R 1 0 h10.
have h2 : continuous (fun x => (clipped_reciprocal 1 0 x)^+2) := continuous_real_square hU.
have hi := @lebesgue_riemann_continuous_segment R _ 1 b h2 hb.
rewrite (inverse_square_riemann_segment (ltW hb)) in hi.
apply: (@measure_subset_real_transfer_null R R _ (lebesgue_scalar_is_measure R)
  `[1,b] [set 1] _ _ _ (lebesgue_scalar_singleton 1) _ hi).
move=> x hx _; move: hx; rewrite /= in_itv /= => /andP[hx _].
by rewrite (@clipped_reciprocal_on R 1 0 x hx) addr0.
Qed.
