(** Federer (1969), 3.2.7, p. 246: the
    actual weighted multiplicity of the printed
    oscillatory curve has infinite upper integral.
    The level-count proof uses no unproved
    regularity or multiplicity assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra ring.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureIntegralUP MeasureIntegralBounds MappingMultiplicity ScalarAbsoluteContinuousArea
  OscillatorySubstitutionCurve OscillatoryCurveLevelCount ReciprocalRootWeightUP ReciprocalRootWeightBasic
  InverseRootMultiplicityDivergence LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [oscillatory_weight_area_target_upper_integral_infinite]:
    the missing summability of g times multiplicity
    in the third example of Federer 3.2.7,
    p. 246. Dyadic target bands each carry
    uniformly positive mass, so the actual target
    upper integral is positive infinity. *)
Theorem oscillatory_weight_area_target_upper_integral_infinite (R:realType) (g:R->R):
  is_reciprocal_root_weight g ->
  measure_upper_integral (@lebesgue_scalar_measure R)
    (scalar_curve_area_target_integrand (@oscillatory_substitution_curve R) `[0,1] g)=+oo%E.
Proof.
move=>hg.
pose f:=@oscillatory_substitution_curve R.
pose N:=fun y=>@mapping_multiplicity R [the choiceType of real_line_metric R] R f `[0,1] y.
pose H:=fun y:R=>((g y)%:E*N y:extended_real_line R)%E.
have [c [/andP[hc0 hc1] hCount]]:=oscillatory_curve_small_level_multiplicity R.
apply:(@inverse_root_multiplicity_upper_integral_infinite R H c hc0).
- move=>y; apply:mule_ge0; first by rewrite lee_fin; exact:reciprocal_root_weight_nonnegative hg y.
  exact:mapping_multiplicity_nonnegative.
- move=>n hn y hy hY.
  have hnR:(0:R)<n%:R by rewrite ltr0n.
  have hn1:(1:R)<=n%:R by rewrite ler1n.
  have hr0:0<c/n%:R by rewrite divr_gt0.
  have hr1:c/n%:R<=1 by rewrite ler_pdivrMr // mul1r; exact (le_trans hc1 hn1).
  have hy1:y<=1 by nra.
  have hN:(n%:R%:E<=N y)%E:=hCount n hn y hy hY.
  have hG:(0<g y).
    rewrite (reciprocal_root_weight_positive_value hg hy hy1) invr_gt0 sqrtr_gt0; exact hy.
  have hGE:(0<=(g y)%:E)%E by rewrite lee_fin; exact:ltW hG.
  have hMul:=lee_wpmul2l hGE hN.
  change (is_true (((g y)%:E*n%:R%:E<=H y)%E)) in hMul.
  rewrite (reciprocal_root_weight_positive_value hg hy hy1) -EFinM in hMul.
  have hEq:(Num.sqrt y)^-1*n%:R=n%:R/Num.sqrt y by ring.
  by rewrite hEq in hMul.
Qed.
