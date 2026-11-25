(** Federer (1969), 3.3.18, p. 301: the omitted part
    of each original density stratum has ordinary zero density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP
  MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel StructureRectifiableDensityStrata
  HausdorffMeasure HausdorffRestrictedDensity SphericalMetricDensityTheorems
  MetricDensities PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_density_stratum_omitted_density_zero]: the
    displayed zero-density assertion for psi restricted to the
    complement of R_i in Federer 3.3.18, p. 301. The complement
    is actually measurable and has finite mass. Actual 2.10.19(4)
    gives a spherical-null exception. The proved original upper
    stratum comparison transfers that exception to psi. No relative
    derivative or omitted-density conclusion is supplied as a premise. *)
Theorem structure_density_stratum_omitted_density_zero (R:realType) (X:metricType R) m
    (psi:set X->\bar R) (F:set X) (b:R):
  is_measure psi ->is_borel_regular_measure psi ->psi setT< +oo ->(0<b)%R ->
  borel_set F ->
  measure_almost_everywhere_on psi (structure_rectifiable_density_stratum m psi F b)
    [set a|partial_function_graph (metric_density m
      (measure_restrict psi (~` structure_rectifiable_density_stratum m psi F b))) a 0].
Proof.
move=>hPsi hRegular hFinite hb hF.
pose S:=structure_rectifiable_density_stratum m psi F b.
have hS:borel_set S:=@structure_rectifiable_density_stratum_borel R X m psi F b hPsi hF.
have hComplement:measure_measurable psi (~` S):=
  borel_regular_borel_measurable hPsi hRegular (borel_set_complement hS).
have hComplementFinite:psi (~` S)< +oo:=
  le_lt_trans (measure_mono hPsi (subsetT (~` S))) hFinite.
have hOff:=@federer_2_10_19_4 R X m psi (~` S) hPsi hRegular hComplement hComplementFinite.
rewrite setCK in hOff.
pose Good:=[set a:X|partial_function_graph (metric_density m (measure_restrict psi (~` S))) a 0].
have hHNull:@hausdorff_measure R X m (S `\` Good)= 0:=hausdorff_null_of_spherical_null hOff.
have hBound:=(@structure_rectifiable_density_stratum_comparisons R X m psi F
  (S `\` Good) b hPsi hRegular hFinite hb (fun a ha=>ha.1)).2.
rewrite hHNull mule0 in hBound.
apply/eqP; rewrite eq_le hBound (measure_nonnegative hPsi).
by [].
Qed.
