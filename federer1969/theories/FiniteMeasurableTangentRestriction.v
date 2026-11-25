(** Federer (1969), 3.2.32, pp. 269–270: supporting
    restrictions to finite measurable source pieces in 3.2.22.
    The omitted portion has zero source-degree density almost
    everywhere on the retained piece by 2.10.19(4), p. 181. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric PartialFunctionUP HausdorffMeasure HausdorffClosedCoverAgreement
  HausdorffSphericalComparison SphericalMetricDensityTheorems MetricDensities
  MeasureUP MeasureBasic MeasureRestriction MeasureRestrictionSupport MeasureAlmostUP MeasureAlmostBasic
  MeasureFiniteClosure BorelRegularMeasureUP BorelRegularFiniteRestriction RestrictedApproximateTangent
  MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section FiniteMeasurableRestriction.
Variable R:realType.
Variables m n:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation H:=(@hausdorff_measure R X m).

(** Source for [finite_measurable_subset_omitted_metric_density_zero]:
    supporting replacement of W by a finite measurable source
    piece in Federer 3.2.32, pp. 269–270, via 2.10.19(4),
    p. 181. Measurability and finite mass give Borel regularity
    of the restricted measure before applying the density theorem.
    No Borel hypothesis on W or S is added. *)
Theorem finite_measurable_subset_omitted_metric_density_zero (W S:set X):
  measure_measurable H W ->measure_measurable H S ->S `<=` W ->H W< +oo ->
  measure_almost_everywhere_on H S [set a|partial_function_graph
    (@metric_density R X m (measure_restrict H (W `\` S))) a 0].
Proof.
move=>hW hS hSW hFinite.
pose B:=@spherical_measure R X m.
pose mu:=measure_restrict H W.
pose A:=W `\` S.
have hH:=@hausdorff_measure_is_measure R X m.
have hB:=@spherical_measure_is_measure R X m.
have hMu:=measure_restrict_is_measure hH W.
have hRegular:=borel_regular_finite_measurable_restriction hH
  (@hausdorff_measure_borel_regular R X m) hW hFinite.
have hAMeas:measure_measurable mu A.
  apply:measure_restrict_measurable; exact (@measure_measurable_difference R X H hH W S hW hS).
have hAW:A `<=` W by move=>x hx; exact hx.1.
have hAValue:mu A=H A:=measure_restrict_subset_value H hAW.
have hAFinite:mu A< +oo.
  rewrite hAValue; exact (le_lt_trans (measure_mono hH hAW) hFinite).
have hMuA:measure_restrict mu A=measure_restrict H A.
  rewrite /mu measure_restrict_intersection.
  have hSets:W `&` A=A.
    apply/seteqP; split; first by move=>x [_ hx].
    by move=>x hx; split; first exact:hAW x hx.
  by rewrite hSets.
have hOff:=@federer_2_10_19_4 R X m mu A hMu hRegular hAMeas hAFinite.
rewrite hMuA in hOff.
pose Good:set X:=[set a|partial_function_graph (metric_density m (measure_restrict H A)) a 0].
have hBNull:B (S `\` Good)=0.
  apply:(measure_null_subset hB _ hOff)=>a [ha hn]; split=>//.
  by move=>[_ hNotS]; exact:hNotS ha.
have hComparison:=@hausdorff_measure_le_spherical_measure R X m (S `\` Good).
change (is_true (H (S `\` Good)<=B (S `\` Good))) in hComparison.
rewrite hBNull in hComparison.
apply/eqP; rewrite eq_le hComparison /=; exact (@measure_nonnegative R X H hH (S `\` Good)).
Qed.

(** Source for [finite_measurable_subset_approximate_tangent_equal]:
    supporting unchanged approximate tangent on source restrictions
    in Federer 3.2.32, pp. 269–270. Zero omitted density
    gives exact equality of the two defining full-density test
    families, hence of their actual tangent cones almost everywhere. *)
Theorem finite_measurable_subset_approximate_tangent_equal (W S:set X):
  measure_measurable H W ->measure_measurable H S ->S `<=` W ->H W< +oo ->
  measure_almost_everywhere_on H S [set a|
    measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
      (measure_restrict H S) m a=
    measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
      (measure_restrict H W) m a].
Proof.
move=>hW hS hSW hFinite.
have hH:=@hausdorff_measure_is_measure R X m.
have hLoss:=finite_measurable_subset_omitted_metric_density_zero hW hS hSW hFinite.
apply:(measure_null_subset hH _ hLoss)=>a [ha hn]; split=>//; move=>hZero; apply:hn.
exact (@restricted_approximate_tangent_equal R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  m H S W a hH hSW hZero).
Qed.
End FiniteMeasurableRestriction.
