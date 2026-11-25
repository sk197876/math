(** Federer (1969), 3.2.26(3), p. 262: restricting
    to a Borel partition member preserves the tangent plane
    almost everywhere on that member. Expand this implicit
    use of 3.2.19 via the off-set density theorem
    2.10.19(4), p. 181, and the exact restricted-cone laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric PartialFunctionUP HausdorffMeasure HausdorffClosedCoverAgreement
  HausdorffSphericalComparison SphericalMetricDensityTheorems MetricDensities
  MeasureUP MeasureBasic MeasureRestriction MeasureRestrictionSupport MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP BorelRegularRestriction TopologicalBorel BorelFamilyBasic
  RestrictedApproximateTangent MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_borel_subset_omitted_metric_density_zero]:
    supporting restriction step in 3.2.26(3), p. 262.
    Apply 2.10.19(4) to the omitted Borel portion
    W minus S under H^m restricted to W. Spherical
    almost-everywhere nullity implies Hausdorff nullity, so
    the omitted portion has zero m-density almost everywhere
    on S. No tangent-plane or rectifiability premise is needed. *)
Theorem finite_borel_subset_omitted_metric_density_zero (R:realType) m n
    (W S:set (R_n R n)):
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) S ->S `<=` W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W < +oo ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) S [set a|
    partial_function_graph (@metric_density R (inner_metric_space (@euclidean_inner_productP R n)) m
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
        (W `\` S))) a 0].
Proof.
move=>hW hS hSW hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose B:=@spherical_measure R X m.
pose mu:=measure_restrict H W.
pose A:=W `\` S.
have hH:=@hausdorff_measure_is_measure R X m.
have hB:=@spherical_measure_is_measure R X m.
have hMu:=measure_restrict_is_measure hH W.
have hRegular:=borel_regular_restrict_borel hH (@hausdorff_measure_borel_regular R X m) hW.
have hABorel:@borel_set X A.
  rewrite /A setDE; exact:(borel_family_binary_intersection (borel_sets_family X) hW
    (borel_set_complement hS)).
have hAMeas:=borel_regular_borel_measurable hMu hRegular hABorel.
have hAW:A `<=` W by move=>x hx; exact hx.1.
have hAValue:mu A=H A:=measure_restrict_subset_value H hAW.
have hAFinite:mu A < +oo.
  rewrite hAValue; exact:(le_lt_trans (measure_mono hH hAW) hFinite).
have hMuA:measure_restrict mu A=measure_restrict H A.
  rewrite /mu measure_restrict_intersection.
  have hSets:W `&` A=A.
    apply/seteqP; split=>x; first by move=>[_ hx].
    move=>hx; split; first exact:hAW x hx; exact hx.
  by rewrite hSets.
have hOff:=@federer_2_10_19_4 R X m mu A hMu hRegular hAMeas hAFinite.
rewrite hMuA in hOff.
pose Good:set X:=[set a|partial_function_graph (metric_density m (measure_restrict H A)) a 0].
have hBNull:B (S `\` Good)=0.
  apply:(measure_null_subset hB _ hOff)=>a [ha hn]; split; last exact hn.
  by move=>[_ hNotS]; exact:hNotS ha.
have hComparison:=@hausdorff_measure_le_spherical_measure R X m (S `\` Good).
change (is_true (H (S `\` Good)<=B (S `\` Good))) in hComparison.
rewrite hBNull in hComparison.
apply/eqP; rewrite eq_le hComparison /=; exact:(@measure_nonnegative R (Choice.clone X _) H hH (S `\` Good)).
Qed.

(** Source for [finite_borel_subset_approximate_tangent_equal]: the
    tangent-plane restriction implicit in the Borel partition of
    3.2.26(3), p. 262. Zero omitted metric density
    makes the full-density test families equal, so the actual
    approximate cones agree pointwise on a conull subset of S. *)
Theorem finite_borel_subset_approximate_tangent_equal (R:realType) m n
    (W S:set (R_n R n)):
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) S ->S `<=` W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W < +oo ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) S [set a|
    measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) S) m a=
    measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W) m a].
Proof.
move=>hW hS hSW hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have hLoss:=@finite_borel_subset_omitted_metric_density_zero R m n W S hW hS hSW hFinite.
apply:(measure_null_subset hH _ hLoss)=>a [ha hn]; split; first exact ha.
move=>hZero; apply:hn.
exact:(@restricted_approximate_tangent_equal R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  m H S W a hH hSW hZero).
Qed.
