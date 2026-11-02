(** Federer (1969), 3.2.19, p. 256: the upper bound one
    and the vanishing off-chart density follow from 2.10.19(5),(4),
    p. 181. Transport the spherical almost-everywhere conclusions to
    Hausdorff measure by the already proved comparison of 2.10.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffSphericalComparison
  BorelRegularMeasureUP SphericalMetricDensityTheorems MetricDensityMonotonicity
  MetricDensities PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_null_of_spherical_null]: supporting null-set
    transport in Federer 3.2.19, p. 256, from H^m<=S^m of
    2.10.2(2), p. 171. No measurability is needed for the null set. *)
Lemma hausdorff_null_of_spherical_null (R : realType) (X : metricType R) m (A : set X) :
  @spherical_measure R X m A=0 -> @hausdorff_measure R X m A=0.
Proof.
move=> hNull; apply/eqP; rewrite eq_le (measure_nonnegative (@hausdorff_measure_is_measure R X m)) andbT.
by have hh := @hausdorff_measure_le_spherical_measure R X m A; rewrite hNull in hh.
Qed.

(** Source for [finite_hausdorff_spherical_finite]: supporting finite
    spherical mass required by 2.10.19(5) in Federer 3.2.19,
    p. 256. The finite factor 2^m is the comparison of
    2.10.2(2), p. 171, including m=0. *)
Lemma finite_hausdorff_spherical_finite (R : realType) (X : metricType R) m (A : set X) :
  @hausdorff_measure R X m A< +oo -> @spherical_measure R X m A< +oo.
Proof.
move=> hFin.
have hFinite : @hausdorff_measure R X m A \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative (@hausdorff_measure_is_measure R X m) A)).
have hh := @spherical_measure_le_double_hausdorff_measure R X m A.
apply: (le_lt_trans hh _); rewrite -(fineK hFinite) -EFinM; exact: ltry.
Qed.

(** Source for [finite_hausdorff_restricted_upper_density]: the bound
    upper density at most one used in Federer 3.2.19, p. 256.
    This is 2.10.19(5), p. 181, transported by H^m<=S^m;
    measurability of A is not needed for this bound. *)
Theorem finite_hausdorff_restricted_upper_density (R : realType) (X : metricType R) m (A : set X) :
  @hausdorff_measure R X m A< +oo ->
  measure_almost_everywhere (@hausdorff_measure R X m)
    [set x | upper_metric_density m (measure_restrict (@hausdorff_measure R X m) A) x<=1].
Proof.
move=> hFin.
have hSF := finite_hausdorff_spherical_finite hFin.
have hAE := @federer_2_10_19_5 R X m A hSF.
apply: hausdorff_null_of_spherical_null.
apply: (@measure_null_subset R X (@spherical_measure R X m)
  (@spherical_measure_is_measure R X m) _ _ _ hAE).
move=> x hNot hBound; apply: hNot.
apply: (le_trans _ hBound).
exact: (@metric_densities_monotone R X m
  (measure_restrict (@hausdorff_measure R X m) A)
  (measure_restrict (@spherical_measure R X m) A) x
  (fun B=>@hausdorff_measure_le_spherical_measure R X m (A `&` B))).2.
Qed.

(** Source for [finite_hausdorff_off_set_density_zero]: the vanishing
    density off a finite measurable set used in Federer 3.2.19,
    p. 256. Apply 2.10.19(4), p. 181, to the actual
    Hausdorff measure and transport only its exceptional spherical-null set. *)
Theorem finite_hausdorff_off_set_density_zero (R : realType) (X : metricType R) m (A : set X) :
  measure_measurable (@hausdorff_measure R X m) A ->
  @hausdorff_measure R X m A< +oo ->
  measure_almost_everywhere_on (@hausdorff_measure R X m) (~` A)
    [set x | partial_function_graph (metric_density m
      (measure_restrict (@hausdorff_measure R X m) A)) x 0].
Proof.
move=> hA hFin; apply: hausdorff_null_of_spherical_null.
exact: (@federer_2_10_19_4 R X m (@hausdorff_measure R X m) A
  (@hausdorff_measure_is_measure R X m) (@hausdorff_measure_borel_regular R X m) hA hFin).
Qed.
