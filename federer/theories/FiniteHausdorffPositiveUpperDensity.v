(** Federer (1969), 3.3.15, p. 299: verify the actual
    positive upper-density premise for arbitrary finite Hausdorff sources. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import HausdorffMeasure HausdorffSubcriticalMetricDensity
  HausdorffLengthUP HausdorffDiameterCost MetricScaleEnvelope CaratheodoryLimitUP
  MetricDensities MetricDensityMonotonicity MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_hausdorff_positive_upper_density]: supporting
    actual examples for the hypothesis in Federer 3.3.15, p. 299.
    The original 2.10.19(2), p. 181, gives a positive lower bound
    for the upper restricted density outside a Hausdorff null set.
    Original A need not be measurable and the density may be infinite. *)
Lemma finite_hausdorff_positive_upper_density (R:realType) (X:metricType R) m (A:set X):
  @hausdorff_measure R X m A< +oo ->
  measure_almost_everywhere_on (@hausdorff_measure R X m) A
    [set a|0<upper_metric_density m (measure_restrict (@hausdorff_measure R X m) A) a].
Proof.
move=>hFinite.
have hH:=@hausdorff_measure_is_measure R X m.
have hScale d:(0<d)%E ->hausdorff_scale_measure m d A< +oo.
  move=>hd; apply:le_lt_trans _ hFinite.
  exact:(caratheodory_limit_upper (@hausdorff_measure_specification R X m) A hd
    (@metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
      (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) d)).
have hBad:=@hausdorff_subcritical_metric_density_null R X m (hausdorff_scale_measure m +oo) A
  (@metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
    (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) +oo) hScale.
apply:(@measure_null_subset R X _ hH _ _ _ hBad).
move=>a [hA hNot]; split; first exact:hA.
have hNonpositive:(upper_metric_density m (measure_restrict (@hausdorff_measure R X m) A) a<=0)%E.
  by rewrite leNgt; apply/negP.
have hInfinity:((0:R)%:E < (+oo : \bar R))%E:=ltry _.
have hDom S:hausdorff_scale_measure m +oo S<=@hausdorff_measure R X m S.
  exact:(caratheodory_limit_upper (@hausdorff_measure_specification R X m) S hInfinity
    (@metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
      (fun j=>val j) (fun j=>hausdorff_diameter_cost m (val j)) +oo)).
have hOrder:=(@metric_densities_monotone R X m
  (measure_restrict (hausdorff_scale_measure m +oo) A)
  (measure_restrict (@hausdorff_measure R X m) A) a (fun B=>hDom (A `&` B))).2.
apply:le_lt_trans (le_trans hOrder hNonpositive) _.
rewrite lte_fin invr_gt0 exprn_gt0 // ltr0n.
Qed.
