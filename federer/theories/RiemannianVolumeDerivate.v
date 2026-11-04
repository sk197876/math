(** Federer (1969), 3.2.46, p. 281, last sentence:
    the derivate of H_rho^n with respect to L^n at a
    equals sqrt(discr g(a)). The statement below holds at
    every original chart point with the original partial
    ratio arithmetic, not merely almost everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MetricSubsetBackground RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianChartReference RiemannianChartVolumeDensity RiemannianVolumeDensityContinuity
  RiemannianVolumeIdentification RiemannianReferenceFineCells
  ContinuousPositiveDensityDerivate MeasureDerivates PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_46_volume_derivate]: the
    pointwise derivate asserted in the last sentence of
    3.2.46, p. 281. The fine relation includes every
    positive finite Euclidean cell containing its base point;
    actual small Euclidean balls prove domain fineness.
    All natural dimensions, including zero, are retained. *)
Theorem federer_3_2_46_volume_derivate (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (hp : 0<=n%:R :> R)
    (a : @metric_subset R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] A) :
  partial_function_graph
    (@measure_derivate R
      [the metricType R of @metric_subset R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] A]
      (riemannian_hausdorff_measure hg n%:R hp)
      (@riemannian_chart_reference R n A g hg)
      (positive_finite_containing_relation (@riemannian_chart_reference R n A g hg)))
    a (riemannian_chart_volume_density hg a)%:E.
Proof.
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose C := [the metricType R of @metric_subset R E A].
apply: (@continuous_positive_density_derivate R C
  (@riemannian_chart_reference R n A g hg) (riemannian_hausdorff_measure hg n%:R hp)
  (riemannian_chart_volume_density hg) a).
- exact: riemannian_chart_reference_is_measure.
- exact: riemannian_hausdorff_is_measure.
- exact: riemannian_chart_reference_regular.
- exact: riemannian_volume_density_identification.
- exact (@riemannian_volume_density_along_continuous_map R n A g hg C
    (fun x=>val x) (fun x=>set_valP x)
    (@metric_subset_inclusion_continuous R E A)).
- exact: riemannian_chart_volume_density_positive.
- exact: riemannian_reference_fine_positive_cells.
Qed.
