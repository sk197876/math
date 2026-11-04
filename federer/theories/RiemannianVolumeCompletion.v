(** Federer (1969), 3.2.46, p. 282: ordinary
    and Riemannian top-volume have the same completed
    measurable subsets of the original chart. The proof
    uses the actual null equivalence and proved countable
    finite-volume cover, rather than assuming completed
    measurability from a topological equivalence. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianChartReference RiemannianChartVolumeDensity RiemannianVolumeIdentification
  RiemannianVolumeFiniteCover RiemannianHausdorffNullEquivalence
  RealHausdorffMeasure EuclideanHausdorffLebesgue
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensityMeasurable
  BorelRegularMeasureUP BorelSigmaFiniteNullTransfer ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_volume_reference_null_iff]:
    actual top-volume and ordinary reference volume have
    identical null subsets, supporting 3.2.46, p. 282.
    All original subsets, including nonmeasurable ones, and
    dimension zero are retained. *)
Theorem riemannian_volume_reference_null_iff (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g) (hp : 0<=m%:R :> R)
    (S : set (riemannian_metric_space hg)) :
  riemannian_hausdorff_measure hg m%:R hp S=0%E <->
    @riemannian_chart_reference R m A g hg S=0%E.
Proof.
have h := @riemannian_hausdorff_null_iff R m A g hg m%:R hp S.
have hValue : @real_hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] m%:R hp
    ((fun x : riemannian_metric_space hg=>val x) @` S)=
    @riemannian_chart_reference R m A g hg S.
  rewrite real_hausdorff_measure_natural riemannian_chart_reference_value.
  exact: (euclidean_hausdorff_spherical_lebesgue _).1.
by rewrite hValue in h.
Qed.

(** Source for [riemannian_volume_reference_measurable_iff]:
    full completed top-volume measurability agrees with
    ordinary chart measurability, supporting 3.2.46, p. 282.
    The finite Borel sandwich is used only after restricting
    to actual finite-measure pieces. No hull excess is
    declared null for an arbitrary source. *)
Theorem riemannian_volume_reference_measurable_iff (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g) (hp : 0<=m%:R :> R)
    (S : set (riemannian_metric_space hg)) :
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S <->
    measure_measurable (@riemannian_chart_reference R m A g hg) S.
Proof.
pose X := [the topologicalType of riemannian_metric_space hg].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose phi := @riemannian_chart_reference R m A g hg.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
split.
- exact (@borel_null_transfer_sigma_finite_measurable R X mu phi hMu hPhi
    (@riemannian_hausdorff_borel_regular R m A g hg m%:R hp)
    (@riemannian_volume_countably_measurable R m A g hg hp)
    (fun D hD=>@riemannian_chart_reference_borel_measurable R m A g hg D hD)
    (fun D hD=>(@riemannian_volume_reference_null_iff R m A g hg hp D).1 hD) S).
- move=> hS.
  apply: (@measure_density_preserves_measurable_sets R X phi mu hPhi
    (partial_function_total (fun x : X=>
      ((riemannian_chart_volume_density hg x)%:E : extended_real_line R))) S
    (@riemannian_volume_density_identification R m A g hg hp) _ hS).
  apply: (@measure_almost_everywhere_mono R X phi hPhi setT _ _
    (measure_almost_everywhere_true hPhi))=> x _.
  exists (riemannian_chart_volume_density hg x)%:E; split; first by [].
  rewrite lee_fin; exact: ltW (@riemannian_chart_volume_density_positive R m A g hg x).
Qed.
