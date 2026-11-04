(** Federer (1969), 3.2.46, p. 282: restore the
    actual source Riemannian volume in the transformation
    formulas. The proved volume density and 2.4.10,
    p. 85, preserve signed integral definedness and values. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations RiemannianTensorUP
  RiemannianMetricCarrier RiemannianHausdorff RiemannianChartReference
  RiemannianChartVolumeDensity RiemannianVolumeIdentification RiemannianChartVolumeIntegral
  RiemannianMapJacobian PartialFunctionUP PartialFunctionBasic PartialDensityProduct
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureChangeOfDensity MeasureStepIntegralIdentification ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_source_density_integral_iff]:
    actual source-volume transport for 3.2.46, p. 282.
    Both signed infinite values and exact partial domains
    are retained. Ordinary reference measurability is the
    premise of this supporting change-of-density lemma, not
    an added hypothesis of the eventual transformation formula. *)
Theorem riemannian_source_density_integral_iff (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g) (hp : 0<=m%:R :> R)
    (u : partial_function (riemannian_metric_space hg) (extended_real_line R)) :
  is_measure_measurable_function (@riemannian_chart_reference R m A g hg) u -> forall a,
  is_measure_integral (riemannian_hausdorff_measure hg m%:R hp) u a <->
  is_measure_integral (@riemannian_chart_reference R m A g hg)
    (partial_density_product u (partial_function_total (fun x : riemannian_metric_space hg=>
      ((riemannian_chart_volume_density hg x)%:E : extended_real_line R)))) a.
Proof.
move=> hU a.
pose X := [the choiceType of riemannian_metric_space hg].
pose phi := @riemannian_chart_reference R m A g hg.
pose w := partial_function_total (fun x : X=>
  ((riemannian_chart_volume_density hg x)%:E : extended_real_line R)).
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have hPositive : measure_almost_everywhere phi (partial_extended_nonnegative_locus w).
  apply: (@measure_almost_everywhere_mono R X phi hPhi setT _ _
    (measure_almost_everywhere_true hPhi))=> x _.
  exists (riemannian_chart_volume_density hg x)%:E; split; first by [].
  rewrite lee_fin; exact: ltW (@riemannian_chart_volume_density_positive R m A g hg x).
exact (@measure_density_integral_iff R X phi (riemannian_hausdorff_measure hg m%:R hp)
  hPhi w u (@riemannian_volume_density_identification R m A g hg hp)
  (@riemannian_chart_density_measurable R m A g hg) hPositive hU a).
Qed.

(** Source for [riemannian_map_area_source_integral_iff]:
    the actual area Jacobian times actual Riemannian source
    volume equals its Euclidean-source form against chart
    reference volume, supporting 3.2.46, p. 282. The
    formula includes singular maps, zero dimension and infinite
    integrals; no cancellation by a possibly zero Jacobian occurs. *)
Theorem riemannian_map_area_source_integral_iff (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) :
  is_measure_measurable_function (@riemannian_chart_reference R m A g hg)
    (extended_riemannian_map_jacobian f m) -> forall a,
  is_measure_integral (riemannian_hausdorff_measure hg m%:R hp)
    (extended_riemannian_map_jacobian f m) a <->
  is_measure_integral (@riemannian_chart_reference R m A g hg)
    (partial_real_function_embed (riemannian_map_euclidean_source_jacobian f m)) a.
Proof.
move=> hJ a.
have hChange := @riemannian_source_density_integral_iff R m A g hg hp
  (extended_riemannian_map_jacobian f m) hJ a.
split=> hi.
- apply: (measure_integral_graph_equivalent _ (hChange.1 hi))=> x z.
  exact: (iff_sym (@riemannian_map_extended_source_volume_graph R m n A B g h hg hh f x z)).
- apply: hChange.2.
  apply: (measure_integral_graph_equivalent _ hi)=> x z.
  exact: (@riemannian_map_extended_source_volume_graph R m n A B g h hg hh f x z).
Qed.
