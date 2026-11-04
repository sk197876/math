(** Federer (1969), 3.2.46, p. 282: the actual
    Hausdorff-volume density formula as a genuine integral,
    on every reference-measurable chart subset. Positivity,
    density measurability and integral existence are proved. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianChartReference
  RiemannianChartVolumeDensity RiemannianVolumeIdentification
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableRealEmbedding ContinuousBorelPreimages TopologicalBorel
  MeasureSubsetIntegral MeasureDensityUP MeasureDensity DerivationIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_chart_density_measurable]: the
    actual continuous positive density is measurable for
    ordinary chart volume, supporting 3.2.46, pp. 281–282.
    Its whole original domain is retained. *)
Lemma riemannian_chart_density_measurable (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :
  is_measure_measurable_function (@riemannian_chart_reference R n A g hg)
    (partial_function_total (fun x : riemannian_metric_space hg=>
      ((riemannian_chart_volume_density hg x)%:E : extended_real_line R))).
Proof.
pose M := [the topologicalType of riemannian_metric_space hg].
pose phi := @riemannian_chart_reference R n A g hg.
have hPhi := @riemannian_chart_reference_is_measure R n A g hg.
apply: (@measurable_total_real_embedding R M phi hPhi).
constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hPhi.
- move=> U hU; rewrite partial_function_total_preimage.
  apply: (@riemannian_chart_reference_borel_measurable R n A g hg).
  exact (@continuous_borel_preimage M (real_line_metric R)
    (riemannian_chart_volume_density hg)
    (@riemannian_chart_volume_density_continuous R n A g hg) U (open_borel_set hU)).
Qed.

(** Source for [riemannian_chart_volume_integral]: the
    displayed volume formula in Federer 3.2.46, p. 282,
    on the actual chart subtype. Every measurable subset is
    allowed, including infinite mass and dimension zero. *)
Theorem riemannian_chart_volume_integral (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (hp : 0<=n%:R :> R)
    (S : set (riemannian_metric_space hg)) :
  measure_measurable (@riemannian_chart_reference R n A g hg) S ->
  is_measure_subset_integral (@riemannian_chart_reference R n A g hg) S
    (partial_function_total (fun x : riemannian_metric_space hg=>
      ((riemannian_chart_volume_density hg x)%:E : extended_real_line R)))
    (riemannian_hausdorff_measure hg n%:R hp S).
Proof.
move=> hS.
pose M := [the choiceType of riemannian_metric_space hg].
pose phi := @riemannian_chart_reference R n A g hg.
pose w := partial_function_total (fun x : M=>
  ((riemannian_chart_volume_density hg x)%:E : extended_real_line R)).
have hPhi := @riemannian_chart_reference_is_measure R n A g hg.
have hDensity := @riemannian_volume_density_identification R n A g hg hp.
have hNonnegative : measure_almost_everywhere phi (partial_extended_nonnegative_locus w).
  apply: (@measure_almost_everywhere_mono R M phi hPhi setT _ _
    (measure_almost_everywhere_true hPhi))=> x _.
  exists (riemannian_chart_volume_density hg x)%:E; split; first by [].
  rewrite lee_fin; exact: ltW (@riemannian_chart_volume_density_positive R n A g hg x).
have hI := @nonnegative_density_subset_integral R M phi w S hPhi
  (@riemannian_chart_density_measurable R n A g hg) hNonnegative hS.
have hValue := measure_density_unique (measure_with_density_laws phi w) hDensity S.
by rewrite hValue in hI.
Qed.
