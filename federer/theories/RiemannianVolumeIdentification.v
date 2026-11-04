(** Federer (1969), 3.2.46, pp. 281–282: actual
    top-dimensional rho Hausdorff measure is the density
    sqrt(discr g) times ordinary chart volume. The proof
    discharges all localisation and regularity hypotheses;
    no measure or Jacobian formula is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLinearMaps RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianChartReference RiemannianChartVolumeDensity RiemannianChartEllipsoid
  RiemannianLocalVolumeComparison ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureDensityUP MeasureContinuousLocalDensity BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_volume_density_identification]:
    the actual rho Hausdorff measure is integration against
    sqrt(discr g), Federer 3.2.46, pp. 281–282. This
    stronger outer-integral formulation holds on every chart
    subset, retaining infinite mass and the R^0 unit atom.
    The printed measurable-set integral is a consequence. *)
Theorem riemannian_volume_density_identification (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (hp : 0<=n%:R :> R) :
  is_measure_density (@riemannian_chart_reference R n A g hg)
    (partial_function_total (fun x : riemannian_metric_space hg=>
      ((riemannian_chart_volume_density hg x)%:E : extended_real_line R)))
    (riemannian_hausdorff_measure hg n%:R hp).
Proof.
pose M := [the topologicalType of riemannian_metric_space hg].
pose phi := @riemannian_chart_reference R n A g hg.
pose mu := riemannian_hausdorff_measure hg n%:R hp.
pose h := riemannian_chart_volume_density hg.
have [U hBase] := @riemannian_chart_countable_open_base R n A g hg.
apply: (@measure_continuous_local_density R M phi mu U h n).
- exact: riemannian_chart_reference_is_measure.
- exact: riemannian_hausdorff_is_measure.
- exact hBase.
- exact: riemannian_chart_reference_regular.
- move=> B hB; split; first exact: riemannian_chart_reference_borel_measurable hB.
  exact (@borel_regular_borel_measurable R M mu
    (@riemannian_hausdorff_is_measure R n A g hg n%:R hp)
    (@riemannian_hausdorff_borel_regular R n A g hg n%:R hp) B hB).
- exact: riemannian_chart_volume_density_continuous.
- exact: riemannian_chart_volume_density_positive.
- move=> lambda hLambda a.
  have [L [r [hr [hDet0 [hGraph [hPatch hBounds]]]]]] :=
    @riemannian_local_volume_comparison R n A g hg (val a) (set_valP a) lambda hp hLambda.
  pose V := [set x : M | inner_norm (@euclidean_inner_productP R n) (L (val x-val a))<r].
  exists V; split; first exact: riemannian_chart_ellipsoid_open.
  split; first by rewrite /V /= subrr linear0 inner_norm0.
  move=> S hS.
  have hNear x (hx : S x) : inner_norm (@euclidean_inner_productP R n) (L (val x-val a))<=r.
    exact: ltW (hS x hx).
  have hVolume := hBounds S hNear.
  have hValue : euclidean_det L=h a.
    exact: partial_function_single_valued hGraph
      (@riemannian_chart_volume_density_graph R n A g hg a).
  by rewrite hValue -(@riemannian_chart_reference_value R n A g hg S) in hVolume.
Qed.
