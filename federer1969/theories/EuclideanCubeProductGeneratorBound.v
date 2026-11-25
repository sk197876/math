(** Federer (1969), 2.10.45, printed pp. 202–203: the diameter covering
    estimate for a Euclidean cube times a second-factor generator. Positive
    meshes decrease to the actual diameter, including zero; no enlargement
    inside the second metric factor is required. This supplies the printed
    cost comparison also for isolated points. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBoxUP SquaredMetricProductUP MetricProductRectangles MetricDiameterUP MetricDiameter
  HausdorffLengthUP HausdorffDiameterCost MetricScaleEnvelopeUP
  EuclideanProductCoefficient EuclideanCubeProductFiniteCover PositiveMeshCostLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_cube_product_generator_bound]: supporting
    exact generator-cost estimate in the last display of
    2.10.45, p. 203. A strictly larger positive mesh
    ceiling replaces the printed assumption diam(T)>0.
    Polynomial continuity recovers the exact cost even at
    diameter zero and natural degree zero. *)
Theorem euclidean_cube_product_generator_bound (R : realType) m k (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second)
    origin axis Q (u delta0 delta : R) (T : set Y) (Delta : \bar R) (nu : set P -> \bar R) :
  @is_euclidean_rectangular_box R m origin axis (fun _=>u) Q ->
  0<=u -> 0<delta -> delta0<delta ->
  (extended_metric_diameter T<=delta0%:E)%E ->
  ((Num.sqrt m.+1%:R*delta)%:E<=Delta)%E ->
  @is_metric_scale_envelope R P (@nonempty_metric_sets R P)
    (fun j=>val j) (fun j=>hausdorff_diameter_cost (k+m) (val j)) Delta nu ->
    (nu (metric_product_rectangle first second Q T)<=
      (euclidean_product_upper_coefficient R m k*(u+delta)^+m)%:E*
        hausdorff_diameter_cost k T)%E.
Proof.
move=> hQ hu hd hgap hT hcap hn.
have hdia0 := metric_diameter_nonnegative (extended_metric_diameter_specification T).
have hf : extended_metric_diameter T \is a fin_num.
  rewrite (ge0_fin_numE hdia0).
  exact: le_lt_trans hT (ltry delta0).
pose d := fine (extended_metric_diameter T).
have hde : extended_metric_diameter T=d%:E := esym (fineK hf).
have hd0 : 0<=d by move: hdia0; rewrite hde lee_fin.
have hdt : d<delta.
  have hle : d<=delta0 by move: hT; rewrite hde lee_fin.
  exact: le_lt_trans hle hgap.
pose K := euclidean_product_upper_coefficient R m k*(u+delta)^+m.
have hK : 0<K.
  rewrite /K mulr_gt0 ?euclidean_product_upper_coefficient_positive //.
  apply: exprn_gt0; lra.
have hh : (nu (metric_product_rectangle first second Q T)<=
    (K*(hausdorff_normalisation R k*d^+k))%:E)%E.
  apply: (@positive_mesh_cost_limit R k d delta K _ hK hd0 hdt)=> h hh hdh hhd.
  have hTh : (extended_metric_diameter T<=h%:E)%E by rewrite hde lee_fin.
  have hph : ((Num.sqrt m.+1%:R*h)%:E<=Delta)%E.
    apply: le_trans _ hcap; rewrite lee_fin.
    have hsqrt := sqrtr_ge0 (m.+1%:R : R); nra.
  exact (@euclidean_cube_product_finite_cutoff_bound R m k P Y pair first second hp
    origin axis Q u h delta T Delta nu hQ hu hh (ltW hhd) hTh hph hn).
by rewrite /hausdorff_diameter_cost /hausdorff_power_cost hde -EFin_expe -!EFinM.
Qed.
