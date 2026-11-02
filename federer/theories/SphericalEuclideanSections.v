(** Federer (1969), 2.10.27, pp. 190–191: supporting comparison of spherical
    cutoff masses of Euclidean ball sections with the abstract ball-section
    cost profile. A strict diameter margin and positive-radius enlargement
    handle tangent sections, without changing the spherical generator
    family. All proofs use profile laws and existing diameter/infimum
    interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanBlockCoordinates EuclideanMetricProduct EuclideanBallSections
  MetricCartesianProductUP MetricDiameter MetricClosedBalls HausdorffMeasureUP HausdorffDiameterCost HausdorffPowerCostLaws
  HausdorffRadiusCost EuclideanBallVolume EuclideanBallDiameter EuclideanBallSectionProfileUP
  SphericalScaleBallBound MetricScaleEnvelopeUP MetricScaleCutoffCost MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_dimensional_euclidean_closed_ball_diameter]:
    supporting actual source-ball diameter in the fine
    coverings of 2.10.27, p. 191. Positivity
    belongs to the ambient dimension; radius zero
    remains allowed. *)
Lemma positive_dimensional_euclidean_closed_ball_diameter (R : realType) N
    (a : inner_metric_space (@euclidean_inner_productP R N)) (r : R) :
  (0<N)%N -> (0<=r)%R ->
  extended_metric_diameter (metric_closed_ball a r)=(r+r)%R%:E.
Proof.
case: N a=> [a|N a] hN hr; first by rewrite ltn0 in hN.
exact: euclidean_closed_ball_diameter hr.
Qed.

(** Source for [euclidean_positive_dimension_ball_cost]: supporting
    normalized source-ball cost in the first display
    of 2.10.27, p. 191. The ambient dimension
    is positive, while the gauge degree and radius
    may be zero. The ambient zero-dimensional case
    has a separate diameter convention. *)
Lemma euclidean_positive_dimension_ball_cost (R : realType) N k
    (a : inner_metric_space (@euclidean_inner_productP R N)) (r : R) :
  (0<N)%N -> (0<=r)%R ->
  hausdorff_diameter_cost k (metric_closed_ball a r)=(euclidean_unit_ball_volume R k*r^+k)%R%:E.
Proof.
case: N a=> [a|N a] hN hr; first by rewrite ltn0 in hN.
rewrite /hausdorff_diameter_cost (@euclidean_closed_ball_diameter R N a r hr)
  hausdorff_power_cost_finite hausdorff_doubled_radius_normalisation; reflexivity.
Qed.

(** Source for [spherical_ball_section_cutoff_bound]: supporting
    section-cover estimate in 2.10.27, p. 191.
    The cutoff mass is bounded by the specified
    profile for every y, including boundary sections
    of radius zero and empty exterior sections. *)
Theorem spherical_ball_section_cutoff_bound (R : realType) m n k
    (u : inner_metric_space (@euclidean_inner_productP R m))
    (v : inner_metric_space (@euclidean_inner_productP R n)) (r d : R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (q : inner_metric_space (@euclidean_inner_productP R m) -> \bar R) :
  is_metric_scale_envelope
    (fun j : @positive_closed_metric_balls R (inner_metric_space (@euclidean_inner_productP R n))=>val j)
    (fun j=>hausdorff_diameter_cost k (val j)) d%:E nu ->
  is_euclidean_ball_section_profile k u r q -> (0<=r)%R -> (r+r<d)%R -> forall y,
  nu (metric_product_section (fun a b=>@euclidean_block_join R m n (a,b))
    (metric_closed_ball (euclidean_block_join (u,v)) r) y)<=q y.
Proof.
move=> hn hq hr hd y; case: (leP (mdist u y) r)=> hy.
- rewrite (@euclidean_closed_ball_section R m n u y v r hr hy) (ball_section_profile_inside hq hy).
  have hterm : (0<=r^+2-mdist u y^+2)%R.
    rewrite subr_ge0 (ler_sqr _ _)=> //; by rewrite nnegrE ?mdist_ge0.
  have hrho : (Num.sqrt (r^+2-mdist u y^+2)<=r)%R.
    rewrite -(ler_sqr _ _) ?nnegrE ?sqrtr_ge0 // sqr_sqrtr //.
    have hh := sqr_ge0 (mdist u y); lra.
  apply: spherical_scale_closed_ball_bound hn (sqrtr_ge0 _) _.
  exact: le_lt_trans (lerD hrho hrho) hd.
- rewrite (ball_section_profile_outside hq hy).
  have he : metric_product_section (fun a b=>@euclidean_block_join R m n (a,b))
      (metric_closed_ball (euclidean_block_join (u,v)) r) y=set0.
    apply/seteqP; split=> [z hz|z []].
    have hmem : ((fun p=>(@euclidean_block_split R m n p).1) @`
        (metric_closed_ball (euclidean_block_join (u,v)) r)) y.
      exists (euclidean_block_join (y,z)); last by rewrite euclidean_block_joinK.
      exact hz.
    rewrite (@euclidean_closed_ball_first_projection R m n u v r hr) in hmem.
    have hle : (mdist u y<=r)%R := hmem.
    by have hh := lt_le_trans hy hle; rewrite ltxx in hh.
  rewrite he (measure_empty (metric_scale_envelope_is_measure hn
    (fun j=>hausdorff_diameter_cost_nonnegative k (val j)))); exact: lexx.
Qed.
