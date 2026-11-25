(** Federer (1969), 3.3.14, p. 298: actual original projection
    volume bounds, with a common null exception for countable tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanLebesgueDimensions OrthogonalProjectionProbability ProjectedVolumeMeasurability ProjectionBeta
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricCoverCosts BorelCaratheodoryMeasure
  StructureEssentialAlmostBound NonnegativeExtendedExponentNormUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic TopologicalBorel BorelClosedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_integral_geometric_projection_bound]: supporting
    nullity of each original exceptional set in Federer 3.3.14, p. 298.
    Actual zeta-infinity is at most actual I-infinity on every Borel
    source by 2.10.8; actual beta-infinity equals one and the proved
    essential bound gives the original projected-volume comparison. *)
Lemma structure_integral_geometric_projection_bound (R:realType) n m (hmn:(m<=n)%N)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  borel_set S ->measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|euclidean_lebesgue_measure m (euclidean_projection_linear p @` S)<=
      @integral_geometric_measure R n m hmn +oo S].
Proof.
move=>hS.
pose theta:=@orthogonal_projection_probability R n m hmn.
pose g:=@projected_volume_function R n m S.
pose z:=@integral_geometric_gauge R n m hmn +oo S.
have hTheta:=theta_star_is_measure R hmn.
have hNorm:=@integral_geometric_gauge_norm_specification R n m hmn +oo (leey 1) S
  (metric_borel_suslin hS).
rewrite projection_beta_infinity mul1e in hNorm.
have hAlmost:=@structure_essential_almost_bound R (@orthogonal_projection_metric_space R n m)
  theta g z hTheta hNorm.
have hCost:=@borel_caratheodory_cost_bound R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
  (@integral_geometric_gauge R n m hmn +oo)
  (@integral_geometric_gauge_borel_cover_cost R n m hmn +oo (leey 1)) S hS.
apply:(measure_almost_everywhere_mono hTheta _ hAlmost)=>p hp.
exact:le_trans hp hCost.
Qed.

(** Source for [structure_countable_projection_bounds]: supporting
    the common null exception in Federer 3.3.14, p. 298. Any actual
    countable family of Borel tests retains all original projected
    volume bounds simultaneously. No open-set or source-null
    preservation conclusion is part of these hypotheses. *)
Lemma structure_countable_projection_bounds (R:realType) n m (hmn:(m<=n)%N)
    (J:choiceType) (D:set J)
    (S:J->set (inner_metric_space (@euclidean_inner_productP R n))):
  countable D ->(forall j,D j ->borel_set (S j)) ->
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|forall j,D j ->euclidean_lebesgue_measure m (euclidean_projection_linear p @` S j)<=
      @integral_geometric_measure R n m hmn +oo (S j)].
Proof.
move=>hD hS.
exact:(@measure_almost_everywhere_countable R
  (@euclidean_projection_space R n m) J
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  D (fun j=>[set p|euclidean_lebesgue_measure m (euclidean_projection_linear p @` S j)<=
    @integral_geometric_measure R n m hmn +oo (S j)]) hD
  (fun j hj=>@structure_integral_geometric_projection_bound R n m hmn (S j) (hS j hj))).
Qed.
