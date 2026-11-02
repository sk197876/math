(** Federer (1969), 2.10.9, p. 175, first sentence: the cost of
    integral-geometric measure satisfies the countable-cover hypothesis of
    2.10.8. Projected Lebesgue measure obeys the covering inequality
    pointwise, and the proved probability Lp countable triangle bound passes
    it to the actual gauge of 2.10.5, p. 172. Keep all infinite values, all
    exponents at least one and unbounded Suslin generators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability
  OrthogonalProjectionProbability ProjectionBeta IntegralGeometricGauge
  NonnegativeExtendedExponentNorm ProbabilityExtendedNormCover
  NonnegativeSum NonnegativeSumScale MeasureUP MeasureIndexedCover
  SuslinSetUP BorelClosedProjection BorelCoverCostUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge_countable_cover]: direct
    cost-cover assertion implicit in the application of 2.10.8
    by Federer 2.10.9, p. 175. The supporting generalisation
    permits arbitrary countable indexed Suslin families, with
    repeated members and unbounded or infinite-cost sets. *)
Theorem integral_geometric_gauge_countable_cover (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) (J : choiceType) (D : set J)
    (S : J -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=t -> countable D -> is_suslin_set R A ->
  (forall j, D j -> is_suslin_set R (S j)) -> A `<=` \bigcup_(j in D) S j ->
  @integral_geometric_gauge R n m hmn t A<=
    nonnegative_sum D (fun j => @integral_geometric_gauge R n m hmn t (S j)).
Proof.
move=> ht hD hA hS hcover.
have hvol q : projected_volume_function (m:=m) A q<=
    nonnegative_sum D (fun j => projected_volume_function (m:=m) (S j) q).
  apply: (@measure_indexed_cover R _ J (@euclidean_lebesgue_measure R m)
    (@euclidean_lebesgue_is_measure R m) _ D
    (fun j => euclidean_projection_linear q @` S j) hD).
  move=> y [x hx <-]; have [j hj hxj] := hcover x hx; exists j=> //; by exists x.
have hnorm := @probability_nonnegative_extended_norm_cover R _ J
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  t D (projected_volume_function (m:=m) A) (fun j => projected_volume_function (m:=m) (S j))
  (@theta_star_total R n m hmn) hD ht
  (fun q => projected_volume_function_nonnegative A q)
  (fun j q => projected_volume_function_nonnegative (S j) q)
  (@theta_star_projected_volume_measurable R n m hmn A hA)
  (fun j hj => @theta_star_projected_volume_measurable R n m hmn (S j) (hS j hj)) hvol.
have hc : (0<=(@projection_beta R n m hmn t)^-1)%R.
  rewrite invr_ge0; exact: ltW (@projection_beta_positive R n m hmn t ht).
rewrite /integral_geometric_gauge nonnegative_sum_scale //; last first.
  move=> j hj; exact: (@nonnegative_extended_exponent_norm_ge0 R _
    (@orthogonal_projection_probability R n m hmn) (projected_volume_function (m:=m) (S j)) t
    (@theta_star_is_measure R n m hmn) (fun q => projected_volume_function_nonnegative (S j) q)
    ht (@theta_star_projected_volume_measurable R n m hmn (S j) (hS j hj))).
apply: lee_wpmul2l hnorm; by rewrite lee_fin.
Qed.

(** Source for [integral_geometric_gauge_borel_cover_cost]: direct
    applicability of the complete Borel-partition theorem 2.10.8
    to integral-geometric measure in Federer 2.10.9, p. 175.
    Borel sets are Suslin by the proved 2.2.10 background. *)
Theorem integral_geometric_gauge_borel_cover_cost (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  1<=t -> is_borel_cover_cost (@integral_geometric_gauge R n m hmn t).
Proof.
move=> ht; constructor.
- move=> A hA; apply: (@integral_geometric_gauge_nonnegative R n m hmn t ht A).
  exact: metric_borel_suslin hA.
- move=> J D S A hD hA hS hcover.
  apply: (@integral_geometric_gauge_countable_cover R n m hmn t J D S A ht hD _ _ hcover).
  + exact: metric_borel_suslin hA.
  + move=> j hj; exact: metric_borel_suslin (hS j hj).
Qed.
