(** Federer (1969), 2.10.35, p. 197: beta_t(n,n)= 1 and orthogonal
    invariance make the equal-dimension integral-geometric gauge equal to
    actual Lebesgue volume. Use only the proved projection and probability-
    norm laws, including infinite volume and exponent. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions MeasureUP MeasureBasic
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability FullDimensionProjections
  OrthogonalProjectionProbability IntegralGeometricGauge FullDimensionProjectionNorm
  NonnegativeExtendedProbabilityConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_dimension_integral_geometric_gauge]: supporting
    equal-dimension gauge calculation used for
    every I_t and Q_t in 2.10.35,
    p. 197. The source may be
    arbitrary because its projected-volume function
    is pointwise constant, hence measurable. *)
Theorem equal_dimension_integral_geometric_gauge (R : realType) (n : nat)
    (hnn : (n<=n)%N) (t : \bar R)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (1<=t)%E -> @integral_geometric_gauge R n n hnn t S=euclidean_lebesgue_measure n S.
Proof.
move=> ht.
have he : projected_volume_function (m:=n) S=
    (fun _ : orthogonal_projection_metric_space R n n=>euclidean_lebesgue_measure n S).
  apply: funext=> p; exact: equal_dimension_projection_volume S (euclidean_projection_linear_member p).
rewrite /integral_geometric_gauge (equal_dimension_projection_beta hnn ht) invr1 mul1e he.
exact: (@probability_nonnegative_extended_constant_norm R (orthogonal_projection_metric_space R n n)
  _ (@theta_star_is_measure R n n hnn) _ t (@theta_star_total R n n hnn)
  (measure_nonnegative (euclidean_lebesgue_is_measure R n) S) ht).
Qed.
