(** Supporting gauge limit for Federer (1969), 2.10.9, p. 175: the actual
    normalized integral-geometric costs beta_t zeta_t approach their value
    from below. Apply the proved probability norm limit to the measurable
    projection-volume function of 2.10.5, p. 172. The source set may be
    unbounded and the projected volumes or the limiting norm may be
    infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric SuslinSetUP
  IntegralGeometricGauge ProjectionBeta OrthogonalProjectionProbability
  ProjectedVolumeMeasurability ProbabilityExtendedNormLeftContinuity ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_normalized_gauge_left_sequence_limit]:
    supporting pointwise cost limit for the displayed measure
    limit in Federer 2.10.9, p. 175. This concerns costs of
    actual Suslin sets, not yet the limit of the constructed
    measures. The normalization uses the proved positive beta
    constants from 2.7.16(6), p. 134. *)
Theorem integral_geometric_normalized_gauge_left_sequence_limit
    (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : nat -> R) (t : \bar R) :
  is_suslin_set R S -> (forall k, (1<=p k)%R /\ (p k)%:E<=t) ->
  extended_order_limit (fun k => (p k)%:E) t ->
  extended_order_limit (fun k => (@projection_beta R n m hmn (p k)%:E)%:E *
      @integral_geometric_gauge R n m hmn (p k)%:E S)
    ((@projection_beta R n m hmn t)%:E * @integral_geometric_gauge R n m hmn t S).
Proof.
move=> hS hp hl.
have ht : 1<=t := le_trans ((hp 0%N).1 : (1 : \bar R)<=(p 0%N)%:E) (hp 0%N).2.
have hnorm := @probability_nonnegative_extended_norm_left_sequence_limit R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (projected_volume_function (m:=m) S) p t (@theta_star_total R n m hmn)
  (fun q => projected_volume_function_nonnegative S q) hp
  (@theta_star_projected_volume_measurable R n m hmn S hS) hl.
have heq : (fun k => (@projection_beta R n m hmn (p k)%:E)%:E *
      @integral_geometric_gauge R n m hmn (p k)%:E S)=
    (fun k => NonnegativeExtendedExponentNorm.nonnegative_extended_exponent_norm
      (@orthogonal_projection_probability R n m hmn) (projected_volume_function (m:=m) S) (p k)%:E).
  apply: funext=> k; exact: (@integral_geometric_gauge_normalized R n m hmn (p k)%:E (hp k).1 S).
by rewrite heq (@integral_geometric_gauge_normalized R n m hmn t ht S).
Qed.
