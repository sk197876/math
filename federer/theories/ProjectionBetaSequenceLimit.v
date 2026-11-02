(** Supporting normalizer limit for Federer (1969), 2.10.9, p. 175. Identify
    the actual beta constants with the probability norms of a simple unit
    exterior vector, as proved for 2.7.16(6), pp. 139–140, and use scalar
    norm continuity from 2.4.17, p. 90. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic EuclideanInnerProduct
  EuclideanProjectionMetric ExteriorDiameterUP ExteriorNorm
  OrthogonalProjectionConstants ProjectionConstantNorms ProjectionBeta ProjectionBetaContinuity
  OrthogonalProjectionProbability BoundedProbabilityExponentNorm
  ProbabilityScalarNormLeftContinuity MeasureExponentDomain ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_beta_left_sequence_limit]: supporting
    beta limit for the displayed measure limit in Federer
    2.10.9, p. 175. The real exponent sequence can oscillate
    within [1,t]; the limit exponent can be infinity. *)
Theorem projection_beta_left_sequence_limit (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (p : nat -> R) (t : \bar R) :
  (forall k, (1<=p k)%R /\ (p k)%:E<=t) ->
  extended_order_limit (fun k => (p k)%:E) t ->
  extended_order_limit (fun k => (@projection_beta R n m hmn (p k)%:E)%:E)
    (@projection_beta R n m hmn t)%:E.
Proof.
move=> hp hl.
have ht : 1<=t := le_trans ((hp 0%N).1 : (1 : \bar R)<=(p 0%N)%:E) (hp 0%N).2.
have [xi [hs hunit]] := @euclidean_simple_unit_vector_exists R n m hmn.
pose g (q : orthogonal_projection_metric_space R n m) :
    real_norm_metric_space (scalar_absolute_value_norm R) :=
  projection_norm (real_exterior_two_nonzero R) xi q.
have hg := @simple_projection_norm_scalar_measurable R n m hmn xi hs.
have hbound q : (`|g q|<=1)%R.
  rewrite /g (ger0_norm (projection_norm_nonnegative (real_exterior_two_nonzero R) xi q)).
  by rewrite -hunit; exact: projection_norm_bound.
have hfin := @bounded_probability_exponent_norm_finite R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  g 1%R 1 (@theta_star_total R n m hmn) ltr01 hbound (lexx 1) hg.
have hh := @probability_scalar_norm_left_sequence_limit R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  g p t (@theta_star_total R n m hmn) hp hg hfin hl.
have hval s (hst : 1<=s) : (@projection_beta R n m hmn s)%:E=
    measure_exponent_norm (@orthogonal_projection_probability R n m hmn) (partial_function_total g) s.
  exact: esym (@projection_beta_scalar_norm_value R n m hmn xi s hs hunit hst).
have hseq : (fun k => (@projection_beta R n m hmn (p k)%:E)%:E)=
    (fun k => measure_exponent_norm (@orthogonal_projection_probability R n m hmn)
      (partial_function_total g) (p k)%:E).
  apply: funext=> k; exact: hval (p k)%:E (hp k).1.
by rewrite hseq (hval t ht).
Qed.
