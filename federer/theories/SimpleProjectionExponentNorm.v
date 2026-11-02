(** Federer (1969), 2.10.37, printed p. 198: the norm of the projected
    endpoint-product function is beta_t(n,m) times the original exterior
    norm, by 2.7.16(6), p. 140. Derive the scalar and nonnegative
    extended-input versions from that existing abstract projection constant
    and the actual invariant probability. Both finite exponents and infinity
    are retained. No relevant working-erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanProjectionMetric ExteriorDiameterUP ExteriorGrading ExteriorNorm AssociatedSubspace
  OrthogonalProjectionConstants ProjectionConstantNorms ProjectionBeta ProjectionBetaContinuity
  OrthogonalProjectionProbabilityUP OrthogonalProjectionProbability OrthogonalGroupTopology
  OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures
  RealNormUP NormMetric PartialFunctionBasic MeasureLpNormUP MeasureLpNorm
  MeasureEssentialNormUP MeasureEssentialNorm MeasureExponentDomain
  NonnegativeExtendedExponentNorm NonnegativeExtendedScalarNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simple_projection_scalar_exponent_norm]: supporting
    scalar form of the second display in
    the proof of 2.10.37, p. 198.
    This is the already proved 2.7.16(6),
    p. 140, instantiated at the actual beta
    and projection probability, without a unit-norm
    hypothesis on the simple exterior vector. *)
Theorem simple_projection_scalar_exponent_norm (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (xi : exterior_power (R_n R n) m) (t : \bar R) :
  simple xi -> (1<=t)%E ->
  measure_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (fun p : orthogonal_projection_metric_space R n m =>
      (projection_norm (real_exterior_two_nonzero R) xi p :
        real_norm_metric_space (scalar_absolute_value_norm R)))) t =
    ((@projection_beta R n m hmn t)*
      exterior_norm (real_exterior_two_nonzero R) (@euclidean_inner_productP R n) xi)%:E.
Proof.
move=> hs ht.
have [mulS [invS [eS hS]]] := orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have htheta := @orthogonal_projection_probability_specification R n m hmn mulS invS eS hS.
have hb := @projection_beta_specification R n m hmn t ht.
have hn := @projection_norm_seminorm R (real_exterior_two_nonzero R) n m
  mulS invS eS hS t (@projection_beta R n m hmn t)
  (@orthogonal_projection_probability R n m hmn) xi ht hb htheta hs.
clear hb; case: t ht hn=> [p| |] ht hn //=.
- have hp : (1<=p)%R := ht.
  exact: measure_lp_norm_unique
    (@measure_lp_norm_specification R _ R^o (fun y : R => `|y|)
      (scalar_absolute_value_norm R) (@orthogonal_projection_probability R n m hmn) p _
      (@theta_star_is_measure R n m hmn) hp
      (@simple_projection_norm_scalar_measurable R n m hmn xi hs)) hn.
- have [ha hl] := measure_essential_norm_specification
    (@orthogonal_projection_probability R n m hmn) (fun y : R => `|y|)
    (partial_function_total (projection_norm (real_exterior_two_nonzero R) xi)).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - exact: hn.2 _ ha.
  - exact: hl _ hn.1.
Qed.

(** Source for [simple_projection_extended_exponent_norm]: supporting
    nonnegative extended-input form of the norm
    identity in 2.10.37, p. 198.
    The projection norms are finite real values;
    the existing scalar embedding theorem identifies
    their actual extended-input exponent norm. *)
Theorem simple_projection_extended_exponent_norm (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (xi : exterior_power (R_n R n) m) (t : \bar R) :
  simple xi -> (1<=t)%E ->
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (fun p : orthogonal_projection_metric_space R n m =>
      (projection_norm (real_exterior_two_nonzero R) xi p)%:E) t =
    ((@projection_beta R n m hmn t)*
      exterior_norm (real_exterior_two_nonzero R) (@euclidean_inner_productP R n) xi)%:E.
Proof.
move=> hs ht.
rewrite (@nonnegative_extended_norm_scalar_embedding R (orthogonal_projection_metric_space R n m)
  _ (@theta_star_is_measure R n m hmn)
  (fun p => (projection_norm (real_exterior_two_nonzero R) xi p :
    real_norm_metric_space (scalar_absolute_value_norm R))) t
  (fun p => projection_norm_nonnegative (real_exterior_two_nonzero R) xi p) ht
  (@simple_projection_norm_scalar_measurable R n m hmn xi hs)).
exact: simple_projection_scalar_exponent_norm.
Qed.
