(** Angular constant in the affine slicing identity of Federer (1969),
    2.10.16, p. 178. Apply the proved wedge integral of 2.7.16(6), p. 139,
    at exponent one to the two simple unit normal vectors. Its orbit image
    is the actual theta-star probability.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric Hom EuclideanLinearMaps
  EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces IsotropyGroupTopology LinearGroupTopology
  LinearGroupSealed CompactGroupHaarNormalisation HomogeneousSpaceUP ProjectionCompositionProbability
  OrthogonalProbabilityBackground ProjectionNormalVector ProjectionNormalOrbit StackedNormalFamily
  StackedNormalJacobian EuclideanNormalJacobian OrthogonalWedgeIntegrals ProjectionBeta
  ExteriorDiameterUP ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts ExteriorNorm
  ExteriorNormNaturality RealPower RealPowerContinuity ExtendedRealOrderTopology SummableRealFunctionUP PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  PushforwardTotalNonnegativeIntegral OrthogonalProjectionProbability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Average.
Variable R : realType.
Variables n a r : nat.
Hypothesis hamn : (a+r<=n)%N.
Local Notation hnr := (leq_trans (leq_addl a r) hamn).
Hypothesis hrna : (r<=n-a)%N.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation P := (orthogonal_projection_metric_space R n a).
Local Notation Q := (orthogonal_projection_metric_space R n r).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Variable F : P*Q -> {linear R_n R n -> R_n R (a+r)}.
Hypothesis hF : is_stacked_normal_family F.

(** Source for [stacked_normal_jacobian_haar_average]: supporting
    Haar-orbit form of the angular average for 2.10.16,
    p. 178. This is exactly the unit-vector case of
    the wedge integral of 2.7.16(6), p. 139. *)
Theorem stacked_normal_jacobian_haar_average (p : P) (q0 : Q) :
  is_measure_integral theta
    (partial_function_total (fun g => (euclidean_normal_jacobian
      (F (p,orthogonal_projection_action (@euclidean_inner_productP R r) hBn hbn hO g q0)))%:E))
    ((@projection_beta R n r hnr 1 / @projection_beta R (n-a) r hrna 1)%R)%:E.
Proof.
pose h2 := euclidean_two_nonzero R.
pose Ap := orthogonal_projection_action (@euclidean_inner_productP R r) hBn hbn hO.
have hb1 := @projection_beta_specification R n r hnr 1 (lexx _).
have hb2 := @projection_beta_specification R (n-a) r hrna 1 (lexx _).
have he2 : real_exterior_two_nonzero R=h2 := Prop_irrelevance _ _.
rewrite he2 in hb1 hb2.
have hsum : (r+a<=n)%N by rewrite addnC.
have hi := @orthogonal_wedge_integral R h2 n mulO invO eO hO r a 1
  (@projection_beta R n r hnr 1) (@projection_beta R (n-a) r hrna 1) theta
  (projection_normal_vector q0) (projection_normal_vector p) ltr01 hsum hb1 hb2 htheta
  (projection_normal_vector_simple q0) (projection_normal_vector_simple p).
rewrite !projection_normal_vector_unit real_power_one_base !mulr1
  real_power_one_exponent ?(ltW hb1.1) // real_power_negative_exponent ?hb2.1 //
  real_power_one_exponent ?(ltW hb2.1) // in hi.
pose f q : extended_real_line R := (euclidean_normal_jacobian (F (p,q)))%:E.
have hpoint g : real_power (exterior_norm h2 hBn
    (exterior_product (exterior_power_map (hom_as_linear (orthogonal_element_map g)) r
      (projection_normal_vector q0)) (projection_normal_vector p))) 1 = euclidean_normal_jacobian (F (p,Ap g q0)).
  rewrite real_power_one_exponent ?exterior_norm_nonnegative //
    -(projection_normal_orbit hO q0 g) exterior_product_norm_swap.
  exact: esym (stacked_normal_jacobian_wedge hF p (Ap g q0)).
have hi' : is_measure_integral theta (partial_function_total (fun g => f (Ap g q0)))
    ((@projection_beta R n r hnr 1 / @projection_beta R (n-a) r hrna 1)%R)%:E.
  apply: (@measure_integral_graph_equivalent R O theta _ _ _ _ hi)=> g z.
  rewrite real_total_integrand_graph /f hpoint; by [].
exact hi'.
Qed.

(** Source for [stacked_normal_jacobian_average]: supporting
    actual theta-star average for 2.10.16, p. 178:
    its value is beta_1(n,r) divided by beta_1(n-a,r).
    This is 2.7.16(6), p. 139, for the two unit
    simple normal vectors, after the orbit pushforward. *)
Theorem stacked_normal_jacobian_average (p : P) (q0 : Q) :
  is_measure_integral (@orthogonal_projection_probability R n r hnr)
    (partial_function_total (fun q => (euclidean_normal_jacobian (F (p,q)))%:E))
    ((@projection_beta R n r hnr 1 / @projection_beta R (n-a) r hrna 1)%R)%:E.
Proof.
pose h2 := euclidean_two_nonzero R.
pose Ap := orthogonal_projection_action (@euclidean_inner_productP R r) hBn hbn hO.
have hb1 := @projection_beta_specification R n r hnr 1 (lexx _).
have hb2 := @projection_beta_specification R (n-a) r hrna 1 (lexx _).
have he2 : real_exterior_two_nonzero R=h2 := Prop_irrelevance _ _.
rewrite he2 in hb1 hb2.
have hsum : (r+a<=n)%N by rewrite addnC.
have hi := @orthogonal_wedge_integral R h2 n mulO invO eO hO r a 1
  (@projection_beta R n r hnr 1) (@projection_beta R (n-a) r hrna 1) theta
  (projection_normal_vector q0) (projection_normal_vector p) ltr01 hsum hb1 hb2 htheta
  (projection_normal_vector_simple q0) (projection_normal_vector_simple p).
rewrite !projection_normal_vector_unit real_power_one_base !mulr1
  real_power_one_exponent ?(ltW hb1.1) // real_power_negative_exponent ?hb2.1 //
  real_power_one_exponent ?(ltW hb2.1) // in hi.
pose f q : extended_real_line R := (euclidean_normal_jacobian (F (p,q)))%:E.
have hpoint g : real_power (exterior_norm h2 hBn
    (exterior_product (exterior_power_map (hom_as_linear (orthogonal_element_map g)) r
      (projection_normal_vector q0)) (projection_normal_vector p))) 1 = euclidean_normal_jacobian (F (p,Ap g q0)).
  rewrite real_power_one_exponent ?exterior_norm_nonnegative //
    -(projection_normal_orbit hO q0 g) exterior_product_norm_swap.
  exact: esym (stacked_normal_jacobian_wedge hF p (Ap g q0)).
have hi' : is_measure_integral theta (partial_function_total (fun g => f (Ap g q0)))
    ((@projection_beta R n r hnr 1 / @projection_beta R (n-a) r hrna 1)%R)%:E.
  apply: (@measure_integral_graph_equivalent R O theta _ _ _ _ hi)=> g z.
  rewrite real_total_integrand_graph /f hpoint; by [].
have hfpos q : 0 <= f q by rewrite /f lee_fin; exact: euclidean_normal_jacobian_nonnegative.
have [b [hb hc]] := @pushforward_total_nonnegative_integrals R O Q theta
  (@orthogonal_probability_is_measure R n mulO theta htheta) (orbit_map Ap q0) f
  hfpos hi'.1.
rewrite (@projection_probability_orbit R n r hnr mulO invO eO hO theta q0 htheta) in hc.
have he := measure_integral_unique hb hi'.
by rewrite he in hc.
Qed.
End Average.
