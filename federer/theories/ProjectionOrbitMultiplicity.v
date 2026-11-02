(** Supporting rotation averaging in Federer (1969), 2.10.16, p. 178.
    Average the actual Lebesgue multiplicity integral along a projection
    orbit of O(n). Its value is the theta-star integral of 2.10.15, p. 178,
    by the pushforward characterization of 2.7.16(6), p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures OrthogonalInjectionSpaces
  OrthogonalGroupTopology OrthogonalProbabilityBackground AffineSubspaceInvariantMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed HomogeneousSpaceUP HomogeneousSpaceLaws
  CompactGroupHaarNormalisation ProjectionCompositionProbability OrthogonalProjectionProbability
  ProjectionMultiplicityIntegral ProjectionMultiplicityParameterisation IntegralGeometricMultiplicity
  ProjectionBeta IntegralGeometricMeasure ExtendedRealOrderTopology PartialFunctionBasic
  TopologicalBorel MeasureUP MeasureIntegralUP MeasureIntegralUniqueness PushforwardTotalNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section ProjectionOrbit.
Variable R : realType.
Variables n m : nat.
Hypothesis hmn : (m<=n)%N.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbm := (@coordinate_basisP R m).
Local Notation P := (orthogonal_projection_metric_space R n m).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Local Notation Ap := (orthogonal_projection_action hBm hBn hbn hO).

(** Source for [projection_orbit_multiplicity_integral]: supporting
    actual Haar-orbit integral for 2.10.16, p. 178.
    Continuous parameter measurability is proved from joint
    counts and Fubini, before using the orbit pushforward;
    no unsupported completed-measurable composition is used. *)
Theorem projection_orbit_multiplicity_integral
    (A : set (inner_metric_space hBn)) (p : P) :
  (0<m)%N -> borel_set A ->
  is_measure_integral theta
    (partial_function_total (fun s => projection_multiplicity_integral A (Ap s p)))
    ((@projection_beta R n m hmn 1)%:E*@integral_geometric_measure R n m hmn 1 A).
Proof.
move=> hmpos hA.
pose ht := @orthogonal_probability_is_measure R n mulO theta htheta.
have hr := @orthogonal_probability_borel_regular R n mulO invO eO hO theta htheta.
have hw := @orthogonal_probability_whole_countably_measurable R n mulO theta htheta.
have [U hU] := @orthogonal_group_countable_base R n.
pose q := orbit_map Ap p.
have hAP := orthogonal_projections_homogeneous hBm hbm hO.
have hq : continuous q := orbit_map_continuous hAP p.
have hg := @projection_multiplicity_continuous_parameter_measurable R O theta ht hr U n m q A hU hw hq hA.
have [a [ha hb]] := @pushforward_total_nonnegative_integrals R O P theta ht q
  (projection_multiplicity_integral (m:=m) A)
  (fun r => projection_multiplicity_integral_nonnegative r hA) hg.
rewrite (@projection_probability_orbit R n m hmn mulO invO eO hO theta p htheta) in hb.
have he := measure_integral_unique hb (@federer_2_10_15 R n m hmn A hmpos hA).2.1.
by rewrite he in ha.
Qed.
End ProjectionOrbit.
