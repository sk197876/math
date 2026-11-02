(** Supporting Federer (1969), 2.10.46, p. 204, and Freilich (1950), Theorem
    4.5, Part 7, pp. 248–250. For each fixed transverse projection, finite
    I_1 measure makes its multiplicity integrals finite for almost every
    orthogonal change of source coordinates. This is an orbit-wise
    consequence of 2.10.15, p. 178, and the finite-integral criterion in
    2.4.3(4), p. 82. It permits the cylinder proof to fix the transverse
    factor before averaging, without making a measurable choice of it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures OrthogonalInjectionSpaces
  OrthogonalGroupTopology OrthogonalProbabilityBackground IsotropyGroupTopology LinearGroupSealed
  CompactGroupHaarNormalisation ProjectionOrbitMultiplicity ProjectionMultiplicityIntegral
  ProjectionBeta IntegralGeometricMeasure ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureFiniteUpperApproximant TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_projection_orbit_almost_finite_integrals]:
    supporting finite-fibre qualification under the inner rotation
    average in Freilich (1950), Theorem 4.5, Part 7,
    pp. 248–250, for 2.10.46, p. 204.
    The fixed projection is arbitrary. Its orbit average has
    finite value beta_1 times I_1, so almost every integrand
    value is finite, including when I_1 itself is zero. *)
Theorem finite_projection_orbit_almost_finite_integrals (R : realType) n k (hkn : (k<=n)%N)
    (mulO : euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n)
    (invO : euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n)
    (eO : euclidean_orthogonal_group R n)
    (hO : is_subgroup_restriction
      (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (euclidean_orthogonal_group R n) mulO invO eO)
    (theta : set (euclidean_orthogonal_group R n) -> \bar R)
    (htheta : is_normalised_haar_measure mulO theta)
    (V : set (inner_metric_space (@euclidean_inner_productP R n)))
    (q : orthogonal_projection_metric_space R n k) :
  (0<k)%N -> borel_set V -> @integral_geometric_measure R n k hkn 1 V< +oo ->
  measure_almost_everywhere theta [set g | projection_multiplicity_integral V
    (orthogonal_projection_action (@euclidean_inner_productP R k)
      (@euclidean_inner_productP R n) (@coordinate_basisP R n) hO g q)< +oo].
Proof.
move=> hk hV hfin.
have hi := @projection_orbit_multiplicity_integral R n k hkn mulO invO eO hO theta htheta V q hk hV.
have hnon := measure_nonnegative (@integral_geometric_measure_is_measure R n k hkn 1 (lexx _)) V.
have hnum : @integral_geometric_measure R n k hkn 1 V \is a fin_num.
  by rewrite (ge0_fin_numE hnon).
have hvalue : (@projection_beta R n k hkn 1)%:E*@integral_geometric_measure R n k hkn 1 V< +oo.
  by rewrite -(fineK hnum) -EFinM ltry.
have hv := measure_upper_integral_unique (measure_upper_integral_specification theta _) hi.2.1.
have hh := @finite_upper_integral_below_infinity_almost R (euclidean_orthogonal_group R n)
  theta (@orthogonal_probability_is_measure R n mulO theta htheta)
  (partial_function_total (fun g=>projection_multiplicity_integral V
    (orthogonal_projection_action (@euclidean_inner_productP R k)
      (@euclidean_inner_productP R n) (@coordinate_basisP R n) hO g q))) ltac:(by rewrite hv).
apply: (@measure_almost_everywhere_mono R (euclidean_orthogonal_group R n)
  theta (@orthogonal_probability_is_measure R n mulO theta htheta) _ _ _ hh).
move=> g [z [hz hzfin]].
change (projection_multiplicity_integral V
  (orthogonal_projection_action (@euclidean_inner_productP R k)
    (@euclidean_inner_productP R n) (@coordinate_basisP R n) hO g q)=z) in hz.
by rewrite /= hz.
Qed.
