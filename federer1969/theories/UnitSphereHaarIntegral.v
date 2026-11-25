(** Federer (1969), 3.2.13, p. 251: comparison of
    the actual sphere integral with a normalized O(m) Haar
    orbit integral, by the proved homogeneous-space uniqueness theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal functions
  topology subtype_topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  UnitSphereSpace UnitSphereOrthogonalAction UnitSphereMeasureInvariant CompactInvariantOrbitIntegral
  EulerGamma EulerGammaHalfParameters IsotropyGroupTopology HomogeneousSpaceUP TopologicalGroupUP LinearGroupTopology LinearGroupSealed
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures CompactGroupHaarNormalisation
  CompactSupportFunctionUP MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_sphere_gamma_mass_positive]: strict
    positivity of the actual sphere mass used to normalize
    invariant integration, Federer 3.2.13, p. 251. *)
Lemma unit_sphere_gamma_mass_positive (R:realType) m (hm:(0<m)%N):
  0<2*(euler_gamma_half R)^+m/euler_gamma (@positive_dimension_half R m hm).
Proof.
have hTwo:0<(2:R) by lra.
have hHalf:0<euler_gamma_half R:=euler_gamma_positive (positive_real_half R).
apply:divr_gt0; last exact:euler_gamma_positive.
exact:mulr_gt0 hTwo (exprn_gt0 m hHalf).
Qed.

(** Source for [unit_sphere_haar_integral]: the sphere integral
    is its total mass times the normalized Haar orbit integral,
    the comparison displayed in Federer 3.2.13, p. 251.
    Orthogonal invariance and transitivity are proved, not hypotheses. *)
Theorem unit_sphere_haar_integral (R:realType) m (hm:(0<m)%N)
    (mulS:set_type (euclidean_orthogonal_group R m)->set_type (euclidean_orthogonal_group R m)->
      set_type (euclidean_orthogonal_group R m))
    (invS:set_type (euclidean_orthogonal_group R m)->set_type (euclidean_orthogonal_group R m))
    (eS:set_type (euclidean_orthogonal_group R m))
    (hS:is_subgroup_restriction (linear_group_mul (@euclidean_inner_productP R m) (@coordinate_basisP R m))
      (linear_group_inv (@euclidean_inner_productP R m) (@coordinate_basisP R m))
      (linear_group_unit (@euclidean_inner_productP R m) (@coordinate_basisP R m))
      (euclidean_orthogonal_group R m) mulS invS eS)
    (theta:set (set_type (euclidean_orthogonal_group R m))->\bar R)
    (x:euclidean_unit_sphere_space R m) (u:euclidean_unit_sphere_space R m->R) (q:R):
  is_normalised_haar_measure mulS theta ->compactly_supported_continuous_functions u ->
  is_measure_integral theta (real_total_integrand (u\o orbit_map (@unit_sphere_action R m) x)) q%:E ->
  is_measure_integral (@unit_sphere_hausdorff_measure R m) (real_total_integrand u)
    ((2*(euler_gamma_half R)^+m/euler_gamma (@positive_dimension_half R m hm))*q)%:E.
Proof.
move=>hTheta hu hq.
exact:(@compact_finite_invariant_orbit_integral R
  [the topologicalType of set_type (euclidean_orthogonal_group R m)] (euclidean_unit_sphere_space R m)
  mulS invS eS (@unit_sphere_action R m) (orthogonal_group_lch hS)
  (@unit_sphere_homogeneous R m mulS invS eS hS hm) (@euclidean_unit_sphere_space_hausdorff R m)
  (@unit_sphere_hausdorff_measure R m) theta
  (2*(euler_gamma_half R)^+m/euler_gamma (@positive_dimension_half R m hm)) x
  (@orthogonal_group_compact_space R (R_n R m) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R m) m (@coordinate_basis R m) (@coordinate_basisP R m))
  (@unit_sphere_hausdorff_is_measure R m) (@unit_sphere_hausdorff_borel_regular R m)
  (@unit_sphere_gamma_mass_positive R m hm) (@unit_sphere_hausdorff_total R m hm)
  (fun g=>@unit_sphere_hausdorff_invariant R m g) hTheta u q hu hq).
Qed.
