(** Federer (1969), 3.2.48, p. 284: the actual
    signed inner integral on A intersect g(B). The existing
    sealed parameterized integral retains exactly its integrability
    domain, so exceptional undefined fibres receive no default value. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures EuclideanRectangularAdjoint
  HausdorffMeasure PartialFunctionUP PartialZeroExtension SummableRealFunctionUP
  MeasureIntegralUP MeasureSubsetIntegral ParameterizedIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_intersection]: the original
    set A intersect g(B), 3.2.48, p. 284. The map
    g is the actual member of the existing orthogonal-group
    carrier, with its original action on Euclidean vectors. *)
Definition spherical_kinematic_intersection (R:realType) N
    (A B:set (R_n R N)) (g:euclidean_orthogonal_group R N):=
  A `&` (orthogonal_element_map g @` B).

(** Source for [spherical_kinematic_weight]: the printed
    signed product alpha(a) beta(g inverse(a)), 3.2.48,
    p. 284. The inverse is the actual adjoint of
    the orthogonal map; no selected extension is used. *)
Definition spherical_kinematic_weight (R:realType) N
    (alpha beta:R_n R N->R) (g:euclidean_orthogonal_group R N) (a:R_n R N):=
  alpha a*beta (euclidean_rectangular_adjoint (orthogonal_element_map g) a).

(** Source for [spherical_kinematic_inner_integral]: the actual
    partial inner-integral function in the displayed formula
    of 3.2.48, p. 284. Its values use the sealed
    integral laws already established in Chapter 2. *)
Definition spherical_kinematic_inner_integral (R:realType) N lambda
    (A B:set (R_n R N)) (alpha beta:R_n R N->R):=
  parameterized_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R N)) lambda)
    (fun g:euclidean_orthogonal_group R N=>partial_function_zero_extension
      (0:extended_real_line R) (spherical_kinematic_intersection A B g)
      (real_total_integrand (spherical_kinematic_weight alpha beta g))).

(** Source for [spherical_kinematic_inner_integral_graph]: the
    exact signed graph of the original inner integral in
    3.2.48, p. 284. Equality includes definedness and
    all original intersection and weight values. *)
Lemma spherical_kinematic_inner_integral_graph (R:realType) N lambda
    (A B:set (R_n R N)) (alpha beta:R_n R N->R)
    (g:euclidean_orthogonal_group R N) z:
  partial_function_graph (spherical_kinematic_inner_integral lambda A B alpha beta) g z <->
  is_measure_subset_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R N)) lambda)
    (spherical_kinematic_intersection A B g)
    (real_total_integrand (spherical_kinematic_weight alpha beta g)) z.
Proof. exact (parameterized_integral_specification _ _ g z). Qed.
