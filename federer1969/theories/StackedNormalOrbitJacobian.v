(** Diagonal rotation of normal frames supporting Federer (1969), 2.10.16,
    p. 178. Orthogonal exterior naturality in 1.7.5, p. 32, reduces a pair
    of rotations to their relative rotation; the wedge integral of
    2.7.16(6), p. 139, is then continuous. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct Hom TensorUP
  EuclideanLinearMaps InnerMetric EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces IsotropyGroupTopology
  LinearGroupTopology LinearGroupSealed TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP
  HomogeneousSpaceLaws StackedNormalFamily StackedNormalJacobian EuclideanNormalJacobian
  ProjectionNormalVector ProjectionNormalOrbit OrthogonalWedgeIntegrals
  ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorHomogeneousProducts ExteriorNorm ExteriorNormNaturality
  RealPower CompactSupportFunctionUP RealMetricBackground TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PairOrbit.
Variable R : realType.
Variables n a r : nat.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation P := (orthogonal_projection_metric_space R n a).
Local Notation Q := (orthogonal_projection_metric_space R n r).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable F : P*Q -> {linear R_n R n -> R_n R (a+r)}.
Hypothesis hF : is_stacked_normal_family F.
Local Notation Aa := (orthogonal_projection_action (@euclidean_inner_productP R a) hBn hbn hO).
Local Notation Ar := (orthogonal_projection_action (@euclidean_inner_productP R r) hBn hbn hO).

(** Source for [stacked_normal_jacobian_diagonal_rotation]:
    supporting orthogonal invariance for the double normal
    average in 2.10.16, p. 178, by the exterior
    isometry law of 1.7.5, p. 32. *)
Lemma stacked_normal_jacobian_diagonal_rotation (p : P) (q : Q) (g : O) :
  euclidean_normal_jacobian (F (Aa g p,Ar g q))=euclidean_normal_jacobian (F (p,q)).
Proof.
rewrite !(@stacked_normal_jacobian_wedge R n a r F hF)
  !(@projection_normal_orbit R n _ mulO invO eO hO) -exterior_power_map_product.
apply: exterior_norm_orthogonal_natural.
by move=> x y; rewrite !hom_as_linearE; exact: orthogonal_element_inner.
Qed.

(** Source for [stacked_normal_jacobian_relative_rotation]:
    supporting reduction to one relative rotation for
    2.10.16, p. 178. Apply the preceding isometry
    simultaneously to both normal frames. *)
Lemma stacked_normal_jacobian_relative_rotation (p : P) (q : Q) (s t : O) :
  euclidean_normal_jacobian (F (Aa s p,Ar t q))=
    euclidean_normal_jacobian (F (p,Ar (mulO (invO s) t) q)).
Proof.
have hG := topological_group_laws (lch_group_topological (orthogonal_group_lch hO)).
have hAa := orthogonal_projections_homogeneous (@euclidean_inner_productP R a) (@coordinate_basisP R a) hO.
have hAr := orthogonal_projections_homogeneous (@euclidean_inner_productP R r) (@coordinate_basisP R r) hO.
rewrite -(@stacked_normal_jacobian_diagonal_rotation (Aa s p) (Ar t q) (invO s))
  (homogeneous_translation_inverse_left hG hAa) -(homogeneous_action_compatible hAr).
by [].
Qed.

(** Source for [stacked_normal_jacobian_orbit_continuous]:
    supporting continuous angular integrand for 2.10.16,
    p. 178. The norm is the exponent-one wedge
    integrand of 2.7.16(6), p. 139. *)
Lemma stacked_normal_jacobian_orbit_continuous (p : P) (q : Q) :
  continuous (fun t : O => (euclidean_normal_jacobian (F (p,Ar t q)) : real_line_metric R)).
Proof.
have hk := @orthogonal_wedge_integrand_compact R (euclidean_two_nonzero R) n r a
  (projection_normal_vector q) (projection_normal_vector p) 1
  (projection_normal_vector_simple q) (projection_normal_vector_simple p) ltr01.
have he : (fun g : O => real_power (exterior_norm (euclidean_two_nonzero R) hBn
    (exterior_product (exterior_power_map (hom_as_linear (orthogonal_element_map g)) r
      (projection_normal_vector q)) (projection_normal_vector p))) 1)=
    (fun t => euclidean_normal_jacobian (F (p,Ar t q))).
  apply/funext=> g.
  rewrite real_power_one_exponent ?exterior_norm_nonnegative //
    -(projection_normal_orbit hO q g) exterior_product_norm_swap.
  exact: esym (stacked_normal_jacobian_wedge hF p (Ar g q)).
by rewrite he in hk; exact hk.1.
Qed.

(** Source for [stacked_normal_jacobian_pair_continuous]:
    supporting joint continuity of the two-frame angular
    factor for 2.10.16, p. 178. Reduction to the
    relative rotation proves joint, not merely separate,
    continuity. *)
Lemma stacked_normal_jacobian_pair_continuous (p : P) (q : Q) :
  continuous (fun z : O*O => (euclidean_normal_jacobian (F (Aa z.1 p,Ar z.2 q)) : real_line_metric R)).
Proof.
have hT := lch_group_topological (orthogonal_group_lch hO).
have he : (fun z : O*O => euclidean_normal_jacobian (F (Aa z.1 p,Ar z.2 q)))=
    (fun z : O*O => euclidean_normal_jacobian (F (p,Ar (mulO (invO z.1) z.2) q))).
  apply/funext=> -[s t]; exact: stacked_normal_jacobian_relative_rotation.
rewrite he.
have hc : continuous (fun z : O*O => (invO z.1,z.2)).
  apply (@topological_pair_continuous (O*O)%type O O (fun z => invO z.1) (@snd O O));
    last exact: second_projection_continuous.
  move=> z; exact (continuous_comp (@first_projection_continuous O O z)
    (@topological_group_inv_continuous O mulO invO eO hT z.1)).
move=> z; exact (continuous_comp (continuous_comp (hc z)
  (@topological_group_mul_continuous O mulO invO eO hT (invO z.1,z.2)))
  (@stacked_normal_jacobian_orbit_continuous p q (mulO (invO z.1) z.2))).
Qed.
End PairOrbit.
