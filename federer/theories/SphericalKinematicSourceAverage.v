(** Federer (1969), 3.2.48, p. 286: averaging the exact original
    source measure over the actual right isotropy action preserves it.
    Every regularity, finiteness, continuity and invariance requirement
    is proved from the printed rectifiability/measurability hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions constructive_ereal topology subtype_topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  LinearBasis HomCompositionDeterminant EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  EuclideanHomInnerCharts HomInner HomSpaceTopology ProductInner ProductFiniteBasis InnerSpaceCountableBase
  LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures IsotropyGroupTopology TopologicalGroupUP
  HaarIntegralUP CompactGroupHaarNormalisation OrthogonalHaarRegularity
  SphericalIsotropyTransverseAction SphericalCoordinateIsotropy SphericalOrthogonalProductAlgebra
  SphericalProductPreimageImage SphericalKinematicSource OrthogonalCartesianRightInvariance
  EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse UnitSphereSpace OrthogonalMaps
  RectifiableSetUP HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureRestriction
  MeasurePushforward ProductMeasure BorelRegularMeasureUP BorelRegularFiniteRestriction InvariantProbabilityAverage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normalised_haar_measure_law]: the measure law already
    included in normalized Haar measure, as used in 3.2.48, p. 286.
    It is extracted from the existing abstract Haar specification. *)
Lemma normalised_haar_measure_law (R:realType) (G:topologicalType)
    (mul:G->G->G) (theta:set G->\bar R):
  is_normalised_haar_measure mul theta ->is_measure theta.
Proof. move=>[[lambda [hInvariant hMeasure hRepresentation hRegular]] hTotal]; exact hMeasure. Qed.

(** Source for [spherical_kinematic_source_average]: the unchanged
    actual source measure in the first equality of the final averaging
    display in 3.2.48, p. 286. All-set equality retains completed
    measurable original subsets; B is genuinely rectifiable as printed. *)
Theorem spherical_kinematic_source_average (R:realType) d k m (c:R_n R (1+d))
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))) (A B:set (R_n R (1+d)))
    (mulS:euclidean_orthogonal_group R d->euclidean_orthogonal_group R d->euclidean_orthogonal_group R d)
    (invS:euclidean_orthogonal_group R d->euclidean_orthogonal_group R d)
    (eS:euclidean_orthogonal_group R d) (theta:set (euclidean_orthogonal_group R d)->\bar R):
  inner_norm (@euclidean_inner_productP R (1+d)) c= 1 ->
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->Q (spherical_coordinate_pole R d)=c ->
  A `<=` @euclidean_unit_sphere_set R (1+d) ->B `<=` @euclidean_unit_sphere_set R (1+d) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) k A ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) k) A ->
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (1+d))) m B ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (1+d))) m) B ->
  is_subgroup_restriction
    (linear_group_mul (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (linear_group_inv (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (linear_group_unit (@euclidean_inner_productP R d) (@coordinate_basisP R d))
    (euclidean_orthogonal_group R d) mulS invS eS ->
  forall hTheta:is_normalised_haar_measure mulS theta,
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R (1+d) (1+d)) (@euclidean_hom_inner_productP R (1+d) (1+d))) in
  let S:=[set z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))|
    spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2] in
  let rho:=measure_restrict (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S in
  measure_pushforward
    (fun z:euclidean_orthogonal_group R d*P=>orthogonal_cartesian_right_translation
      (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map z.1))) z.2)
    (product_measure (normalised_haar_measure_law hTheta)
      (measure_restrict_is_measure (@hausdorff_measure_is_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S))=rho.
Proof.
move=>hc hQ hQc hA hB hRA hMA hRB hMB hGroup hTheta P S rho.
pose H:=Hom (R_n R (1+d)) (R_n R (1+d)).
pose hH:=@euclidean_hom_inner_productP R (1+d) (1+d).
pose hP:=product_inner_productP hH hH.
pose G:=euclidean_orthogonal_group R d.
have hSource:=@spherical_kinematic_source R d k m c A B hc hA hB hRA hMA hRB hMB.
pose hRho:=measure_restrict_is_measure (@hausdorff_measure_is_measure R P
  ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))) S.
have hRhoRegular:is_borel_regular_measure rho.
  exact (@borel_regular_finite_measurable_restriction R P
    (@hausdorff_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))
    (@hausdorff_measure_is_measure R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))
    (@hausdorff_measure_borel_regular R P ((k+d*(d-1)%/2)+(m+d*(d-1)%/2)))
    S hSource.2 hSource.1.2).
have hRhoFinite:(rho setT< +oo)%E.
  rewrite /rho /measure_restrict setIT; exact hSource.1.2.
have [U hU]:=@orthogonal_group_countable_open_base R d.
pose b:=@hom_rank_one_base R (R_n R (1+d)) (R_n R (1+d)) (1+d) (1+d)
  (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)) (@coordinate_basis R (1+d)).
have hb:=@hom_rank_one_baseP R (R_n R (1+d)) (R_n R (1+d)) (1+d) (1+d)
  (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)) (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)).
have [V hV]:=@inner_space_countable_open_base R [the lmodType R of (H*H)%type] _ hP _
  (cartesian_basis b b) (cartesian_basisP hb hb).
pose F:=fun z:G*P=>orthogonal_cartesian_right_translation
  (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map z.1))) z.2.
have hInvariant g:measure_pushforward (fun z:P=>F (g,z)) rho=rho.
  have hMember:=@spherical_isotropy_transverse_operator_member R d Q (orthogonal_element_map g)
    hQ (orthogonal_element_orthogonal g).
  rewrite hQc in hMember.
  have hFixed:euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map g)) c=c.
    have h:=congr1 (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map g))) hMember.2.
    rewrite (euclidean_orthogonal_adjoint_cancel hMember.1) in h; exact (esym h).
  exact (@orthogonal_cartesian_right_translation_measure R (1+d) c
    (euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map g))) A B
    ((k+d*(d-1)%/2)+(m+d*(d-1)%/2))%N (euclidean_orthogonal_adjoint_orthogonal hMember.1) hFixed).
exact (@invariant_probability_average_pushforward R _ _ theta rho
  (normalised_haar_measure_law hTheta) hRho U V F hU hV
  (orthogonal_normalised_haar_borel_regular hGroup hTheta) hRhoRegular hTheta.2 hRhoFinite
  (orthogonal_cartesian_right_inverse_action_continuous hQ) hInvariant).
Qed.
