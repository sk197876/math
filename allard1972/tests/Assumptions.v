(** Axiom audit of the Allard subproject: Allard (1972), sections 2 and 3. The
    only axioms allowed are boolp.propositional_extensionality,
    boolp.functional_extensionality_dep and
    boolp.constructive_indefinite_description. *)
From Allard Require Import AllardHomInnerProduct AllardExteriorPowers AllardOrthogonalProjectors
  AllardGrassmann AllardGrassmannSubspaces AllardJacobians AllardProjectionFormula
  AllardProjectionContinuity.
From Allard Require Import AllardVarifolds AllardImageVarifold AllardRectifiableVarifolds.
From Allard Require Import AllardSimpleProjection AllardTangentMeasurability AllardSetVarifold
  AllardRectifiableSum AllardRectifiableIntegral AllardRectifiableTangent AllardRectifiableDensity
  AllardRectifiableStructure.

(** Allard 2.2. *)
Print Assumptions allard_2_2_hom_inner.
Print Assumptions allard_2_2_hom_norm.
Print Assumptions allard_2_2_norm_comparison.
Print Assumptions rank_one_map_hom_inner.
Print Assumptions allard_2_2_1.
Print Assumptions allard_2_2_2.

(** Allard 2.3 and new:grass_compact. *)
Print Assumptions orthogonal_projector_frame.
Print Assumptions allard_2_3_1.
Print Assumptions allard_2_3_2.
Print Assumptions allard_2_3_3.
Print Assumptions allard_2_3_4.
Print Assumptions allard_2_3_5.
Print Assumptions orthogonal_projectors_compact.
Print Assumptions projection_grassmann_compact.
Print Assumptions projection_grassmann_separable.
Print Assumptions grassmann_bundle_locally_compact.
Print Assumptions grassmann_bundle_separable.
Print Assumptions allard_2_3_identification.

(** Allard 2.4 and 2.4(1). *)
Print Assumptions allard_2_4.
Print Assumptions allard_2_4_gram.
Print Assumptions allard_2_4_1.

(** Blueprint new:projection_formula. *)
Print Assumptions projection_formula_operator_injective.
Print Assumptions projection_formula_map_symmetric.
Print Assumptions projection_formula_map_idempotent.
Print Assumptions projection_formula_map_image.
Print Assumptions projection_formula_jacobian.
Print Assumptions projection_formula_orthogonal_projector.
Print Assumptions projection_formula_domainE.
Print Assumptions projection_formula_domain_open.
Print Assumptions projection_formula_onP.
Print Assumptions projection_formula_continuous.
Print Assumptions projection_formula_grassmann_open.

(** Allard 3.1. *)
Print Assumptions allard_3_1.
Print Assumptions allard_3_1_weight_integral.
Print Assumptions allard_3_1_weight_borel_integral.

(** Allard 3.2(1). *)
Print Assumptions image_bundle_jacobian_continuous.
Print Assumptions image_bundle_map_continuous.
Print Assumptions image_bundle_map_proper.
Print Assumptions image_varifold_unique.
Print Assumptions image_varifoldP.
Print Assumptions allard_3_2_1_varifold.
Print Assumptions allard_3_2_1.
Print Assumptions allard_3_2_1_integral.
Print Assumptions allard_3_2_1_continuous_integral.
Print Assumptions allard_3_2_1_unique.
Print Assumptions image_bundle_map_plane.

(** Allard 3.5 (partial). *)
Print Assumptions approximate_tangent_plane_exists.
Print Assumptions approximate_tangent_cone_closed_ball_local.
Print Assumptions set_approximate_tangent_plane_ae.
Print Assumptions set_varifold_unique.
Print Assumptions set_varifold_weight_borel.

(** Blueprint new:simple_to_projection. *)
Print Assumptions simple_projection_hom_continuous.
Print Assumptions simple_projection_hom_projector.
Print Assumptions simple_projection_hom_image.

(** Allard 3.5 and blueprint al:3.5:lem. *)
Print Assumptions set_tangent_plane_measurable.
Print Assumptions set_tangent_borel_version.
Print Assumptions set_varifold_is_varifold.
Print Assumptions set_varifold_set_varifold.
Print Assumptions set_varifold_weight.
Print Assumptions set_varifold_integral.
Print Assumptions rectifiable_varifold_weight.
Print Assumptions rectifiable_varifold_representation.
Print Assumptions rectifiable_varifold_pushforward.
Print Assumptions rectifiable_varifold_integral.
Print Assumptions rectifiable_sum_tangent_equal.
Print Assumptions rectifiable_sum_tangent_agree.
Print Assumptions rectifiable_sum_tangent_plane_ae.
Print Assumptions rectifiable_sum_tangent_measurable.
Print Assumptions rectifiable_sum_density_ae.
Print Assumptions rectifiable_sum_density_positive_finite.
Print Assumptions rectifiable_sum_measure_with_density.
Print Assumptions rectifiable_sum_measure_metric_density.

(** Allard 3.5(1). *)
Print Assumptions allard_3_5_1_a_only_if.
Print Assumptions allard_3_5_1_b_tangent_ae.
Print Assumptions allard_3_5_1_b_measurable.
Print Assumptions allard_3_5_1_b_pushforward.
Print Assumptions allard_3_5_1_b_integral.
Print Assumptions allard_3_5_1_b_weight.
Print Assumptions allard_3_5_1_b.
