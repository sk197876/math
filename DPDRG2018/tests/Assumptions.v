(** Axiom audit for the formalisation of De Philippis, De Rosa and
    Ghiraldin (2018), Appendix A. Only the three axioms of MathComp's
    boolp (functional_extensionality_dep, propositional_extensionality and
    constructive_indefinite_description) may appear. *)
From DPDRG Require Import DdgGrassmann DdgMovingPlane DdgLemmaA1 DdgGrassmannTangent
  DdgAnisotropicIntegrandUP DdgAnisotropicIntegrand DdgWeightedJacobian DdgFlow
  DdgWeightedJacobianEstimate DdgFirstVariation DdgFirstVariationPoint.

Print Assumptions ddg_A_1.
Print Assumptions ddg_A_1_perp.
Print Assumptions ddg_moving_planeP.
Print Assumptions ddg_plane_estimate.
Print Assumptions ddg_lemma_A_1.
Print Assumptions ddg_lemma_A_1_moving_plane.
Print Assumptions ddg_tangent_direction_tangent.
Print Assumptions ddg_grassmann_tangent.
Print Assumptions ddg_tangent_cone_linear.
Print Assumptions ddg_B_unique.
Print Assumptions ddg_relative_differentiable.
Print Assumptions ddg_B_spec.
Print Assumptions ddg_B_characterisation.
Print Assumptions ddg_B_formula.
Print Assumptions ddg_B_class_one.
Print Assumptions ddg_jacobian_projection.
Print Assumptions ddg_jacobian_derivative.
Print Assumptions ddg_weighted_jacobian_derivative.
Print Assumptions ddg_B_derivative.
Print Assumptions ddg_flow_class_one.
Print Assumptions ddg_flow_injective.
Print Assumptions ddg_flow_differential_injective.
Print Assumptions ddg_flow_proper.
Print Assumptions ddg_flow_immersion.
Print Assumptions ddg_jacobian_estimate.
Print Assumptions ddg_weighted_jacobian_estimate.
Print Assumptions ddg_lemma_A_2_constant_lipschitz.
Print Assumptions ddg_lemma_A_2_constant.
Print Assumptions ddg_integral_derivative.
Print Assumptions ddg_frozen_class_one.
Print Assumptions ddg_point_flow_integrand_derivative.
Print Assumptions ddg_lemma_A_2.
Print Assumptions ddg_lemma_A_2_image.
