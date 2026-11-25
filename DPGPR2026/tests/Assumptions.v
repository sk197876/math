(** Axiom audit of the DPGPR subproject: De Philippis, Gennaioli, Pigati
    and Rindler (2026). The only axioms allowed are
    boolp.propositional_extensionality, boolp.functional_extensionality_dep
    and boolp.constructive_indefinite_description. Each worker appends a
    block for its items. *)

(** Blueprint section 3: def:classes, lem:classes, lem:ibp. *)
From DPGPR Require Import DgprGrowthClasses DgprClassesProduct DgprLebesgueIntegrals
  DgprDivergenceIntegral DgprClassesTimeDerivative DgprDifferentialCalculus
  DgprIntegrationByParts DgprIntegrationByPartsClasses DgprLipschitzSmoothing
  DgprIntegrationByPartsGeneral.

Print Assumptions dgpr_gaussian_decay_polynomial_growth.
Print Assumptions dgpr_gaussian_decay_before_polynomial_growth_before.
Print Assumptions dgpr_classes_product.
Print Assumptions dgpr_classes_product_polynomial.
Print Assumptions dgpr_classes_product_gaussian.
Print Assumptions dgpr_classes_product_polynomial_before.
Print Assumptions dgpr_classes_product_gaussian_before.
Print Assumptions dgpr_gaussian_weight_summable.
Print Assumptions dgpr_directional_integral.
Print Assumptions dgpr_classes_div.
Print Assumptions dgpr_classes_laplacian.
Print Assumptions dgpr_classes_dt.
Print Assumptions dgpr_values_evaluation.
Print Assumptions dgpr_directional_integral_values.
Print Assumptions dgpr_ibp_smooth.
Print Assumptions dgpr_log_density_fields.
Print Assumptions dgpr_second_order_fields.
Print Assumptions dgpr_ibp_smooth_classes.
Print Assumptions dgpr_lipschitz_differentiable_ae.
Print Assumptions dgpr_smoothing_differential_ae.
Print Assumptions dgpr_almost_dominated_limit.
Print Assumptions dgpr_ibp_fields.
Print Assumptions dgpr_ibp.

(** Blueprint section 2: mr:notation, def:sv, lem:sv, rem:sv_singular,
    def:spectral, lem:spectral, lem:trace, lem:hull, lem:barycentre,
    mr:functionals. *)
From DPGPR Require Import DgprOrthonormalCoordinates DgprHomNorms DgprSingularValueUP
  DgprSingularValue DgprSingularValueRank DgprSpectralCalculusUP DgprSpectralCalculus
  DgprTraceComparison DgprConvexHull DgprBarycentre DgprFunctionals.

Print Assumptions dgpr_rank_one_inner.
Print Assumptions dgpr_hom_norm_adjoint.
Print Assumptions dgpr_hom_norm_comp_left.
Print Assumptions dgpr_hom_norm_comp_right.
Print Assumptions dgpr_sv_characterisation.
Print Assumptions dgpr_sv_hom.
Print Assumptions dgpr_sv_lip.
Print Assumptions dgpr_sv_rank.
Print Assumptions dgpr_sv_eigen.
Print Assumptions dgpr_sv_singular.
Print Assumptions dgpr_spectralP.
Print Assumptions dgpr_spectral_expansion.
Print Assumptions dgpr_spectral_symmetric.
Print Assumptions dgpr_spectral_eigenvalue.
Print Assumptions dgpr_spectral_lipschitz.
Print Assumptions dgpr_spectral_lipschitz_constant.
Print Assumptions dgpr_trace_comparison.
Print Assumptions dgpr_hull_compact.
Print Assumptions dgpr_barycentre.
Print Assumptions dgpr_barycentre_exists.
Print Assumptions dgpr_functional_representation.
Print Assumptions dgpr_variation_vanishes.
Print Assumptions dgpr_variation_null_outside.
Print Assumptions dgpr_functional_null_outside.
Print Assumptions dgpr_variation_dominated.
Print Assumptions dgpr_variation_dominated_integral.

(** Blueprint section 3: differentiation under the integral sign (general),
    def:heat, lem:kernel(1),(2),(3),(5),(6), lem:heat_extension(1) for
    j <= 2, (3), and lem:semiconvex ((3.16)). *)
From DPGPR Require Import DgprParameterIntegralDifferential DgprParameterIntegralSmooth
  DgprHeatKernel DgprHeatKernelDifferential DgprHeatExtension DgprHeatSemiconvex.

Print Assumptions dgpr_parameter_integral_differential.
Print Assumptions dgpr_parameter_integral_class_one.
Print Assumptions dgpr_integral_hom_exists.
Print Assumptions dgpr_parameter_integral_continuous.
Print Assumptions dgpr_parameter_integral_directional.
Print Assumptions dgpr_parameter_integral_partial.
Print Assumptions dgpr_class_successor_coordinate_fields.
Print Assumptions dgpr_parameter_integral_smooth.
Print Assumptions dgpr_gamma_half_sqr.
Print Assumptions dgpr_gaussian_integral.
Print Assumptions dgpr_kernel_mass.
Print Assumptions dgpr_kernel_moment.
Print Assumptions dgpr_kernel_max.
Print Assumptions dgpr_kernel_formulas.
Print Assumptions dgpr_kernel_time_derivative.
Print Assumptions dgpr_kernel_heat.
Print Assumptions dgpr_kernel_differential_bound.
Print Assumptions dgpr_kernel_second_bound.
Print Assumptions dgpr_convolution_differential.
Print Assumptions dgpr_heat_extension_integral.
Print Assumptions dgpr_heat_extension_first.
Print Assumptions dgpr_heat_extension_second.
Print Assumptions dgpr_heat_extension_gauss.
Print Assumptions dgpr_heat_extension_lower.
Print Assumptions dgpr_heat_extension_positive.
Print Assumptions dgpr_semiconvex.

(** Blueprint section 3: lem:heat_extension(1) (class infinity in (s,x),
    also backward in time, and the heat equation), (2) for j <= 2 with the
    blueprint's constants, (3) without integrability hypotheses, (4) for
    Z = R and f >= 0, and lem:kernel(4) for j <= 2 with the blueprint's
    constants. *)
From DPGPR Require Import DgprHeatKernelFamily DgprHeatExtensionSmooth DgprHeatExtensionBounds
  DgprHeatExtensionMass.

Print Assumptions dgpr_kernel_family_bound.
Print Assumptions dgpr_kernel_family_space_derivative.
Print Assumptions dgpr_kernel_family_time_derivative.
Print Assumptions dgpr_kernel_family_joint_class_zero.
Print Assumptions dgpr_heat_extension_class_coordinates.
Print Assumptions dgpr_heat_extension_smooth.
Print Assumptions dgpr_heat_extension_backward_smooth.
Print Assumptions dgpr_heat_extension_time_derivative.
Print Assumptions dgpr_heat_extension_heat.
Print Assumptions dgpr_heat_extension_backward_heat.
Print Assumptions dgpr_kernel_first_scaled_bound.
Print Assumptions dgpr_kernel_second_scaled_bound.
Print Assumptions dgpr_heat_norm_integral.
Print Assumptions dgpr_norm_total_integral.
Print Assumptions dgpr_heat_extension_zero_bound.
Print Assumptions dgpr_heat_extension_gauss_bound.
Print Assumptions dgpr_heat_extension_first_bound.
Print Assumptions dgpr_heat_extension_second_bound.
Print Assumptions dgpr_heat_extension_mass.

(** Blueprint lem:inner, lem:tube and mr:functionals (first consequence
    on R^n). *)
From DPGPR Require Import DgprInnerApproximation DgprFunctionalsEuclidean DgprTubeEstimate.

Print Assumptions dgpr_inner_approximation_measure.
Print Assumptions dgpr_inner_approximation.
Print Assumptions dgpr_full_domain_measure_laws.
Print Assumptions dgpr_dominated_finite_variation.
Print Assumptions dgpr_dominated_variation.
Print Assumptions dgpr_dominated_representation.
Print Assumptions dgpr_tube_minkowski.
Print Assumptions dgpr_layer_gaussian_bound.
Print Assumptions dgpr_tube_summable.
Print Assumptions dgpr_tube_estimate.

(** Blueprint section 3: lem:kernel(4) for every j (with class infinity of
    p_s), and lem:heat_extension(1) and (2) for every j. *)
From DPGPR Require Import DgprHeatKernelHigher DgprHeatExtensionHigher.

Print Assumptions dgpr_kernel_graded_bound.
Print Assumptions dgpr_kernel_graded_space_derivative.
Print Assumptions dgpr_kernel_iterated.
Print Assumptions dgpr_kernel_class_infinity.
Print Assumptions dgpr_kernel_higher_bound.
Print Assumptions dgpr_heat_extension_space_smooth.
Print Assumptions dgpr_heat_extension_iterated.
Print Assumptions dgpr_heat_extension_multi_partial.
Print Assumptions dgpr_heat_extension_higher_bound.

(** Blueprint section 4: mr:standing (S), def:heat_objects,
    lem:identities, lem:heat_calculus and the class-infinity part of
    lem:regularity. *)
From DPGPR Require Import DgprStanding DgprHeatJets DgprBackwardHeat DgprHeatJetCalculus
  DgprHeatTestFunction DgprHeatObjects DgprIdentities DgprHeatCalculus DgprIdentitiesDivergence
  DgprIdentitiesSmooth.

Print Assumptions dgpr_heat_kernel_test.
Print Assumptions dgpr_backward_heat_jet.
Print Assumptions dgpr_backward_heat_operator.
Print Assumptions dgpr_identities_heat_extensions.
Print Assumptions dgpr_identities_mass.
Print Assumptions dgpr_identities_barycentre.
Print Assumptions dgpr_identities_bounds.
Print Assumptions dgpr_identities_sv.
Print Assumptions dgpr_identities_heat.
Print Assumptions dgpr_heat_calculus_S.
Print Assumptions dgpr_heat_calculus_product.
Print Assumptions dgpr_heat_calculus_square.
Print Assumptions dgpr_heat_calculus_chain.
Print Assumptions dgpr_heat_calculus_Bq.
Print Assumptions dgpr_identities_spt.
Print Assumptions dgpr_identities_div.
Print Assumptions dgpr_identities_divB.
Print Assumptions dgpr_logarithm_norm_class.
Print Assumptions dgpr_identities_div_smooth.
Print Assumptions dgpr_regularity_smooth.
Print Assumptions dgpr_regularity_log_smooth.

(** Blueprint section 4, continued: lem:identities(bounds) with rho <= U,
    the joint bounds and the Gaussian decay before T of lem:regularity,
    and the pointwise identities and estimates of the proof of
    lem:DGPR31. *)
From DPGPR Require Import DgprBackwardHeatDecay DgprMeasureComparison DgprLemma31.

Print Assumptions dgpr_backward_heat_joint_bound.
Print Assumptions dgpr_backward_heat_gaussian_decay.
Print Assumptions dgpr_integral_measure_comparison.
Print Assumptions dgpr_identities_rho_le_U.
Print Assumptions dgpr_identities_bounds_full.
Print Assumptions dgpr_regularity_gaussian_extensions.
Print Assumptions dgpr_sum_sqr_le.
Print Assumptions dgpr_lemma31_heat_entropy.
Print Assumptions dgpr_lemma31_heat_B2.
Print Assumptions dgpr_lemma31_grad_log_rho.
Print Assumptions dgpr_lemma31_B_zeta_bound.
Print Assumptions dgpr_lemma31_B_gradient_bound.
Print Assumptions dgpr_lemma31_eta_pointwise.

(** Blueprint section 4, lem:DGPR31: the time derivative of ∫ f_t for
    f of Gaussian decay before T, the estimates at a fixed time, the real
    analysis on [0,T), and Lemma 3.1 under the hypotheses of Gaussian
    decay of rho log q and rho |B|^2. *)
From DPGPR Require Import DgprHeatIntegral DgprLemma31Main DgprTimeIntegrals DgprEntropyBound
  DgprLemma31Final.

Print Assumptions dgpr_slice_gaussian.
Print Assumptions dgpr_heat_integral.
Print Assumptions dgpr_lemma31_DB_bound.
Print Assumptions dgpr_lemma31_integrand_bound.
Print Assumptions dgpr_lemma31_time_slice.
Print Assumptions dgpr_lemma31_K_bound.
Print Assumptions dgpr_before_ftc.
Print Assumptions dgpr_before_upper_integral.
Print Assumptions dgpr_time_min_integral.
Print Assumptions dgpr_entropy_jensen.
Print Assumptions dgpr_lemma31_entropy_bounds.
Print Assumptions dgpr_lemma31_majorant.
Print Assumptions dgpr_lemma_3_1_conditional.

(** Blueprint section 4, lem:DGPR32: integration of eq:32:I over [0,tau],
    under the hypotheses of dgpr_lemma_3_1_conditional and eq:32:I at a
    fixed time. *)
From DPGPR Require Import DgprLemma32Final.

Print Assumptions dgpr_segment_upper_integral_le.
Print Assumptions dgpr_lemma32_log_bound.
Print Assumptions dgpr_lemma_3_2_conditional.

(** Blueprint lem:regularity and lem:DGPR31: a field DB of space
    differentials of B exists, so the hypothesis hDB is satisfiable. *)
From DPGPR Require Import DgprLemma31Field.

Print Assumptions dgpr_slice_differential.
Print Assumptions dgpr_lemma31_DB_exists.

(** Blueprint lem:regularity: Gaussian decay of S, polynomial growth of
    B, eta, kappa, q and of the logarithms, and Gaussian decay of
    rho log q and rho |B|^2; lem:DGPR31 under (S) alone. *)
From DPGPR Require Import DgprRegularity DgprLemma31Theorem.

Print Assumptions dgpr_regularity_S_gaussian.
Print Assumptions dgpr_regularity_polynomial.
Print Assumptions dgpr_regularity_log_polynomial.
Print Assumptions dgpr_regularity_entropy_gaussian.
Print Assumptions dgpr_regularity_B2_gaussian.
Print Assumptions dgpr_lemma_3_1.

(** Blueprint def:entropy, lem:entropy, lem:upper_entropy,
    lem:lower_entropy, and lem:compact_case for normalised data. *)
From DPGPR Require Import DgprEntropy DgprLowerEntropy DgprUpperEntropy DgprCompactCase.

Print Assumptions dgpr_entropy_derivative.
Print Assumptions dgpr_entropy_initial_bound.
Print Assumptions dgpr_lower_entropy.
Print Assumptions dgpr_upper_entropy_of.
Print Assumptions dgpr_upper_entropy.
Print Assumptions dgpr_upper_entropy_constant_gt0.
Print Assumptions dgpr_upper_entropy_conditional.
Print Assumptions dgpr_standing_restrict.
Print Assumptions dgpr_upper_entropy_property_of.
Print Assumptions dgpr_compact_case_entropy.
Print Assumptions dgpr_compact_case_normalised.
Print Assumptions dgpr_compact_case_standing.

(** Blueprint lem:DGPR32: chi and Q (lem:spectral), eq:32:I at a fixed
    time, the regularity facts at time t, and Lemma 3.2 under (S). *)
From DPGPR Require Import DgprLemma32Spectral DgprLemma32Calculus DgprLemma32Pointwise
  DgprLemma32Theorem.

Print Assumptions dgpr_Q_image.
Print Assumptions dgpr_Q_operator_norm.
Print Assumptions dgpr_Q_hom_norm_lower.
Print Assumptions dgpr_Q_lipschitz.
Print Assumptions dgpr_values_compare.
Print Assumptions dgpr_upper_integral_scale.
Print Assumptions dgpr_lemma32_C1_gt0.
Print Assumptions dgpr_lemma32_fixed_time.
Print Assumptions dgpr_slice_polynomial.
Print Assumptions dgpr_polynomial_local_lipschitz.
Print Assumptions dgpr_lemma32_log_rho_growth.
Print Assumptions dgpr_lemma32_B_lipschitz.
Print Assumptions dgpr_lemma_3_2.

(** Blueprint section on varifolds: mr:hypotheses_main, thm:main
    (interface), def:BF, lem:first_variation, lem:KF and the reduction of
    thm:MS to thm:main. *)
From DPGPR Require Import DgprMainHypotheses DgprAnisotropicIntegrand DgprKF
  DgprVarifoldWeight DgprFirstVariation DgprMichaelSimon.

Print Assumptions dgpr_variation_measure_unique.
Print Assumptions dgpr_B_continuous.
Print Assumptions dgpr_KF_compact_convex.
Print Assumptions dgpr_KF_bounds.
Print Assumptions dgpr_lemma_KF.
Print Assumptions dgpr_test_flow.
Print Assumptions dgpr_first_variation_unique.
Print Assumptions dgpr_first_variation.
Print Assumptions dgpr_MS_HM.
Print Assumptions dgpr_MS_weight_representation.
Print Assumptions dgpr_MS_rectifiable.
Print Assumptions dgpr_MS_reduction.
Print Assumptions dgpr_theorem_1_6_from_main.

(** Blueprint lem:compact_case for the data of mr:hypotheses_main: the
    dual density of mr:functionals, the reduction to (S) and the compact
    case. *)
From DPGPR Require Import DgprDualDensity DgprMainToStanding DgprCompactCaseGeneral.

Print Assumptions dgpr_covector_norm_le.
Print Assumptions dgpr_dual_field_measurable.
Print Assumptions dgpr_dual_density.
Print Assumptions dgpr_measure_scale_radon.
Print Assumptions dgpr_variation_value_scale.
Print Assumptions dgpr_main_measure_open.
Print Assumptions dgpr_main_measure_finite.
Print Assumptions dgpr_main_measure_hausdorff.
Print Assumptions dgpr_main_standing.
Print Assumptions dgpr_compact_case_general.

(** Blueprint thm:main (Theorem 1.1 for rectifiable data) by cut-off
    functions, the first variation δ_F V as a distribution, and thm:MS
    (Theorem 1.6). *)
From DPGPR Require Import DgprMainVariation DgprMainCutoff DgprMainMeasure DgprMainTheorem
  DgprFirstVariationFunctionalUP DgprFirstVariationFunctional DgprTheorem16.

Print Assumptions dgpr_bounded_variation_measure.
Print Assumptions dgpr_test_variation_bound.
Print Assumptions dgpr_main_cutoff.
Print Assumptions dgpr_product_differential.
Print Assumptions dgpr_rank_one_inner_bound.
Print Assumptions dgpr_hom_pairing_measurable.
Print Assumptions dgpr_density_measure_change.
Print Assumptions dgpr_cutoff_bound.
Print Assumptions dgpr_main_from_cutoff_bound.
Print Assumptions dgpr_main_from_compact_case.
Print Assumptions dgpr_theorem_1_1_rectifiable.
Print Assumptions dgpr_first_variation_functional_unique.
Print Assumptions dgpr_first_variation_functional_specification.
Print Assumptions dgpr_first_variation_functional_variation.
Print Assumptions dgpr_first_variation_functional_representation.
Print Assumptions dgpr_theorem_1_6.
