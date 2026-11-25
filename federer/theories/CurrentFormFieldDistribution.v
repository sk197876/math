(** Federer (1969), 4.1.19, p. 377: locally
    integrable form fields define actual distributions on
    compact smooth multivector tests. This is the
    earlier weak-dual-field construction with the actual
    mass/comass dual identification, not a new dual space. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms CurrentCoefficientNorms CurrentVectorSpaces
  CurrentVectorCompleteness CurrentCovectorDual NormDualLocallyIntegrableField
  ContinuousDualUP WeakEvaluationTopologySealed OpenFamilyTopologyUP NormOpenTopology
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  ContinuousRealDual DistributionIntegralFieldUP DistributionFromDualFieldSealed
  LocallyIntegrableVectorFieldUP EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_form_field_distribution_exists]:
    every locally integrable original coefficient field
    has the actual continuous distribution used in
    the smoothing criterion of Federer 4.1.19,
    p. 377. Its tests are the original
    smooth multivector tests with mass norm. *)
Theorem current_form_field_distribution_exists
    (R : realType) (h2 : (1+1:R)!=0) n d
    (f : R_n R n -> A_m (R_n R n) R^o d) :
  @is_locally_integrable_vector_field R (R_n R n)
    (A_m (R_n R n) R^o d)
    (inner_norm (@euclidean_inner_productP R n))
    (@current_form_comass R h2 n d)
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@current_form_comass_real_norm R h2 n d)
    (@euclidean_lebesgue_measure R n) f ->
  let Full := fun _ : R_n R n => True in
  let hFull := fun (x : R_n R n) (_ : True) =>
    norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x in
  let E := @current_vector_smooth_space R h2 n Full hFull d in
  let ev := @current_vector_smooth_value R h2 n Full hFull d in
  let hE := @current_vector_smooth_space_laws R h2 n Full hFull d in
  let D := @current_vector_smooth_derivatives R h2 n Full hFull d in
  let hD := @current_vector_smooth_derivative_laws R h2 n Full hFull d in
  exists T : Hom (smooth_test_space hE) R^o,
    open_family_continuous (smooth_test_opens hE hD)
      (norm_open_family (@scalar_absolute_value_norm R)) T /\
    is_distribution_integral_action (@euclidean_lebesgue_measure R n)
      (@current_covector_evaluation R n d) f (smooth_test_value hE) T.
Proof.
move=> hField Full hFull E ev hE D hD.
pose X := R_n R n.
pose V := exterior_power X d.
pose VN := @current_vector_mass R h2 n d.
pose hVN := @current_vector_mass_real_norm R h2 n d.
pose Y := A_m X R^o d.
pose NY := @current_form_comass R h2 n d.
pose hNY := @current_form_comass_real_norm R h2 n d.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose ed := @current_covector_evaluation R n d.
pose hDual := @current_covector_continuous_dual R h2 n d.
pose O := WeakEvaluationTopology.opens (fun a y => ed a y).
pose hO := WeakEvaluationTopology.laws (fun a y => ed a y).
have hWeak := @norm_dual_locally_integrable_field R X V Y NX VN NY
  hNX hVN hNY ed hDual O hO (@euclidean_lebesgue_measure R n) f hField.
pose T := @DistributionFromDualField.value R X V NX VN hNX hVN Y ed NY
  hDual (@current_multivector_mass_separable R h2 n d) O hO
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (@euclidean_distribution_measure_open R n) f hWeak E ev hE D hD.
pose SO := smooth_test_opens hE hD.
pose hSO := (smooth_test_final_topology_laws hE hD).1.
pose evaluation := @continuous_real_dual_evaluation R (smooth_test_space hE) SO hSO.
exists (evaluation T); split.
- exact: (@continuous_real_dual_member_continuous R (smooth_test_space hE) SO hSO T).
- exact: (@DistributionFromDualField.laws R X V NX VN hNX hVN Y ed NY
    hDual (@current_multivector_mass_separable R h2 n d) O hO
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (@euclidean_distribution_measure_open R n) f hWeak E ev hE D hD).
Qed.
