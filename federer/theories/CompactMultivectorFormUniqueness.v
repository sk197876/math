(** Federer (1969), 4.1.19, p. 377:
    almost uniqueness is tested on every
    original compactly supported L1 multivector
    field. Reuse scalar Radon uniqueness and
    the actual mass/comass coefficient dual. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingPairing CurrentDomain CurrentCoefficientNorms
  CurrentVectorSpaces CurrentVectorCompleteness CurrentCovectorDual
  MeasureUP MeasureAlmostUP RadonMeasureUP PartialFunctionBasic
  MeasurableNormedFunctionUP MeasureIntegralUP SummableRealFunctionUP
  EuclideanOpenDomainMeasure CurrentDomainRadonSigmaFinite
  CompactSummableMultivectors CompactSummableDualDensityUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FormUniqueness.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation V := (exterior_power X m).
Local Notation Y := (A_m X R^o m).
Local Notation MN := (@current_vector_mass R h2 n m).
Local Notation hMN := (@current_vector_mass_real_norm R h2 n m).
Local Notation YN := (@current_form_comass R h2 n m).
Local Notation hYN := (@current_form_comass_real_norm R h2 n m).
Local Notation O := (@compact_summable_multivector_space R h2 n m U hU).
Local Notation value := (@compact_summable_multivector_value R h2 n m U hU).

(** Source for [compact_multivector_form_density_almost_unique]:
    the original Omega_m actions determine the
    measurable m-form almost everywhere, supporting
    Federer 4.1.19, p. 377.
    The original open U, all natural
    degrees and arbitrary total measure are retained. *)
Theorem compact_multivector_form_density_almost_unique
    (phi psi : UT -> Y) :
  is_measurable_normed_function mu
    (partial_function_total (fun x => (phi x : real_norm_metric_space hYN))) ->
  is_measurable_normed_function mu
    (partial_function_total (fun x => (psi x : real_norm_metric_space hYN))) ->
  (forall xi : O, exists r : R,
    is_measure_integral mu
      (real_total_integrand (fun x => pairing (value xi x) (phi x))) r%:E /\
    is_measure_integral mu
      (real_total_integrand (fun x => pairing (value xi x) (psi x))) r%:E) ->
  measure_almost_everywhere mu [set x | phi x=psi x].
Proof.
move=> hPhi hPsi hAction.
have hMeasure := @euclidean_open_domain_measure_laws R n U hU.
have hCountable := @current_domain_radon_countably_measurable R n U hU
  mu hMu hMeasure.2.
have [d [e he]] := @current_vector_finite_basis R h2 n m.
exact: (@compact_summable_dual_density_almost_unique R UT V Y MN hMN
  (@current_multivector_mass_separable R h2 n m)
  (@current_covector_evaluation R n m) YN hYN
  (@current_covector_continuous_dual R h2 n m) d e he mu hMu hMeasure.2
  hCountable phi psi hPhi hPsi hAction).
Qed.
End FormUniqueness.
