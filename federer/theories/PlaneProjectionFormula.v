(** Federer (1969), 2.5.10, p. 101: the complete displayed fibre-sum formula
    and the conditional existence of its H^1 measurable representing density
    under the continuum hypothesis. The density is not required to have
    countably measurable support. Source context and erratum:
    PlaneProjectionMeasure.v, SummableSignedFibreIntegral.v, and
    ContinuumBorelRepresentation.v. The failure of L^2 measurability is
    proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric ExtendedRealOrderTopology
  PartialFunctionBasic MeasureUP BorelRegularMeasureUP TopologicalBorel
  HausdorffLength LebesgueScalarMeasure PlaneProjectionMeasure PlaneProjectionFunctional
  EuclideanPlaneMeasurableImages MappingMultiplicity FiniteCompletedMultiplicityIntegral
  SummableSignedFibreIntegral FibreNumericalIntegrand MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence SummableRealFunctionUP TotalLoneSummability
  TotalScalarLpUP TotalScalarLpFiniteSeminorm FunctionOperatorSeminorm
  ContinuumHypothesisUP ContinuumBorelRepresentation RealLatticeDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section PlaneFormula.
Variable R : realType.
Local Notation X := [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
Local Notation H := (@hausdorff_length R X).
Local Notation psi := (@plane_projection_measure R).

(** Source for [plane_projection_finite_set_integral]:
    the completed finite-set case needed for the formula
    in Federer 2.5.10, p. 101. It extends
    2.10.10, p. 176, through the Borel sandwich
    of 2.2.3, p. 61. *)
Lemma plane_projection_finite_set_integral A :
  measure_measurable H A -> H A < +oo ->
  is_measure_integral (@lebesgue_scalar_measure R) (partial_function_total
    (fun t => (@mapping_multiplicity R X R (@plane_first_projection R) A t : extended_real_line R))) (psi A).
Proof.
exact (@finite_completed_multiplicity_integral R X R (@plane_first_projection R) H psi
  (@lebesgue_scalar_measure R) (@hausdorff_length_is_measure R X)
  (plane_projection_is_measure R) (lebesgue_scalar_is_measure R)
  (@hausdorff_length_borel_regular R X) (@plane_projection_hausdorff_bound R)
  (@plane_projection_multiplicity_integral R) A).
Qed.

(** Source for [plane_projection_functional_fibre_formula]:
    direct displayed formula for mu(f) in Federer
    2.5.10, p. 101. The graph of the inner
    sum is exactly numerical summation over p^{-1}{t};
    its almost-everywhere existence and finite integral
    are included in the conclusion. *)
Theorem plane_projection_functional_fibre_formula f : total_scalar_lp H 1 f ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (fibre_numerical_integrand (@plane_first_projection R) (fun x => (f x)%:E))
    (plane_projection_functional f)%:E.
Proof.
move=> hf.
have [a ha] := @total_lone_summable_real R X H (@hausdorff_length_is_measure R X) f hf.
have hsum : is_measure_summable H (partial_function_total (fun x => ((f x)%:E : extended_real_line R))).
  exists a; apply: (@measure_integral_graph_equivalent R X H _ _ _ _ ha)=> x z.
  exact: real_total_integrand_graph.
have hB S (hS : borel_set S) := @borel_regular_borel_measurable R X psi
  (plane_projection_is_measure R) (plane_projection_borel_regular R) S hS.
have [b [hbi hbf]] := @summable_signed_fibre_integral R X R (@plane_first_projection R)
  H psi (@lebesgue_scalar_measure R) (@hausdorff_length_is_measure R X)
  (plane_projection_is_measure R) (lebesgue_scalar_is_measure R)
  (@hausdorff_length_borel_regular R X) (fun x => ((f x)%:E : extended_real_line R))
  hB (@plane_projection_hausdorff_bound R) plane_projection_finite_set_integral hsum.
have hb' : is_measure_integral psi (real_total_integrand f) b%:E.
  apply: (@measure_integral_graph_equivalent R X psi _ _ _ _ hbi)=> x z.
  symmetry; exact: real_total_integrand_graph.
by rewrite (measure_integral_unique hb' (plane_projection_functional_integral hf)) in hbf.
Qed.

(** Source for [plane_projection_density_under_continuum]:
    application of the CH paragraph of Federer 2.5.10,
    p. 101, to its actual geometric functional.
    CH remains an explicit hypothesis, not a project
    axiom; no countable-support requirement is imposed
    on the resulting H^1 measurable density. *)
Theorem plane_projection_density_under_continuum : continuum_hypothesis ->
  exists k : X -> R, is_real_lattice_density H (total_scalar_lp H 1)
    (@plane_projection_functional R) k.
Proof.
move=> hCH; apply: (@continuum_borel_lone_functional_representation R X H
  (@hausdorff_length_is_measure R X) (@hausdorff_length_borel_regular R X)
  (@plane_projection_functional R) hCH (euclidean_plane_separable R)
  (@plane_projection_functional_linear R)).
apply: le_lt_trans (_ : function_operator_seminorm _ _ _ <= (1%R : R)%:E) (ltry _).
apply: function_operator_seminorm_least_bound; first exact: ler01.
move=> f hf; rewrite mul1r; exact: plane_projection_functional_bound hf.
Qed.
End PlaneFormula.
