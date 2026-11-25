(** Federer (1969), 2.5.10, pp. 100–101: under CH the density representation
    holds for Borel regular measures over separable metric spaces. The
    conclusion permits a density without countably measurable support. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP ContinuumHypothesisUP ContinuumBorelDecomposition
  FunctionLatticeSeminormUP FunctionOperatorSeminorm TotalScalarLpUP TotalScalarLpFiniteSeminorm
  RealLatticeDensityUP FiniteDecompositionRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [continuum_borel_lone_functional_representation]:
    the conditional affirmative answer in Federer 2.5.10,
    pp. 100–101. CH and separability are explicit hypotheses;
    the conclusion is an actual measurable density representing
    every total real L1 function by its finite integral. *)
Theorem continuum_borel_lone_functional_representation (R : realType) (T : metricType R)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_borel_regular_measure mu)
    (A : (T -> R) -> R) :
  continuum_hypothesis -> (exists S : set T, countable S /\ dense S) ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  function_operator_seminorm (total_scalar_lp mu 1) A
    (finite_total_scalar_lp_norm mu 1) < +oo ->
  exists k : T -> R, is_real_lattice_density mu (total_scalar_lp mu 1) A k.
Proof.
move=> hCH hsep hA hb.
have [C [B hCB]] := continuum_borel_regular_finite_decomposition hm hr hCH hsep.
have [k [hk hnorm]] := @lone_functional_representation_by_finite_decomposition R T
  [the choiceType of set nat] mu hm C B A hCB hA hb.
by exists k.
Qed.
