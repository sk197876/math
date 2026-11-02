(** Federer (1969), 2.5.10, pp. 100–101: the representation conclusion for
    Radon measures, obtained from the disjoint-decomposition assertion. The
    density need not have countably measurable support. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP RadonMeasureUP FunctionLatticeSeminormUP FunctionOperatorSeminorm
  TotalScalarLpUP TotalScalarLpFiniteSeminorm RealLatticeDensityUP
  FiniteDecompositionRepresentation RadonFiniteDecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [radon_lone_functional_representation]: the Radon case of
    Federer 2.5.10, pp. 100–101 Every bounded linear functional on total
    real L1 functions has an actual measurable integral density. The
    essential bound is inherited from the general decomposition theorem;
    countable support is not imposed. *)
Theorem radon_lone_functional_representation (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (A : (T -> R) -> R) :
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  function_operator_seminorm (total_scalar_lp mu 1) A
    (finite_total_scalar_lp_norm mu 1) < +oo ->
  exists k : T -> R, is_real_lattice_density mu (total_scalar_lp mu 1) A k.
Proof.
move=> hA hb; have [G [hcompact hG]] := radon_measure_finite_decomposition hm hr.
have [k [hk hnorm]] := @lone_functional_representation_by_finite_decomposition R T
  [the choiceType of set T] mu hm G (fun K => K) A hG hA hb.
by exists k.
Qed.
