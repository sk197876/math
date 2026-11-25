(** Federer (1969), 4.1.19, p. 377: the
    L1 representation step uses the scalar Radon
    conclusion of 2.5.10, p. 101, with
    the original bound unchanged. The Radon measure
    need not have finite total mass. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP RadonMeasureUP
  FunctionLatticeSeminormUP TotalScalarLpUP TotalScalarLpFiniteSeminorm
  RealLatticeDensityUP RadonFiniteDecomposition FiniteDecompositionRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [radon_bounded_lone_density]: apply
    the Radon decomposition in 2.5.10, p. 101,
    to the bounded L1 functional used by
    Federer 4.1.19, p. 377. The selected
    density satisfies the actual pointwise bound c;
    no countable support or finite total measure
    is added to the original hypotheses. *)
Theorem radon_bounded_lone_density (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) (A : (X -> R) -> R) (c : R) :
  0 <= c ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  (forall f, total_scalar_lp mu 1 f ->
    `|A f| <= c*finite_total_scalar_lp_norm mu 1 f) ->
  exists k : X -> R,
    is_real_lattice_density mu (total_scalar_lp mu 1) A k /\
    forall x, `|k x| <= c.
Proof.
move=> hC hLinear hBound.
have [G [hCompact hDecomposition]] :=
  @radon_measure_finite_decomposition R X mu hm hr.
exact: (@bounded_lone_density_from_finite_decomposition R X
  [the choiceType of set X] mu hm G (fun K => K) A c
  hDecomposition hC hLinear hBound).
Qed.
