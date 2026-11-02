(** Federer (1969), 2.5.14, p. 108: private choice of the normalized
    representative in the Radon vector theorem. The initial density has unit
    dual norm locally almost everywhere. In a nonzero space replace all
    other values by one fixed unit dual functional; local measurable
    modification preserves the representation. Zero-dimensional spaces are
    handled separately in the assembly theorem. Source context:
    RadonDualLocalModification.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP RealMetricBackground PartialFunctionBasic FunctionLatticeUP CompactSupportFunctionUP
  VectorDaniellHypotheses VectorDaniellRepresentationUP VectorDaniellNormalisationUP
  MeasureUP RadonMeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableTotalBasic
  MeasureStepIntegralIdentification TotalScalarMeasurability SummableRealFunctionUP LocallyNullMeasureUP LocallyAlmostMeasureLaws
  RadonDualLocalModification DualUnitSphereWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_dual_normalization_exists]: supporting
    representative selection for the conclusion retained from
    Federer 2.5.12, p. 103, by 2.5.14, p. 108.
    The result strengthens almost unit norm to everywhere unit
    norm when E is nonzero; it does not claim that locally
    null sets are globally null. *)
Theorem radon_dual_normalization_exists (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (k : X -> weak_dual_space hN) :
  (exists y : E, y<>0) ->
  is_vector_daniell_density mu Q T k ->
  measure_locally_almost_everywhere mu [set x | dual_norm N (val (k x))= 1] ->
  exists l : X -> weak_dual_space hN, is_normalised_vector_daniell_density mu Q T l.
Proof.
move=> hE hk hn.
have [alpha halpha] := nontrivial_dual_unit_sphere_inhabited hN hE.
pose l x := if dual_norm N (val (k x)) == 1 then k x else alpha.
have hl1 x : dual_norm N (val (l x))= 1.
  rewrite /l; case: ifP=> [/eqP h|_]; by [].
have he : measure_locally_almost_everywhere mu [set x | k x=l x].
  apply: (measure_locally_almost_mono hm _ hn)=> x hx.
  change (k x=l x); by rewrite /l hx eqxx.
exists l; constructor.
- exact (@radon_dual_locally_equal_representation R X E N hN mu hm hr Q T hM k l he hk).
- have heq : (fun x => dual_norm N (val (l x)))=(fun _ : X => (1 : R)).
    by apply: funext=> x; exact: hl1.
  rewrite heq; apply: (@measurable_partial_real_embedding R X mu hm
    (partial_function_total (fun _ : X => (1 : real_line_metric R)))).
  exact (@measurable_total_constant R X [the topologicalType of real_line_metric R] mu hm 1).
- apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm)).
  by move=> x _; exact: hl1.
- by move=> x; rewrite hl1.
Qed.
