(** Federer (1969), 2.5.12, printed p. 103: the representing dual-valued
    density is almost unique. The proof uses the countable dense rational
    subspace on p. 104, scalar almost uniqueness from 2.5.9, and continuity
    of dual functionals. No unit-norm or common bound is imposed on the
    competing representations. The local erratum has no entry for pp.
    103–106. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic
  TotalScalarMeasurability FunctionLatticeUP FunctionLatticeLaws
  RealIntegralFunctionalUP FunctionLatticeRegularityUP CountablyMeasurableUP
  RealLatticeDensityUP RealLatticeDensityUniqueness VectorDaniellHypotheses
  VectorDaniellDensities VectorDaniellRationalSpan VectorDaniellDualExtension
  VectorDaniellRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weak_dual_measurable_evaluation]: evaluations of
    a weakly measurable dual-valued function are measurable,
    by the topology of Federer 2.5.12(2), pp. 102–103, and
    measurable composition 2.3.2(4), p. 73. *)
Lemma weak_dual_measurable_evaluation (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (k : X -> weak_dual_space hN) (y : E) :
  is_measure_measurable_function phi (partial_function_total k) ->
  is_measure_measurable_function phi
    (partial_function_total (fun x => (val (k x) y : real_line_metric R))).
Proof.
move=> hk.
exact (@measurable_total_borel_postcomposition R X
  [the topologicalType of weak_dual_space hN]
  [the topologicalType of real_line_metric R] phi hphi k
  (fun alpha : weak_dual_space hN => (val alpha y : real_line_metric R)) hk
  (continuous_borel_function (@weak_dual_evaluation_continuous R E N hN y))).
Qed.

(** Source for [vector_daniell_density_component]: scalar
    representation obtained by testing with f times y, as in
    Federer 2.5.12, p. 104. This consequence applies to any
    candidate satisfying the representation specification. *)
Lemma vector_daniell_density_component (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (k : X -> weak_dual_space hN) :
  is_vector_lattice_module hN L Q ->
  is_vector_daniell_density phi Q T k -> forall y,
  is_real_lattice_density phi (positive_function_lattice L)
    (component_integral T y) (fun x => val (k x) y).
Proof.
move=> hM hk y; split.
- exact: (real_total_scalar_measurable hphi
    (weak_dual_measurable_evaluation hphi y (vector_daniell_density_measurable hk))).
- move=> f hf.
  have hi := vector_daniell_density_integral hk
    (vector_lattice_module_product hM y hf.1).
  have he : (fun x => val (k x) (f x *: y)) =
      (fun x => f x * val (k x) y).
    apply: funext=> x.
    exact (@dual_space_scale R E N hN (val (k x)) (f x) y (set_valP (k x))).
  by rewrite he in hi.
Qed.

(** Source for [vector_daniell_density_almost_unique]: direct
    almost-uniqueness assertion of Federer 2.5.12, p. 103.
    Scalar uniqueness on the countable dense set gives one
    common conull set; continuity then gives equality on E.
    No boundedness assumption on either density is added. *)
Theorem vector_daniell_density_almost_unique (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (L : set (X -> R)) (Q : set (X -> E)) (T : (X -> E) -> R)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (D : set E) (hD : is_rational_dense_subspace hN D)
    (k l : X -> weak_dual_space hN) :
  is_function_lattice L -> is_vector_lattice_module hN L Q ->
  is_real_integral_functional phi (positive_function_lattice L)
    (variation_integral N Q T) ->
  is_function_lattice_regular (positive_function_lattice L) phi ->
  measure_countably_measurable phi setT ->
  is_vector_daniell_density phi Q T k ->
  is_vector_daniell_density phi Q T l ->
  measure_almost_everywhere phi [set x | k x=l x].
Proof.
move=> hL hM hrep hreg hX hk hl.
have hy y : D y -> measure_almost_everywhere phi
    [set x | val (k x) y=val (l x) y].
  move=> _; apply: (real_lattice_density_almost_unique
    (positive_function_lattice_laws hL) hphi hrep hreg hX).
  - exact (@vector_daniell_density_component R X E N hN L Q T phi hphi k hM hk y).
  - exact (@vector_daniell_density_component R X E N hN L Q T phi hphi l hM hl y).
have hall := measure_almost_everywhere_countable hphi hD.1 hy.
apply: (measure_almost_everywhere_mono hphi _ hall)=> x hx.
apply: val_inj; apply: (@dual_space_dense_eq R E N hN D (val (k x)) (val (l x)) hD.2.1).
- exact: set_valP (k x).
- exact: set_valP (l x).
- exact: hx.
Qed.
