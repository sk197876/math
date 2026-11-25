(** Federer (1969), 2.5.12, printed pp. 103–105: every member of Q is
    measurable, and pairing a measurable E-valued map with k preserves
    measurability and preserves summability when its norm is summable. These
    consequences use the abstract dual bounds and the already proved
    measurable scalar components. The local erratum has no entry for pp.
    103–105. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP FunctionLatticeUP RealIntegralFunctionalUP
  FunctionLatticeRegularityUP CountablyMeasurableUP VectorDaniellHypotheses
  VectorDaniellRationalSpan VectorDaniellDualExtension VectorDaniellDualDensity
  VectorDaniellWeakMeasurability VectorDaniellPairingMeasurability
  MeasurableDualPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Conclusions.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable L : set (X -> R).
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
Hypothesis hL : is_function_lattice L.
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi (positive_function_lattice L)
  (variation_integral N Q T).
Hypothesis hreg : is_function_lattice_regular (positive_function_lattice L) phi.
Hypothesis hX : measure_countably_measurable phi setT.
Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable kk : E -> X -> R.
Hypothesis hkk : is_component_density_family N L T phi kk.
Local Notation k := (vector_density N D kk).

(** Source for [vector_member_measurable]: the assertion that
    every member of Q is measurable, Federer 2.5.12, p. 103,
    proved using countably many norming functionals on p. 104.
    This statement supplies the auxiliary norming family and
    enumeration by their proved existence results. *)
Theorem vector_member_measurable (w : X -> E) : Q w ->
  is_measure_measurable_function phi
    (partial_function_total (w : X -> real_norm_metric_space hN)).
Proof.
move=> hw.
have [mu hmu] := norming_family_exists hN.
have [e [he1 he2]] := countable_enumeration hD.1 hD.2.2.1.
exact (@vector_member_measurable_enumerated R X E N hN L Q T hL hM phi hphi hrep D hD mu hmu e he2 w hw).
Qed.

(** Source for [vector_density_pairing_measurable]: the
    measurable-pairing conclusion of Federer 2.5.12, p. 103,
    proved on p. 105. Here eta is total; its pairing is
    considered in the extended-real integral space through
    the ordinary real embedding. *)
Theorem vector_density_pairing_measurable (eta : X -> E) :
  is_measure_measurable_function phi
    (partial_function_total (eta : X -> real_norm_metric_space hN)) ->
  is_measure_measurable_function phi
    (real_total_integrand (fun x => k x (eta x))).
Proof.
move=> heta.
apply: (measurable_unit_dual_pairing hD hphi
  (fun x => vector_density_unit_ball hD kk x) _ heta).
move=> y hy.
exact: (vector_density_component_measurable hL hQ hM hT hphi hrep hreg hX hD hkk hy).
Qed.

(** Source for [vector_density_pairing_summable]: the summability
    conclusion in Federer 2.5.12, p. 103, using the unit dual
    bound from p. 104 and dominated summability 2.4.6, p. 83.
    The result includes the actual finite integral and its
    absolute bound by the integral of the norm. *)
Theorem vector_density_pairing_summable (eta : X -> E) (b : R) :
  is_measure_measurable_function phi
    (partial_function_total (eta : X -> real_norm_metric_space hN)) ->
  is_measure_integral phi (real_total_integrand (fun x => N (eta x))) b%:E ->
  exists c : R,
    is_measure_integral phi (real_total_integrand (fun x => k x (eta x))) c%:E /\
    `|c| <= b.
Proof.
move=> heta hi.
apply: (real_total_dominated_integral hphi
  (vector_density_pairing_measurable heta) hi)=> x.
exact: vector_density_bound hD kk x (eta x).
Qed.
End Conclusions.
