(** Federer (1969), 2.5.12, printed p. 103, last two sentences, proved on p.
    105: pairing with k preserves measurability, and summability when the
    norm is summable. This module retains partial measurable domains, using
    the extension convention of 2.3.2, p. 73. Its hypotheses concern only a
    weakly measurable unit-ball-valued k; no implementation of the
    representing density is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition
  PartialFunctionExtensionUP PartialNormPower RealPower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableTotalExtension MeasurableAlmostModification MeasureIntegralUP
  MeasureIntegralAlmostEquality SummableRealFunctionUP VectorDaniellHypotheses
  VectorDaniellRationalSpan VectorDaniellDualExtension VectorDaniellUniqueness
  MeasurableDualPairing VectorDaniellPairingMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_dual_pairing]: the function <eta,k>
    of Federer 2.5.12, p. 103, with exactly the domain
    of eta. Finite real values are embedded into the extended
    line solely for the project's integral interface. *)
Definition partial_dual_pairing (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (k : X -> weak_dual_space hN) (f : partial_function X E) :
    partial_function X (extended_real_line R) :=
  @partial_function_postcompose X (E * weak_dual_space hN) (extended_real_line R)
    (partial_function_pair f (partial_function_total k))
    (fun p => (val p.2 p.1 : R)%:E).

(** Source for [partial_dual_pairing_graph]: graph description
    of the pairing in Federer 2.5.12, p. 103. This
    supporting adapter prevents arbitrary values outside eta's domain. *)
Lemma partial_dual_pairing_graph (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (k : X -> weak_dual_space hN) (f : partial_function X E) x z :
  partial_function_graph (partial_dual_pairing k f) x z <->
    exists y, partial_function_graph f x y /\ (val (k x) y)%:E=z.
Proof.
split.
- move=> [[y a] [[hy ha] he]]; exists y; split=> //.
  by rewrite (ha : k x=a).
- move=> [y [hy he]]; exists (y,k x); by split=> //; split.
Qed.

(** Source for [partial_dual_pairing_measurable_summable]:
    the final measurable-function conclusions of Federer 2.5.12,
    p. 103, including partial domains. The absolute integral
    bound follows from the unit-ball estimate on p. 105.
    The norm integral is written using the first-power adapter
    from 2.4.12, p. 86. *)
Theorem partial_dual_pairing_measurable_summable (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (hsep : is_separable_normed_space hN)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (k : X -> weak_dual_space hN)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_measurable_function phi (partial_function_total k) ->
  (forall x, dual_norm N (val (k x)) <= 1) ->
  is_measure_measurable_function phi f ->
  is_measure_measurable_function phi (partial_dual_pairing k f) /\
  (forall a : R, is_measure_integral phi (partial_norm_power N 1 f) a%:E ->
    exists c : R, is_measure_integral phi (partial_dual_pairing k f) c%:E /\ `|c| <= a).
Proof.
move=> hk hb hf.
have [D hD] := @rational_dense_subspace_exists R E N hN hsep.
have [g [he [ha hg]]] := @measurable_function_total_extension R X
  [the topologicalType of real_norm_metric_space hN] phi hphi f 0 hf.
have hunit x : dual_unit_ball hN (val (k x)) by split; [exact: set_valP (k x)|exact: hb].
have hcomp y : D y -> is_measure_measurable_function phi
    (partial_function_total (fun x => (val (k x) y : real_line_metric R))).
  move=> _; exact (@weak_dual_measurable_evaluation R X E N hN phi hphi k y hk).
have hmg := @measurable_unit_dual_pairing R X E N hN D hD phi hphi
  (fun x => val (k x)) hunit g hcomp hg.
have hpair : measure_almost_equal phi (real_total_integrand (fun x => val (k x) (g x)))
    (partial_dual_pairing k f).
  apply: (measure_almost_everywhere_mono hphi _ (measurable_function_domain hf))=> x [y hy].
  exists (val (k x) y)%:E; split.
  - apply/real_total_integrand_graph; by rewrite (he x y hy).
  - apply/partial_dual_pairing_graph; by exists y.
split.
  exact (@measurable_function_almost_equal R X [the topologicalType of extended_real_line R]
    phi hphi _ _ hmg hpair).
move=> a hi.
have hnorm : measure_almost_equal phi (partial_norm_power N 1 f)
    (real_total_integrand (fun x => N (g x))).
  apply: (measure_almost_everywhere_mono hphi _ (measurable_function_domain hf))=> x [y hy].
  exists (N y)%:E; split.
  - exists y; split=> //; by rewrite real_power_one_exponent ?(real_seminorm_nonnegative hN.1).
  - apply/real_total_integrand_graph; by rewrite (he x y hy).
have hNi := measure_integral_almost_equal hphi hi hnorm.
have hbound x : `|val (k x) (g x)| <= N (g x).
  have /dual_unit_ball_bound [_ hh] := hunit x; exact (hh (g x)).
have [c [hc hcb]] := real_total_dominated_integral hphi hmg hNi hbound.
exists c; split=> //; exact (@measure_integral_almost_equal R X phi hphi _ _ c%:E hc hpair).
Qed.
