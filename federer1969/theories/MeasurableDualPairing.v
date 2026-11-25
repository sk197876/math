(** Federer (1969), 2.5.12, printed p. 105, paragraph beginning "Using 2.3.2
    (4), (5)": measurability of the pairing with a measurable map into the
    dual unit ball. The proof below writes the pairing as the supremum of
    its lower Lipschitz cones based on a countable dense set. This is a
    local proof of the same measurable-composition conclusion, using the
    printed estimate, rather than constructing a topology on the dual unit
    ball. The local erratum has no correction to book p. 105. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology normedtype lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  NormMetricContinuity MetricPairDistance PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic
  MeasureStepIntegralIdentification TotalScalarMeasurability FunctionLatticeLaws
  SummableRealFunctionUP PartialFunctionSupremumUP MeasurableCountableSupremum
  VectorDaniellHypotheses VectorDaniellRationalSpan VectorDaniellDualExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Pairing.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Variable k : X -> E -> R.
Hypothesis hk : forall x, dual_unit_ball hN (k x).

(** Source for [unit_dual_pairing_difference_bound]: the estimate
    for the pairing in Federer 2.5.12, p. 105, with the dual
    functional fixed. Supporting lemma; no measurable hypotheses
    or particular construction of the functional are used. *)
Lemma unit_dual_pairing_difference_bound x u v :
  `|k x u-k x v| <= N (u-v).
Proof.
have /dual_unit_ball_bound [hd hb] := hk x.
by rewrite -(dual_space_sub _ _ hd); exact: hb.
Qed.

(** Source for [measurable_norm_distance_from_point]: composition
    with the continuous distance from a fixed point, supporting
    the use of 2.3.2(4) in Federer 2.5.12, p. 105.
    The measurable map is total, with values in the norm topology. *)
Lemma measurable_norm_distance_from_point (eta : X -> E) (p : E) :
  is_measure_measurable_function phi
    (partial_function_total (eta : X -> real_norm_metric_space hN)) ->
  is_measure_measurable_function phi
    (partial_function_total (fun x => (N (eta x-p) : real_line_metric R))).
Proof.
move=> he.
have hc : continuous (fun z : real_norm_metric_space hN =>
    (N (z-p) : real_line_metric R)).
  move=> z U hU.
  have [e hepos hb] := proj1
    (metricType_numDomainType.nbhs_mdistP (N (z-p) : real_line_metric R) U) hU.
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP z _)).
  exists e=> // y hy; apply: hb.
  change (`|N (z-p)-N (y-p)| < e).
  have h := real_norm_change_bound hN (z-p) (y-p).
  rewrite opprB addrA subrK in h.
  exact: le_lt_trans h hy.
exact: (measurable_total_borel_postcomposition hphi he (continuous_borel_function hc)).
Qed.

(** Source for [measurable_unit_dual_pairing]: the measurable
    pairing conclusion of Federer 2.5.12, p. 105. In place of
    separately constructing the product topology on E times U*,
    use the identity
    k(x)(eta(x)) = sup_{y in D} (k(x)(y)-nu(eta(x)-y)).
    Density and the printed norm estimate prove this identity.
    Only the measurable evaluations on D and unit dual bounds
    are required. *)
Theorem measurable_unit_dual_pairing (eta : X -> E) :
  (forall y, D y -> is_measure_measurable_function phi
    (partial_function_total (fun x => (k x y : real_line_metric R)))) ->
  is_measure_measurable_function phi
    (partial_function_total (eta : X -> real_norm_metric_space hN)) ->
  is_measure_measurable_function phi
    (real_total_integrand (fun x => k x (eta x))).
Proof.
move=> hcomp heta.
apply: (measurable_countable_supremum hphi (D := D)
  (f := fun y => real_total_integrand (fun x => k x y-N (eta x-y)))).
- exact: hD.1.
- move=> y hy.
  have h1 := real_total_scalar_measurable hphi (hcomp y hy).
  have h2 := real_total_scalar_measurable hphi
    (measurable_norm_distance_from_point y heta).
  have hc : continuous
      (fun p : real_line_metric R * real_line_metric R =>
        (p.1-p.2 : real_line_metric R)).
    change (continuous (fun p : R^o * R^o => p.1-p.2)).
    move=> p; apply: cvgB; [exact: cvg_fst | exact: cvg_snd].
  have h3 := total_scalar_continuous_binary_operation hphi hc h1 h2.
  exact: (measurable_partial_real_embedding hphi (total_scalar_real_measurable hphi h3)).
- constructor.
  + apply/seteqP; split=> x _.
    * move=> y _; exists (k x y-N (eta x-y))%:E.
      by apply/real_total_integrand_graph.
    * exists (k x (eta x))%:E; by apply/real_total_integrand_graph.
  + move=> x t ht z [y [hy hz]].
    move/real_total_integrand_graph: ht=> <-.
    move/real_total_integrand_graph: hz=> <-.
    rewrite lee_fin.
    have hh := unit_dual_pairing_difference_bound x (eta x) y.
    move: hh; rewrite ler_norml=> /andP [hlo hhi]; lra.
  + move=> x t ht b hb; move/real_total_integrand_graph: ht=> <-.
    have hzero : ((k x 0-N (eta x-0))%:E <= b)%E.
      apply: hb; exists 0; split; first exact: hD.2.2.1.
      by apply/real_total_integrand_graph.
    case: b hb hzero=> [r| |] hb hzero.
    * rewrite lee_fin; apply: contrapT=> /negP hnot.
      have hgap : 0 < (k x (eta x)-r)/3 by rewrite -ltNge in hnot; lra.
      have [y [hy hnear]] := dense_approximation hD.2.1 (eta x) hgap.
      have hyb : ((k x y-N (eta x-y))%:E <= r%:E)%E.
        apply: hb; exists y; split=> //; by apply/real_total_integrand_graph.
      rewrite lee_fin in hyb.
      have hh := unit_dual_pairing_difference_bound x (eta x) y.
      move: hh; rewrite ler_norml=> /andP [hlo hhi].
      rewrite -ltNge in hnot; clear hb hzero t; lra.
    * exact: leey.
    * by have := lt_le_trans (ltNyr _) hzero; rewrite ltxx.
Qed.
End Pairing.
