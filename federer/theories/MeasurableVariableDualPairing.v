(** Federer (1969), 4.1.1, p. 346: the
    measurable pairing with a locally integrable
    weak dual field follows the countable-dense
    argument of 2.5.12, p. 105. This
    supporting version retains a measurable variable
    bound instead of assuming unit dual norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology normedtype lra.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  NormMetricContinuity MetricPairDistance PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic
  MeasureStepIntegralIdentification TotalScalarMeasurability FunctionLatticeLaws
  SummableRealFunctionUP PartialFunctionSupremumUP MeasurableCountableSupremum
  VectorDaniellHypotheses VectorDaniellRationalSpan VectorDaniellDualExtension MeasurableDualPairing.
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
Variable k : X -> Hom E R^o.
Variable C:X->R.
Hypothesis hC:forall x,0<=C x.
Hypothesis hk:forall x y,`|k x y|<=C x*N y.
Hypothesis hCm:is_measure_measurable_function phi
  (partial_function_total (fun x=>(C x:real_line_metric R))).

(** Source for [variable_dual_pairing_difference_bound]:
    evaluation differences are bounded by the local
    operator bound times the norm difference,
    supporting Federer 4.1.1, p. 346. *)
Lemma variable_dual_pairing_difference_bound x u v:
  `|k x u-k x v|<=C x*N (u-v).
Proof. by rewrite -linearB; exact:hk. Qed.

(** Source for [measurable_variable_dual_pairing]: the
    pairing is measurable under a measurable finite
    pointwise operator bound, supporting Federer
    4.1.1, p. 346, by the original
    countable-dense supremum proof of 2.5.12. *)
Theorem measurable_variable_dual_pairing (eta : X -> E) :
  (forall y, D y -> is_measure_measurable_function phi
    (partial_function_total (fun x => (k x y : real_line_metric R)))) ->
  is_measure_measurable_function phi
    (partial_function_total (eta : X -> real_norm_metric_space hN)) ->
  is_measure_measurable_function phi
    (real_total_integrand (fun x => k x (eta x))).
Proof.
move=> hcomp heta.
apply: (measurable_countable_supremum hphi (D := D)
  (f := fun y => real_total_integrand (fun x => k x y-C x*N (eta x-y)))).
- exact: hD.1.
- move=> y hy.
  have h1 := real_total_scalar_measurable hphi (hcomp y hy).
  have h2 := real_total_scalar_measurable hphi
    (@measurable_norm_distance_from_point R X E N hN phi hphi eta y heta).
  have hMulCont:continuous (fun p:real_line_metric R*real_line_metric R=>(p.1 * p.2:real_line_metric R)).
    change (continuous (fun p:R^o*R^o=>p.1 * p.2)).
    move=>p; exact:(cvgM cvg_fst cvg_snd).
  have hCM:=real_total_scalar_measurable hphi hCm.
  have hCMul:=total_scalar_continuous_binary_operation hphi hMulCont hCM h2.
  have hc : continuous
      (fun p : real_line_metric R * real_line_metric R =>
        (p.1-p.2 : real_line_metric R)).
    change (continuous (fun p : R^o * R^o => p.1-p.2)).
    move=> p; apply: cvgB; [exact: cvg_fst | exact: cvg_snd].
  have h3 := total_scalar_continuous_binary_operation hphi hc h1 hCMul.
  exact: (measurable_partial_real_embedding hphi (total_scalar_real_measurable hphi h3)).
- constructor.
  + apply/seteqP; split=> x _.
    * move=> y _; exists (k x y-C x*N (eta x-y))%:E.
      by apply/real_total_integrand_graph.
    * exists (k x (eta x))%:E; by apply/real_total_integrand_graph.
  + move=> x t ht z [y [hy hz]].
    move/real_total_integrand_graph: ht=> <-.
    move/real_total_integrand_graph: hz=> <-.
    rewrite lee_fin.
    have hh := variable_dual_pairing_difference_bound x (eta x) y.
    move: hh; rewrite ler_norml=> /andP [hlo hhi]; lra.
  + move=> x t ht b hb; move/real_total_integrand_graph: ht=> <-.
    have hzero : ((k x 0-C x*N (eta x-0))%:E <= b)%E.
      apply: hb; exists 0; split; first exact: hD.2.2.1.
      by apply/real_total_integrand_graph.
    case: b hb hzero=> [r| |] hb hzero.
    * rewrite lee_fin; apply: contrapT=> /negP hnot.
      rewrite -ltNge in hnot.
      have hCp:0<C x+1 by have:=hC x; lra.
      have hDen:0<3*(C x+1) by rewrite mulr_gt0 // ltr0n.
      pose gap:=(k x (eta x)-r)/(3*(C x+1)).
      have hgap:0<gap by rewrite /gap divr_gt0 // subr_gt0.
      have hGapEq:gap*(3*(C x+1))=k x (eta x)-r.
        by rewrite /gap divfK // gt_eqF.
      have [y [hy hnear]] := dense_approximation hD.2.1 (eta x) hgap.
      have hyb : ((k x y-C x*N (eta x-y))%:E <= r%:E)%E.
        apply: hb; exists y; split=> //; by apply/real_total_integrand_graph.
      rewrite lee_fin in hyb.
      have hh := variable_dual_pairing_difference_bound x (eta x) y.
      move: hh; rewrite ler_norml=> /andP [hlo hhi].
      have hCx:=hC x.
      clear hb hzero t; nra.
    * exact: leey.
    * by have := lt_le_trans (ltNyr _) hzero; rewrite ltxx.
Qed.
End Pairing.
