(** Federer (1969), 2.5.12, pp. 104–105: countably many coordinates on a
    dense rational subspace determine measurability of a
    dual-unit-ball-valued map and its dual norm. These supporting
    consequences are stated independently of the component-density
    construction, so that 2.5.14, p. 108, can use the same argument with the
    Radon measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionBasic
  PartialFunctionPreimages MeasureUP MeasureAlmostBasic MeasureCountableClosure MeasurableFunctionUP
  SummableRealFunctionUP MeasurableCountableSupremum PartialFunctionSupremumUP
  MeasureStepIntegralIdentification VectorDaniellHypotheses VectorDaniellRationalSpan
  VectorDaniellDualExtension VectorDaniellWeakMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section BoundedDual.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable k : X -> weak_dual_space hN.
Hypothesis hk : forall x, dual_unit_ball hN (val (k x)).
Hypothesis hc : forall y, D y -> is_measure_measurable_function phi
  (partial_function_total (fun x => (val (k x) y : real_line_metric R))).

(** Source for [bounded_dual_family_norm_measurable]: the
    countable supremum formula in Federer 2.5.12, p. 105,
    supporting the Radon variant 2.5.14, p. 108. Only
    coordinate measurability and the pointwise unit-ball laws
    are required, independently of any particular density witness. *)
Theorem bounded_dual_family_norm_measurable :
  is_measure_measurable_function phi (real_total_integrand (fun x => dual_norm N (val (k x)))).
Proof.
apply: (measurable_countable_supremum hphi (D := D `&` [set y | N y < 1])
  (f := fun y => real_total_integrand (fun x => val (k x) y))).
- exact: (sub_countable (subset_card_le (@subIsetl _ D _)) hD.1).
- move=> y [hy _].
  exact (@measurable_partial_real_embedding R X phi hphi
    (partial_function_total (fun x => (val (k x) y : real_line_metric R))) (@hc y hy)).
- constructor.
  + apply/seteqP; split=> x _.
    * by move=> y _; exists (val (k x) y)%:E; apply/real_total_integrand_graph.
    * by exists (dual_norm N (val (k x)))%:E; apply/real_total_integrand_graph.
  + move=> x t ht z [y [[hy hNy] hz]].
    move/real_total_integrand_graph: ht => <-; move/real_total_integrand_graph: hz => <-.
    rewrite lee_fin (@dual_norm_dense_sup R E N hN D hD _ (hk x)).
    have hyS : [set val (k x) y | y in D `&` [set y | N y < 1]] (val (k x) y) by exists y.
    exact (sup_upper_bound (@dense_unit_values_has_sup R E N hN D hD _ (hk x)) hyS).
  + move=> x t ht b hb; move/real_total_integrand_graph: ht => <-.
    have h0 : ((val (k x) 0)%:E <= b)%E.
      apply: hb; exists 0; split.
      * by split; [exact: hD.2.2.1 | rewrite /= (real_seminorm_zero hN.1) ltr01].
      * by apply/real_total_integrand_graph.
    case: b hb h0 => [r| |] hb h0.
    * rewrite lee_fin (@dual_norm_dense_sup R E N hN D hD _ (hk x)).
      apply: ge_sup (@dense_unit_values_has_sup R E N hN D hD _ (hk x)).1 _ => _ [y hy <-].
      rewrite -lee_fin; apply: hb; exists y; split=> //.
      by apply/real_total_integrand_graph.
    * exact: leey.
    * by have := lt_le_trans (ltNyr (val (k x) 0)) h0; rewrite ltxx.
Qed.

(** Source for [bounded_dual_family_weak_measurable]: the
    countable weak-base argument of Federer 2.5.12, p. 105,
    supporting 2.5.14, p. 108. The map is arbitrary in
    the dual unit ball; no scalar representation or countable
    support assumption is used. *)
Theorem bounded_dual_family_weak_measurable :
  is_measure_measurable_function phi (partial_function_total k).
Proof.
have [e [he1 he2]] := countable_enumeration hD.1 hD.2.2.1.
pose B := @weak_basic R E N hN e.
apply: (measurable_relative_countable_base hphi
  (S := [set beta : weak_dual_space hN | dual_unit_ball hN (val beta)]) (B := B)).
- exact: hk.
- move=> V hV beta hb hVb; exact: (@weak_basic_refines R E N hN D hD e he2 V beta hV hVb hb).
- move=> s.
  have he : k @^-1` B s=\bigcap_(p in [set p | p \in s])
      [set x | ratr p.1.2 < val (k x) (e p.1.1) < ratr p.2].
    by apply/seteqP; split=> x hx p hp; exact: hx p hp.
  rewrite he; apply: (measure_measurable_countable_intersection hphi); first exact: countableP.
  move=> p _; apply: real_interval_preimage_measurable; exact: (@hc _ (he1 _)).
Qed.
End BoundedDual.
