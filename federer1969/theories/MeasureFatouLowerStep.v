(** Federer (1969), beginning of the proof of 2.4.6, p. 84: reduce the lower
    integral to positive finite sums over disjoint measurable sets. We use
    the positive variation of the assigned step sum directly, then its
    defining finite-subsum bounds. All test fibres are restricted to a
    common conull set, preserving their measures. Source context:
    ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial
  PartialFunctionUP PartialFunctionLimitExtremaUP MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureStepFunctionUP MeasureStepFibres MeasureIntegralUP NonnegativeSum NumericalSum NumericalSumOrder
  ExtendedLowerLimit FatouNullRestriction MeasureFatouFiniteFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_fatou_lower_step_bound]: supporting upper bound on
    every lower function's assigned sum in Federer 2.4.6, p. 84 *)
Lemma measure_fatou_lower_step_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) (a : nat -> \bar R)
    (u : partial_function X (real_line_metric R)) b :
  is_partial_function_lower_limit f g ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  (forall n, is_measure_integral mu (f n) (a n)) ->
  is_measure_lower_function mu g u -> is_measure_step_integral mu u b ->
  b <= extended_lower_limit a.
Proof.
move=> hg hp hi [hu hug] hb.
pose E := partial_step_lower_locus u g `&` \bigcap_n partial_extended_nonnegative_locus (f n).
have hE : measure_almost_everywhere mu E.
  apply: (@measure_almost_everywhere_and R X mu hm _ _ hug).
  apply: (@measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT _ (countableP _)).
  by move=> n _; exact: hp.
have hEm := @measure_conull_set_measurable R X mu hm E hE.
pose A y := partial_function_preimage u [set y] `&` E.
have hA y : measure_measurable mu (A y).
  exact (@measure_measurable_intersection R X mu hm _ _
    (@measurable_real_fibre R X mu hm u (step_function_measurable hu) y) hEm).
have hAe y : mu (A y) = mu (partial_function_preimage u [set y]).
  exact (@measure_conull_intersection_value R X mu hm E _ hE).
pose c (y : R) := y%:E*mu (partial_function_preimage u [set y]).
pose p (y : R) := extended_positive_part (c y).
have hp0 y : (@setT R) y -> 0 <= p y by move=> _; exact: extended_positive_part_nonnegative.
have hbp : b <= nonnegative_sum setT p.
  apply: (@numerical_sum_values_mono R R setT c p b (nonnegative_sum setT p))=> //.
  - by move=> y _; rewrite /p /extended_positive_part le_max lexx.
  - exact: numerical_sum_nonnegative hp0.
apply: le_trans hbp _; apply: nonnegative_sum_least=> C _.
pose D := [fset y in C | (0 < y)%R].
have hsum : (\sum_(y <- C) p y) = \sum_(y <- D) y%:E*mu (A y).
  rewrite /D -big_fset_condE [in RHS]big_mkcond.
  apply: eq_big_seq=> y hy; have [hy0|hy0] := ltP 0%R y.
  - rewrite hAe /p /c /extended_positive_part max_l //.
    apply: mule_ge0; first by rewrite lee_fin ltW.
    exact: measure_nonnegative.
  - rewrite /p /c /extended_positive_part max_r //.
    apply: mule_le0_ge0; first by rewrite lee_fin.
    exact: measure_nonnegative.
rewrite hsum; apply: (@measure_fatou_finite_family R X R mu hm f g a D A (fun y => y) hg hp hi).
- by move=> y _; exact: hA.
- move=> y z hy hz hne x [[v [hv ev]] _] [[w [hw ew]] _].
  have he := partial_function_single_valued hv hw.
  apply: (negP hne); apply/eqP; by rewrite -ev -ew.
- by move=> y; rewrite /D inE=> /andP[_ hy].
- move=> y hy x [_ [_ hx]] n; have [z [hz _]] := hx n Logic.I; by exists z.
- move=> y hy x [[v [hv ev]] [[w [z [hw [hz hwz]]]] _]].
  have he := partial_function_single_valued hv hw.
  exists z; split=> //; by rewrite -ev he.
Qed.
