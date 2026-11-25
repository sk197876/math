(** Supporting dominated-convergence adapter for Federer (1969), 2.6.3(2),
    p. 118, applying the already proved theorem 2.4.9, p. 85. The integral
    values and the real pointwise limit are retained explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialExtendedOrderLoci PartialAbsolutePartsGraph
  PartialDominatedConvergence SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness MeasureBoundedConvergence
  ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_dominated_integral_limit]: supporting passage from
    finite intervals to the improper integrals in Federer 2.6.3(2), p. 118,
    by 2.4.9, p. 85 A proved summable dominator and a specified scalar limit
    of the integrals imply the actual limit integral. *)
Theorem real_dominated_integral_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> R) (g H : X -> R) (a : nat -> R) (b : R) :
  is_measure_summable mu (real_total_integrand H) ->
  is_measure_measurable_function mu (real_total_integrand g) ->
  (forall n x, `|f n x| <= H x) ->
  (forall x, extended_order_limit (fun n => (f n x)%:E) (g x)%:E) ->
  (forall n, is_measure_integral mu (real_total_integrand (f n)) (a n)%:E) ->
  extended_order_limit (fun n => (a n)%:E) b%:E ->
  is_measure_integral mu (real_total_integrand g) b%:E.
Proof.
move=> hH hg hb hc hi ha.
have hdom n : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (real_total_integrand (f n))) (real_total_integrand H)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (`|f n x|)%:E,(H x)%:E; split.
  - exists (f n x)%:E; split; first exact/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split; first exact/real_total_integrand_graph.
    by rewrite lee_fin; exact: hb.
have hconv : measure_almost_everywhere mu (partial_extended_convergence_locus
    (fun n => real_total_integrand (f n)) (real_total_integrand g)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (fun n => (f n x)%:E),(g x)%:E; split.
  - by move=> n; exact/real_total_integrand_graph.
  - split; first exact/real_total_integrand_graph.
    exact: hc.
have [c [e [d [hci [hgi [_ [_ hlim]]]]]]] := @measure_bounded_convergence R X mu hm
  (fun n => real_total_integrand (f n)) (real_total_integrand g) (real_total_integrand H)
  hH (fun n => (hi n).1) hg hdom hconv.
have he : c=a.
  apply: funext=> n; have hh := measure_integral_unique (hci n) (hi n); by injection hh.
rewrite he in hlim.
have hd := extended_order_limit_unique hlim ha.
by rewrite -hd.
Qed.
