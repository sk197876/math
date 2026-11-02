(** Federer (1969), 2.4.17, p. 90, with the conull partial-domain convention
    of 2.3.2, p. 73. These supporting transfer laws permit total
    representatives without changing norms or admissible exponents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasurableTotalExtension CountableOrderIntervals ExtendedRealOrderTopology MeasureExponentDomain
  MeasureExponentAlmostEquality MeasureExponentContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_partial_exponent_norm_continuous_on_closure]: the
    complete continuity assertion in Federer 2.4.17, p. 90, retaining the
    conull partial domains of 2.3.2, p. 73 The norm family and P are
    unchanged by total extension. *)
Theorem measure_partial_exponent_norm_continuous_on_closure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f ->
  continuous (fun p : subspace (closure
      (measure_finite_norm_exponents mu f : set (extended_real_line R))) =>
    (measure_exponent_norm mu f p : extended_real_line R)).
Proof.
move=> hf; have [g [he [ha hg]]] := @measurable_function_total_extension R X
  (real_norm_metric_space (scalar_absolute_value_norm R)) mu hm f 0%R hf.
have hP := @finite_norm_exponents_almost_equal R X mu hm f _ hf hg ha.
pose P : set (extended_real_line R) := measure_finite_norm_exponents mu f.
have hdom : P `<=` [set p : extended_real_line R | 1 <= p] by move=> p hp; exact hp.1.
have hclosed : closed [set p : extended_real_line R | 1 <= p] :=
  @order_closed_upper_ray_closed _ [the orderTopologicalType _ of order_topology (\bar R)] 1.
have hc p : closure P p -> 1 <= p by move=> hp; exact: (hclosed p (closureS hdom hp)).
have hn p (hp : closure P p) := @measure_exponent_norm_almost_equal R X mu hm f _ hf hg ha p (hc p hp).
have hcont := @measure_exponent_norm_continuous_on_closure R X mu hm g hg.
rewrite -hP in hcont; move/subspace_continuousP: hcont=> hcont.
apply/subspace_continuousP=> x hx B hB.
have hBg : nbhs (measure_exponent_norm mu (partial_function_total g) x : extended_real_line R) B.
  by rewrite -(hn x hx).
have hb := hcont x hx B hBg.
change (nbhs x [set y | closure P y -> B (measure_exponent_norm mu f y)]).
change (nbhs x [set y | closure P y -> B (measure_exponent_norm mu (partial_function_total g) y)]) in hb.
apply: (filterS _ hb)=> y hy hyP; rewrite (hn y hyP); exact: hy hyP.
Qed.
