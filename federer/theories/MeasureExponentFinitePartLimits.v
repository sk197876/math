(** Federer (1969), 2.4.17, p. 90: limits along the finite part of P at
    every closure point. This theorem assembles those cases in the actual
    extended-real topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureLpNorm
  MeasureExponentDomain FiniteExponentPart ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedRealLimitBounds
  ExtendedOrderLimitTopology MeasureFiniteExponentContinuity MeasureInfinityExponentContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_exponent_finite_part_sequential_limit]: Supporting
    Federer 2.4.17, p. 90.The sequence lies in P intersect R; its limit may
    have infinite norm or be the exponent infinity. *)
Theorem measure_exponent_finite_part_sequential_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_measure_measurable_function mu (partial_function_total f) ->
  forall (u : nat -> extended_real_line R) (q : extended_real_line R),
  (forall n, finite_exponent_part (measure_finite_norm_exponents mu (partial_function_total f)) (u n)) ->
  u @ \oo --> q ->
  (fun n => (measure_exponent_norm mu (partial_function_total f) (u n) : extended_real_line R)) @ \oo -->
    (measure_exponent_norm mu (partial_function_total f) q : extended_real_line R).
Proof.
move=> hf u q hu hl; apply/extended_order_limit_topology_iff.
have hlim := (extended_order_limit_topology_iff u q).1 hl.
pose p n := fine (u n).
have he n : (p n)%:E=u n by rewrite /p fineK //; exact (hu n).2.
have hp n : (1 <= p n)%R.
  have hh := (hu n).1.1; by rewrite -(he n) lee_fin in hh.
have hfin n : measure_lp_norm mu (fun y : R => `|y|%R) (p n) (partial_function_total f) < +oo.
  have hh := (hu n).1.2; by rewrite -(he n) in hh.
have hefun : (fun n => (p n)%:E)=u by apply/funext=> n; exact: he.
have hfn : (fun n => measure_exponent_norm mu (partial_function_total f) (u n))=
    (fun n => measure_lp_norm mu (fun y : R => `|y|%R) (p n) (partial_function_total f)).
  apply/funext=> n; by rewrite -(he n).
rewrite hfn; rewrite -hefun in hlim.
have hq : 1 <= q.
  apply: (@extended_order_limit_lower_bound R _ q 1 hlim)=> n; exact: hp.
clear hl; case: q hq hlim=> [q| |] hq hlim; last by move: hq; rewrite leNgt ltNyr.
- exact: (@measure_finite_exponent_sequence_continuity R X R^o _ (scalar_absolute_value_norm R) mu hm _ q p hq hp hf hfin hlim).
- exact: (@measure_infinity_exponent_sequence_continuity R X mu hm f p hp hf (hfin 0%N) hlim).
Qed.
