(** Federer (1969), 2.4.3(2), p. 81: on a null
    measured space every partial integrand is almost everywhere zero,
    so its actual integral is zero. Supporting the null-factor
    case of 3.2.48, p. 285, without any assigned fibre values. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureConullZeroIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [null_whole_measure_integral]: the null-space
    instance of integral invariance in 2.4.3(2), p. 81,
    used for zero factors in 3.2.48, p. 285. The original
    partial graph is retained, including an empty domain. *)
Lemma null_whole_measure_integral (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (f:partial_function X (extended_real_line R)):
  mu setT=0%E ->is_measure_integral mu f 0%E.
Proof.
move=>hNull; apply:(measure_almost_zero_integral hm).
exact (measure_null_subset hm (fun x _=>I) hNull).
Qed.
