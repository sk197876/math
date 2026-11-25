(** Federer (1969), 2.4.3(4), p. 82: an upper integral below positive
    infinity implies the same for the positive part, and implies f<infinity
    almost everywhere. Source context: PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureStepFunctionUP MeasureIntegralUP MeasureIntegralBounds
  MeasureStepPositivePart MeasureFiniteUpperApproximant PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_function_positive_part]: the
    positive part f+ in Federer 2.4.3(4), p. 82;
    its domain equals that of f, including infinite values. *)
Definition partial_extended_function_positive_part (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) :=
  partial_function_postcompose f (fun y => (extended_positive_part y : extended_real_line R)).

(** Source for [positive_part_upper_function]: the positive part
    of an upper step function bounds f+, supporting Federer
    2.4.3(4), p. 82. *)
Lemma positive_part_upper_function (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) u :
  is_measure_upper_function mu f u ->
  is_measure_upper_function mu (partial_extended_function_positive_part f)
    (partial_real_function_positive_part u).
Proof.
move=> [hu hlu]; split.
- exact: (@measure_step_positive_part R X mu hm u hu).1.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlu).
  move=> x [y [z [hy [hz hzy]]]].
  exists (Order.max y 0%R), (extended_positive_part z); split.
  + exists y; by split.
  split; first by exists z; split.
  change (Order.max z 0 <= (Order.max y 0%R)%:E).
  rewrite EFin_max; exact: le_max2 hzy (lexx _).
Qed.

(** Source for [measure_upper_integral_positive_part_finite]:
    the integral conclusion in Federer 2.4.3(4), p. 82.
    The assigned sum of the chosen step function may be negative
    infinity; its positive variation is nevertheless finite. *)
Theorem measure_upper_integral_positive_part_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_upper_integral mu f < +oo ->
  measure_upper_integral mu (partial_extended_function_positive_part f) < +oo.
Proof.
move=> hf; have [u [a [hu [ha hfin]]]] := @measure_finite_upper_approximant R X mu f hf.
have [_ hp] := @measure_step_positive_part R X mu hm u hu.1.
have hb := @measure_upper_integral_bound R X mu (partial_extended_function_positive_part f)
  (partial_real_function_positive_part u) _ (@positive_part_upper_function R X mu hm f u hu) hp.
apply: le_lt_trans hb _; exact: measure_step_positive_part_finite ha hfin.
Qed.

(** Source for [measure_finite_upper_integral_consequences]: complete
    conjunction in Federer 2.4.3(4), p. 82 *)
Theorem measure_finite_upper_integral_consequences (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_upper_integral mu f < +oo ->
  measure_upper_integral mu (partial_extended_function_positive_part f) < +oo /\
  measure_almost_everywhere mu (partial_extended_below_infinity_locus f).
Proof.
move=> hf; split.
- exact: (@measure_upper_integral_positive_part_finite R X mu hm f hf).
- exact: (@finite_upper_integral_below_infinity_almost R X mu hm f hf).
Qed.
