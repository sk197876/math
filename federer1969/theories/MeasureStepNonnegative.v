(** Federer (1969), 2.4.3(3), p. 82: an upper step function for an
    almost-everywhere nonnegative function has a nonnegative assigned sum.
    Source context: PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureStepFunctionUP NonnegativeSum NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_real_nonnegative_locus]: supporting
    nonnegativity locus of a step function in Federer 2.4.3(3),
    p. 82; undefined values do not satisfy the assertion. *)
Definition partial_real_nonnegative_locus (R : realType) (X : Type)
    (u : partial_function X (real_line_metric R)) :=
  [set x | exists y, partial_function_graph u x y /\ (0 <= y)%R].

(** Source for [measure_step_nonnegative_coefficients]: negative
    level sets are null when u>=0 almost everywhere, supporting
    the weighted-sum argument in Federer 2.4.3(3), p. 82. *)
Lemma measure_step_nonnegative_coefficients (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) :
  measure_almost_everywhere mu (partial_real_nonnegative_locus u) -> forall y : R,
    0 <= y%:E*mu (partial_function_preimage u [set y]).
Proof.
move=> hu y; have [hy|hy] := leP 0%R y.
- apply: mule_ge0; first by rewrite lee_fin.
  exact: measure_nonnegative.
- have hz : mu (partial_function_preimage u [set y]) = 0.
    apply: (@measure_null_subset R X mu hm _ (~` partial_real_nonnegative_locus u) _ hu).
    move=> x [a [ha ea]] [b [hb hpos]].
    have hab := partial_function_single_valued ha hb.
    have hpos' : (0 <= y)%R by rewrite -ea hab.
    by move: hy; rewrite ltNge hpos'.
  by rewrite hz mule0.
Qed.

(** Source for [measure_step_integral_nonnegative]: supporting nonnegativity
    of the assigned sum in Federer 2.4.3(3), p. 82 *)
Lemma measure_step_integral_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) a :
  measure_almost_everywhere mu (partial_real_nonnegative_locus u) ->
  is_measure_step_integral mu u a -> 0 <= a.
Proof.
move=> hu ha.
have hp y : (@setT R) y -> 0 <= y%:E*mu (partial_function_preimage u [set y]).
  move=> _; exact (@measure_step_nonnegative_coefficients R X mu hm u hu y).
rewrite /is_measure_step_integral (numerical_sum_nonnegative hp) in ha.
case: ha=> <-; exact: nonnegative_sum_nonnegative.
Qed.
