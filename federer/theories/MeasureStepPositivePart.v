(** Federer (1969), 2.4.3(4), p. 82: supporting passage from an upper step
    function to its positive part. The positive part has the positive
    variation as its assigned sum. Source context:
    PartialExtendedOrderLoci.v. Scalar maximum continuity uses the same
    narrow imports as ClosedSetContinuousCutoffs.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureBasic MeasurableFunctionUP MeasurablePostcomposition BorelFunctionBasic
  MeasureStepFunctionUP PartialFunctionRangeOperations ExtendedRealPartial
  ExtendedRealAddVariations NonnegativeSum NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_real_function_positive_part]: supporting
    positive part of an upper step function in Federer 2.4.3(4),
    p. 82, retaining its original partial domain. *)
Definition partial_real_function_positive_part (R : realType) (X : Type)
    (u : partial_function X (real_line_metric R)) :=
  partial_function_postcompose u (fun y => (Order.max y 0%R : real_line_metric R)).

(** Source for [measurable_real_function_positive_part]: supporting
    measurability of the positive-part step approximant in Federer
    2.4.3(4), p. 82. *)
Lemma measurable_real_function_positive_part (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu u ->
  is_measure_measurable_function mu (partial_real_function_positive_part u).
Proof.
move=> hu; apply: (@measurable_function_borel_postcomposition R X _ _ mu hm u _ hu).
apply: continuous_borel_function.
change (continuous (fun y : R^o => Order.max y 0%R)); move=> y.
apply: (@continuous_max R R^o (fun y => y) (fun _ => 0%R) y).
- exact: cvg_id.
- exact: cvg_cst.
Qed.

(** Source for [positive_step_fibre]: supporting positive-level
    fibre identity for the argument in Federer 2.4.3(4), p. 82. *)
Lemma positive_step_fibre (R : realType) (X : Type)
    (u : partial_function X (real_line_metric R)) (y : R) :
  (0 < y)%R -> partial_function_preimage (partial_real_function_positive_part u) [set y] =
    partial_function_preimage u [set y].
Proof.
move=> hy; apply/seteqP; split=> x.
- move=> [z [[w [hw he]] hz]]; exists w; split=> //.
  have he' : Order.max w 0%R = y by rewrite he hz.
  have [hw0|hw0] := leP 0%R w.
  + by rewrite max_l // in he'.
  + rewrite max_r ?ltW // in he'; by move: hy; rewrite -he' ltxx.
- move=> [w [hw he]]; exists y; split=> //; exists w; split=> //.
  by rewrite he max_l // ltW.
Qed.

(** Source for [negative_positive_step_fibre]: negative levels
    of a positive-part step function are empty, supporting Federer
    2.4.3(4), p. 82. *)
Lemma negative_positive_step_fibre (R : realType) (X : Type)
    (u : partial_function X (real_line_metric R)) (y : R) :
  (y < 0)%R -> partial_function_preimage (partial_real_function_positive_part u) [set y] = set0.
Proof.
move=> hy; apply/seteqP; split=> x; last by case.
move=> [z [[w [hw he]] hz]].
have hh : (0 <= y)%R by rewrite -hz -he le_max lexx orbT.
by move: hy; rewrite ltNge hh.
Qed.

(** Source for [positive_step_coefficients]: the level-weighted
    sum of u+ is the positive variation of the sum for u,
    supporting Federer 2.4.3(4), p. 82; the zero level
    contributes zero even when it has infinite measure. *)
Lemma positive_step_coefficients (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) (y : R) :
  y%:E * mu (partial_function_preimage (partial_real_function_positive_part u) [set y]) =
    extended_positive_part (y%:E * mu (partial_function_preimage u [set y])).
Proof.
have hm0 := @measure_nonnegative R X mu hm (partial_function_preimage u [set y]).
have [hy|hy] := ltP 0%R y.
- rewrite positive_step_fibre // /extended_positive_part max_l //.
  apply: mule_ge0=> //; by rewrite lee_fin ltW.
- have [hy0|hy0] := eqVneq y 0%R.
  + by rewrite hy0 /extended_positive_part !mul0e maxxx.
  + have hyn : (y < 0)%R by rewrite lt_neqAle hy0 hy.
    rewrite negative_positive_step_fibre // (measure_empty hm) mule0.
    rewrite /extended_positive_part max_r //.
    apply: mule_le0_ge0=> //; by rewrite lee_fin.
Qed.

(** Source for [measure_step_positive_part]: supporting step
    closure and assigned-sum identity for Federer 2.4.3(4),
    p. 82. No finiteness assumption is needed for closure. *)
Lemma measure_step_positive_part (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) :
  is_measure_step_function mu u ->
  is_measure_step_function mu (partial_real_function_positive_part u) /\
  is_measure_step_integral mu (partial_real_function_positive_part u)
    (nonnegative_sum setT (fun y : R => extended_positive_part
      (y%:E * mu (partial_function_preimage u [set y])))).
Proof.
move=> hu; have ha : is_measure_step_integral mu (partial_real_function_positive_part u)
    (nonnegative_sum setT (fun y : R => extended_positive_part
      (y%:E * mu (partial_function_preimage u [set y])))).
  rewrite /is_measure_step_integral.
  have he : (fun y : R => y%:E * mu (partial_function_preimage (partial_real_function_positive_part u) [set y])) =
      (fun y : R => extended_positive_part (y%:E * mu (partial_function_preimage u [set y]))).
    by apply/funext=> y; exact: positive_step_coefficients.
  rewrite he numerical_sum_nonnegative // => y _.
  exact: extended_positive_part_nonnegative.
split=> //; constructor.
- exact (@measurable_real_function_positive_part R X mu hm u (step_function_measurable hu)).
- apply: partial_postcomposition_range_countable; exact: step_function_countable_range hu.
- eexists; exact ha.
Qed.

(** Source for [measure_step_positive_part_finite]: finiteness
    of the positive variation when the assigned sum is below
    positive infinity, supporting Federer 2.4.3(4), p. 82.
    The original sum may equal negative infinity. *)
Lemma measure_step_positive_part_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (u : partial_function X (real_line_metric R)) a :
  is_measure_step_integral mu u a -> a < +oo ->
  nonnegative_sum setT (fun y : R => extended_positive_part
    (y%:E * mu (partial_function_preimage u [set y]))) < +oo.
Proof.
move=> ha hfin.
have [he _] := nonnegative_difference_finite_sides
  (nonnegative_sum_nonnegative _ _) (nonnegative_sum_nonnegative _ _) ha.
by rewrite he.
Qed.
