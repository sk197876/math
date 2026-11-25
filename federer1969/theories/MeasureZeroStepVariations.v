(** Federer (1969), 2.4.10, p. 85: supporting restriction of upper/lower
    step functions to measurable pieces. The two numerical variations of a
    restricted step function are bounded by the original variations, so
    definedness is preserved. This supplies an expanded argument for the
    splitting exercise. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureBasic MeasureStepFunctionUP ExtendedRealPartial ExtendedRealPartsScale NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_extension_nonzero_fibre]: supporting
    nonzero-level identity for the step sums used in Federer
    2.4.10, p. 85. The extra complement contributes
    only to the zero fibre, whose weight is zero. *)
Lemma zero_extension_nonzero_fibre (X Y : Type) (zero y : Y)
    (A : set X) (f : partial_function X Y) :
  y <> zero -> partial_function_preimage (partial_function_zero_extension zero A f) [set y] =
    A `&` partial_function_preimage f [set y].
Proof.
move=> hy; rewrite partial_zero_extension_preimage.
apply/seteqP; split=> x; last by move=> hx; left.
move=> [hx|[_ hz]]=> //; by exfalso; apply: hy; symmetry.
Qed.

(** Source for [zero_step_coefficient_variation_bounds]: supporting
    coefficient comparison for restriction of a step function
    in Federer 2.4.10, p. 85. Both infinite
    fibre measures and the zero level are included. *)
Lemma zero_step_coefficient_variation_bounds (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (u : partial_function X (real_line_metric R)) (y : R) :
  let v := partial_function_zero_extension (0%R : real_line_metric R) A u in
  extended_positive_part (y%:E*mu (partial_function_preimage v [set y])) <=
    extended_positive_part (y%:E*mu (partial_function_preimage u [set y])) /\
  extended_negative_part (y%:E*mu (partial_function_preimage v [set y])) <=
    extended_negative_part (y%:E*mu (partial_function_preimage u [set y])).
Proof.
move=> v; have [hy|hy] := eqVneq y 0%R.
- by rewrite hy !mul0e; split.
- have hy' : y <> 0%R by move=> he; move: hy; rewrite he eqxx.
  have hv : partial_function_preimage v [set y] = A `&` partial_function_preimage u [set y].
    exact: zero_extension_nonzero_fibre hy'.
  have hb : mu (partial_function_preimage v [set y]) <= mu (partial_function_preimage u [set y]).
    rewrite hv; apply: (@measure_mono R X mu hm)=> x [_ hx]; exact hx.
  split.
  + rewrite !extended_positive_nonnegative_product ?measure_nonnegative //.
    have hp : (0 : \bar R) <= (Num.max y 0)%:E by rewrite lee_fin le_max lexx orbT.
    exact (@lee_wpmul2l R _ hp _ _ hb).
  + rewrite !extended_negative_nonnegative_product ?measure_nonnegative //.
    have hp : (0 : \bar R) <= (Num.max (-y) 0)%:E by rewrite lee_fin le_max lexx orbT.
    exact (@lee_wpmul2l R _ hp _ _ hb).
Qed.

(** Source for [zero_step_variation_bounds]: supporting comparison
    of the two full variations when restricting a step function
    in Federer 2.4.10, p. 85; numerical sum laws
    from 2.1.1(8), p. 53. *)
Lemma zero_step_variation_bounds (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (u : partial_function X (real_line_metric R)) :
  let v := partial_function_zero_extension (0%R : real_line_metric R) A u in
  nonnegative_sum setT (fun y : R => extended_positive_part (y%:E*mu (partial_function_preimage v [set y]))) <=
    nonnegative_sum setT (fun y : R => extended_positive_part (y%:E*mu (partial_function_preimage u [set y]))) /\
  nonnegative_sum setT (fun y : R => extended_negative_part (y%:E*mu (partial_function_preimage v [set y]))) <=
    nonnegative_sum setT (fun y : R => extended_negative_part (y%:E*mu (partial_function_preimage u [set y]))).
Proof.
move=> v; split; apply: nonnegative_sum_mono=> y _.
- exact (@zero_step_coefficient_variation_bounds R X mu hm A u y).1.
- exact (@zero_step_coefficient_variation_bounds R X mu hm A u y).2.
Qed.
