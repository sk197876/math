(** Federer (1969), 2.6.4, p. 118: supporting measurability of
    separated-variable products, from measurable rectangles in 2.6.2(2), p.
    115, and arithmetic in 2.3.2, p. 74. No sigma-finiteness is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureSplit MeasureAlmostBasic MeasurableFunctionUP ProductMeasure ProductRectangleMeasurability
  TotalScalarArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [product_measurable_first_function]: supporting
    pullback by the first projection in Federer 2.6.4, p. 118.
    Its open inverse images are the measurable cylinders of
    2.6.2(2), p. 115. The target may be any topological space. *)
Lemma product_measurable_first_function (R : realType) (X Y : choiceType)
    (Z : topologicalType) (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (f : X -> Z) :
  is_measure_measurable_function alpha (partial_function_total f) ->
  is_measure_measurable_function (product_measure ha hb)
    (partial_function_total (fun p : X*Y => f p.1)).
Proof.
move=> hf; constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true (product_measure_is_measure ha hb).
- move=> W hW; rewrite partial_function_total_preimage.
  have he : (fun p : X*Y => f p.1) @^-1` W = (f @^-1` W) `*` setT.
    apply/seteqP; split=> [p hp|p [hp _]]=> //; by split.
  rewrite he; apply: product_measure_rectangle_measurable; last exact: measure_measurable_whole hb.
  have hh := measurable_function_open_preimage hf hW.
  by rewrite partial_function_total_preimage in hh.
Qed.

(** Source for [product_measurable_second_function]: supporting
    pullback by the second projection in Federer 2.6.4, p. 118,
    from the measurable rectangles of 2.6.2(2), p. 115. *)
Lemma product_measurable_second_function (R : realType) (X Y : choiceType)
    (Z : topologicalType) (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (g : Y -> Z) :
  is_measure_measurable_function beta (partial_function_total g) ->
  is_measure_measurable_function (product_measure ha hb)
    (partial_function_total (fun p : X*Y => g p.2)).
Proof.
move=> hg; constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true (product_measure_is_measure ha hb).
- move=> W hW; rewrite partial_function_total_preimage.
  have he : (fun p : X*Y => g p.2) @^-1` W = setT `*` (g @^-1` W).
    apply/seteqP; split=> [p hp|p [_ hp]]=> //; by split.
  rewrite he; apply: product_measure_rectangle_measurable; first exact: measure_measurable_whole ha.
  have hh := measurable_function_open_preimage hg hW.
  by rewrite partial_function_total_preimage in hh.
Qed.

(** Source for [product_measurable_scalar_function]: supporting
    measurability of h(x,y)=f(x)g(y) in Federer 2.6.4,
    p. 118. This assertion does not require summability. *)
Lemma product_measurable_scalar_function (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (g : Y -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_measure_measurable_function alpha (partial_function_total f) ->
  is_measure_measurable_function beta (partial_function_total g) ->
  is_measure_measurable_function (product_measure ha hb)
    (partial_function_total (fun p : X*Y =>
      (f p.1*g p.2 : real_norm_metric_space (scalar_absolute_value_norm R)))).
Proof.
move=> hf hg; apply: (@measurable_total_scalar_product R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb)
  (fun p => f p.1) (fun p => g p.2)).
- exact (@product_measurable_first_function R X Y _ alpha beta ha hb f hf).
- exact (@product_measurable_second_function R X Y _ alpha beta ha hb g hg).
Qed.
