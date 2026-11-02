(** Federer (1969), 2.6.4, p. 118: supporting countable measurability for
    the product of two L1 functions. The nonzero locus is exactly the
    rectangle of their nonzero loci; the ambient measures need not be
    sigma-finite. The definition is 2.3.4, p. 76, and rectangular values are
    2.6.2(2), p. 115. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP CountablyMeasurableUP CountablyMeasurableProduct ProductMeasure
  ProductFunctionMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_product_nonzero_rectangle]: supporting
    exact nonzero-locus identity for the function product in
    Federer 2.6.4, p. 118. Total functions and real scalars
    ensure that no undefined value or zero divisor occurs. *)
Lemma scalar_product_nonzero_rectangle (R : realType) (X Y : Type)
    (f : X -> R) (g : Y -> R) :
  partial_function_nonzero_locus 0 (partial_function_total (fun p : X*Y => f p.1*g p.2)) =
  partial_function_nonzero_locus 0 (partial_function_total f) `*`
  partial_function_nonzero_locus 0 (partial_function_total g).
Proof.
rewrite /partial_function_nonzero_locus !partial_function_total_preimage.
apply/seteqP; split; move=> [x y] /=.
- move=> hn; split=> hz; apply: hn; by rewrite hz ?mul0r ?mulr0.
- move=> [hf hg] hz; have /orP[/eqP he|/eqP he] : (f x==0)||(g y==0).
    by rewrite -mulf_eq0 hz eqxx.
  + exact: hf he.
  + exact: hg he.
Qed.

(** Source for [product_countably_measurable_scalar_function]:
    supporting Fubini hypothesis for the L1 product map in
    Federer 2.6.4, p. 118. Only the two nonzero loci
    need countably finite-measure covers. *)
Lemma product_countably_measurable_scalar_function (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (g : Y -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_countably_measure_measurable_function alpha (0 : real_norm_metric_space (scalar_absolute_value_norm R)) (partial_function_total f) ->
  is_countably_measure_measurable_function beta (0 : real_norm_metric_space (scalar_absolute_value_norm R)) (partial_function_total g) ->
  is_countably_measure_measurable_function (product_measure ha hb) (0 : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total (fun p : X*Y =>
      (f p.1*g p.2 : real_norm_metric_space (scalar_absolute_value_norm R)))).
Proof.
move=> hf hg; constructor.
- exact: product_measurable_scalar_function (countably_measurable_function_measurable hf)
    (countably_measurable_function_measurable hg).
- rewrite scalar_product_nonzero_rectangle.
  exact: countably_measurable_product_rectangle
    (countably_measurable_function_locus hf) (countably_measurable_function_locus hg).
Qed.
