(** Federer (1969), 2.4.9, p. 85: supporting replacement on null sets when
    applying Fatou to the dominated differences. Integral invariance follows
    from 2.4.3(2), p. 81, its lower-integral counterpart and the
    null-modification measurability result of 2.3.2, p. 73. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableAlmostModification PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralSqueeze MeasureUpperIntegralMonotone MeasureIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [almost_equal_extended_order]: supporting
    two-sided comparison for null replacements in Federer
    2.4.9, p. 85, using the convention of 2.3.1. *)
Lemma almost_equal_extended_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  measure_almost_equal mu f g ->
  measure_almost_everywhere mu (partial_extended_le_locus f g) /\
  measure_almost_everywhere mu (partial_extended_le_locus g f).
Proof.
move=> he; split;
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x [z [hf hg]];
  exists z,z; by split=> //; split.
Qed.

(** Source for [measure_integral_almost_equal]: supporting
    invariance of integral values under null replacements in
    Federer 2.4.9, p. 85; exact partial domains
    may differ on the exceptional null set. *)
Lemma measure_integral_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) a :
  is_measure_integral mu f a -> measure_almost_equal mu f g -> is_measure_integral mu g a.
Proof.
move=> hf he; have [hfg hgf] := @almost_equal_extended_order R X mu hm f g he.
have eu := @measure_upper_integral_unique R X mu f _ a (measure_upper_integral_specification mu f) hf.2.1.
have el := @measure_lower_integral_unique R X mu f _ a (measure_lower_integral_specification mu f) hf.2.2.
apply: (@measure_integral_squeeze R X mu hm g a).
- exact (@measurable_function_almost_equal R X (extended_real_line R) mu hm f g hf.1 he).
- rewrite -eu; exact (@measure_upper_integral_monotone R X mu hm g f hgf).
- rewrite -el; exact (@measure_lower_integral_monotone R X mu hm f g hfg).
Qed.

(** Source for [measure_summable_almost_equal]: supporting
    invariance of summability under the null replacements used
    in Federer 2.4.9, p. 85. *)
Lemma measure_summable_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  is_measure_summable mu f -> measure_almost_equal mu f g -> is_measure_summable mu g.
Proof.
move=> [a ha] he; exists a; exact (@measure_integral_almost_equal R X mu hm f g a%:E ha he).
Qed.
