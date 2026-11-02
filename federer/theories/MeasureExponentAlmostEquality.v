(** Federer (1969), 2.4.17, p. 90, with the conull partial-domain convention
    of 2.3.2, p. 73. These supporting transfer laws permit total
    representatives without changing norms or admissible exponents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasureAlmostUP MeasurableFunctionUP
  MeasureLpNormAlmostEquality MeasureEssentialNormComparison MeasureExponentDomain MeasureReciprocalInterval ReciprocalExponent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_exponent_norm_almost_equal]: supporting
    null-modification invariance of the norm family in Federer
    2.4.17, p. 90, using 2.4.12, p. 86.
    Both finite and infinite exponents retain partial domains. *)
Lemma measure_exponent_norm_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_almost_equal mu f g -> forall p, 1 <= p ->
  measure_exponent_norm mu f p=measure_exponent_norm mu g p.
Proof.
move=> hf hg he [p| |] hp /=.
- exact: (@measure_lp_norm_almost_equal R X R^o _ (scalar_absolute_value_norm R) mu hm p f g hp hf hg he).
- exact: (@measure_essential_norm_almost_equal R X _ mu hm _ f g he).
- by [].
Qed.

(** Source for [finite_norm_exponents_almost_equal]: supporting
    preservation of P in Federer 2.4.17, p. 90,
    under the total-extension reduction of 2.3.2, p. 73. *)
Lemma finite_norm_exponents_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_almost_equal mu f g ->
  measure_finite_norm_exponents mu f=measure_finite_norm_exponents mu g.
Proof.
move=> hf hg he; apply/seteqP; split=> p [hp hfin]; split=> //.
- by rewrite -(measure_exponent_norm_almost_equal hm hf hg he hp).
- by rewrite (measure_exponent_norm_almost_equal hm hf hg he hp).
Qed.

(** Source for [reciprocal_norm_exponents_almost_equal]: supporting
    preservation of U in Federer 2.4.17, p. 90,
    including its reciprocal zero convention. *)
Lemma reciprocal_norm_exponents_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_almost_equal mu f g ->
  measure_positive_reciprocal_exponents mu f=measure_positive_reciprocal_exponents mu g.
Proof.
move=> hf hg he; apply/seteqP; split=> u [hu0 [hu1 [hpos hfin]]]; split=> //; split=> //.
- have hd := @reciprocal_lebesgue_exponent_domain R u hu0 hu1.
  have hn := @measure_exponent_norm_almost_equal R X mu hm f g hf hg he _ hd.
  rewrite !measure_reciprocal_exponent_normE in hpos hfin *.
  by rewrite -hn.
- have hd := @reciprocal_lebesgue_exponent_domain R u hu0 hu1.
  have hn := @measure_exponent_norm_almost_equal R X mu hm f g hf hg he _ hd.
  rewrite !measure_reciprocal_exponent_normE in hpos hfin *.
  by rewrite hn.
Qed.
