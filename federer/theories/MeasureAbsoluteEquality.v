(** Federer (1969), 2.4.14, p. 88: equality in the estimate of a signed
    integral by the integral of its absolute value. These supporting lemmas
    derive the sign condition from the nonnegative integral deficit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  PartialExtendedOrderLoci PartialAbsolutePartsGraph MeasureIntegralNegation
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralOrderEquality
  MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence MeasureIntegralNegationLaw MeasureSummableFiniteValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [equal_absolute_integral_nonnegative]: supporting
    positive-sign equality case in Federer 2.4.14, p. 88 If f and |f| have
    the same finite integral, f is nonnegative almost everywhere.
    Summability supplies the finite-value region. *)
Lemma equal_absolute_integral_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (c : R) :
  is_measure_integral mu f c%:E ->
  is_measure_integral mu (partial_extended_function_absolute_value f) c%:E ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f).
Proof.
move=> hf habs.
have hs : is_measure_summable mu f by exists c.
have hfin := @measure_summable_finite_almost R X mu hm f hs.
have hord : measure_almost_everywhere mu [set x | exists a b : R,
    partial_function_graph f x a%:E /\ partial_function_graph (partial_extended_function_absolute_value f) x b%:E /\ (a <= b)%R].
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfin).
  move=> x [z [hz hzfin]].
  exists (fine z),`|fine z|%R; split; first by rewrite fineK.
  split; last exact: ler_norm.
  exists z; split=> //; by rewrite -(fineK hzfin) abse_EFin.
have he := @measure_integral_order_equality R X mu hm _ _ c hf habs hord.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [z [hz [w [hw hwz]]]].
have hew : w=z := partial_function_single_valued hw hz.
exists z; split=> //; rewrite -hwz; exact: abse_ge0.
Qed.

(** Source for [nonnegative_absolute_integral_agrees]: supporting
    converse for the positive-sign case in Federer 2.4.14,
    p. 88. Almost-everywhere nonnegativity identifies f
    with |f|, retaining either infinite integral value. *)
Lemma nonnegative_absolute_integral_agrees (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) c :
  is_measure_integral mu f c ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  is_measure_integral mu (partial_extended_function_absolute_value f) c.
Proof.
move=> hf hp; apply: (@measure_integral_almost_equal R X mu hm _ _ c hf).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp).
move=> x [z [hz hz0]]; exists z; split=> //; exists z; split=> //.
exact: gee0_abs hz0.
Qed.

(** Source for [absolute_negation_graph]: supporting invariance of |f| under
    negation for the two sign cases in Federer 2.4.14, p. 88 It holds also
    at infinite values. *)
Lemma absolute_negation_graph (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) x z :
  partial_function_graph (partial_extended_function_absolute_value (partial_extended_function_negate f)) x z <->
  partial_function_graph (partial_extended_function_absolute_value f) x z.
Proof.
split.
- move=> [y [[w [hw hwy]] hyz]]; exists w; split=> //.
  by rewrite -hwy abseN in hyz.
- move=> [w [hw hwz]]; exists (-w); split; last by rewrite abseN.
  exists w; by split.
Qed.

(** Source for [absolute_integral_equality_constant_sign]: the necessary
    constant-sign condition in the proof of Federer 2.4.14, p. 88 The second
    alternative says that -f is nonnegative almost everywhere, equivalently
    f is nonpositive. *)
Lemma absolute_integral_equality_constant_sign (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (c : R) :
  is_measure_integral mu f c%:E ->
  is_measure_integral mu (partial_extended_function_absolute_value f) `|c|%:E ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) \/
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_extended_function_negate f)).
Proof.
move=> hf habs; have [hc|hc] := leP 0%R c.
- left; rewrite (ger0_norm hc) in habs.
  exact (@equal_absolute_integral_nonnegative R X mu hm f c hf habs).
- right; have hn := @measure_integral_negation R X mu hm f c%:E hf.
  have hcn : (c <= 0)%R := ltW hc.
  rewrite (ler0_norm hcn) in habs.
  have habsn : is_measure_integral mu
      (partial_extended_function_absolute_value (partial_extended_function_negate f)) (-c)%:E.
    apply: (@measure_integral_graph_equivalent R X mu _ _ (-c)%:E _ habs)=> x z.
    exact (iff_sym (absolute_negation_graph f x z)).
  exact (@equal_absolute_integral_nonnegative R X mu hm _ (-c)%R hn habsn).
Qed.
