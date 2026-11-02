(** Federer (1969), 2.4.4(2), p. 82, proof p. 83: every almost-everywhere
    nonnegative measurable function is integrable and its integral is
    nonnegative. Infinite integrals are allowed. The proof splits according
    to whether the positive-infinite level set has positive or zero measure,
    exactly as in the book. the footnote on p. 184 explicitly emphasises
    that the assertion includes integrability. Source context:
    MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralSqueeze MeasureNonnegativeFiniteIntegral
  MeasureInfiniteLevelLowerBound MeasureNonnegativeLowerIntegral MeasureIntegral MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_infinite_level_below_infinity_almost]:
    the transition to the second case in the proof of Federer
    2.4.4(2), p. 83, with the conull original domain retained. *)
Lemma null_infinite_level_below_infinity_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  mu (partial_function_preimage f [set y | y == +oo])=0 ->
  measure_almost_everywhere mu (partial_extended_below_infinity_locus f).
Proof.
move=> hd hz; pose A := partial_function_preimage f [set y | y == +oo].
have hn : measure_almost_everywhere mu (~` A) by rewrite /measure_almost_everywhere setCK.
have hg := @measure_almost_everywhere_and R X mu hm _ _ hd hn.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hg).
move=> x [[z hz'] hnot]; exists z; split=> //.
rewrite lt_neqAle leey andbT; apply/negP=> /eqP he.
apply: hnot; exists z; split=> //; by rewrite he.
Qed.

(** Source for [nonnegative_measurable_function_integral]: complete Federer
    2.4.4(2), p. 82, including the implicit integrability assertion made
    explicit. *)
Theorem nonnegative_measurable_function_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  is_measure_integral mu f (measure_lower_integral mu f) /\ 0 <= measure_lower_integral mu f.
Proof.
move=> hf hp; pose A := partial_function_preimage f [set y | y == +oo].
have [hA|hA] := eqVneq (mu A) 0.
- apply: (@nonnegative_almost_finite_function_integral R X mu hm f hf hp).
  exact (@null_infinite_level_below_infinity_almost R X mu hm f (measurable_function_domain hf) hA).
- have hpos : 0 < mu A by rewrite lt_neqAle eq_sym hA (measure_nonnegative hm).
  have hi := @positive_infinite_level_lower_integral R X mu hm f hf hp hpos.
  split; last by rewrite hi leey.
  apply: (@measure_integral_squeeze R X mu hm f _ hf); last exact: lexx.
  by rewrite hi leey.
Qed.

(** Source for [nonnegative_measurable_function_integrable]:
    explicit integrability consequence of Federer 2.4.4(2),
    p. 82, for use without a preselected integral value. *)
Corollary nonnegative_measurable_function_integrable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> is_measure_integrable mu f.
Proof.
move=> hf hp; exists (measure_lower_integral mu f).
exact (@nonnegative_measurable_function_integral R X mu hm f hf hp).1.
Qed.

(** Source for [nonnegative_integral_value]: the public-value
    form of Federer 2.4.4(2), p. 82; independent of
    the supplied proof of integrability. *)
Corollary nonnegative_integral_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (hf : is_measure_integrable mu f) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> 0 <= measure_integral hf.
Proof.
move=> hp; rewrite measure_integral_lower.
exact (@measure_lower_integral_nonnegative R X mu hm f hp).
Qed.
