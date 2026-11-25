(** Federer (1969), 2.9.20, proof of (1)=>(2), p. 166: subtract indefinite
    integrals to obtain the integral on a subinterval. This supporting
    subset law follows the finite difference and subset conventions of 2.4.4
    and 2.4.10, pp. 82–85. No relevant erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  PartialZeroExtension PartialExtendedArithmetic MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureSubsetIntegral MeasureIntegralUP
  MeasureIntegralDifference MeasureIntegralAlmostEquality MeasureSummableFiniteValues
  PartialSimpleIntegralError.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nested_subset_integral_finite_difference]: supporting
    subtraction used in Federer 2.9.20, p. 166, first implication If A is
    contained in B and the two actual subset integrals are finite, the
    integral over B minus A exists and equals their difference. Summability
    supplies a conull finite-value region before pointwise subtraction; no
    infinity-minus-itself convention or total domain is assumed. *)
Theorem nested_subset_integral_finite_difference (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R))
    (A B : set X) (a b : R) :
  is_measure mu -> A `<=` B ->
  is_measure_subset_integral mu A f a%:E ->
  is_measure_subset_integral mu B f b%:E ->
  is_measure_subset_integral mu (B `\` A) f (b-a)%:E.
Proof.
move=> hm hAB hA hB.
pose FA := partial_function_zero_extension (0 : extended_real_line R) A f.
pose FB := partial_function_zero_extension (0 : extended_real_line R) B f.
have hdiff := @measure_integral_finite_difference R X mu hm FB FA b a hB hA.
apply: (@measure_integral_almost_equal R X mu hm _ _ (b-a)%:E hdiff).
have hsum : is_measure_summable mu FB by exists b.
have hf := @measure_summable_finite_almost R X mu hm FB hsum.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hf)=> x [z [hz hfin]].
pose r := fine z.
have hze : z=r%:E by rewrite /r fineK.
rewrite hze in hz.
case: (pselect (A x))=> hAx.
- have hBx := hAB x hAx.
  have hfx := (@partial_function_zero_extension_on X (extended_real_line R) 0 B f x r%:E hBx).1 hz.
  have hAz : partial_function_graph FA x r%:E.
    exact: (@partial_function_zero_extension_on X (extended_real_line R) 0 A f x r%:E hAx).2 hfx.
  have hD := @partial_subtract_finite_graph R X FB FA x r r hz hAz.
  rewrite subrr in hD; exists 0; split=> //.
  apply/(partial_function_zero_extension_off _ _ _); first by move=> [_].
  by [].
- case: (pselect (B x))=> hBx.
  + have hAz : partial_function_graph FA x 0.
      by apply/(partial_function_zero_extension_off _ _ _ hAx).
    have hD := @partial_subtract_finite_graph R X FB FA x r 0 hz hAz.
    rewrite subr0 in hD; exists r%:E; split=> //.
    apply/(partial_function_zero_extension_on _ _ _ (conj hBx hAx)).
    exact: (@partial_function_zero_extension_on X (extended_real_line R) 0 B f x r%:E hBx).1 hz.
  + have hAz : partial_function_graph FA x 0.
      by apply/(partial_function_zero_extension_off _ _ _ hAx).
    have hBz : partial_function_graph FB x 0.
      by apply/(partial_function_zero_extension_off _ _ _ hBx).
    have hD := @partial_subtract_finite_graph R X FB FA x 0 0 hBz hAz.
    rewrite subrr in hD; exists 0; split=> //.
    apply/(partial_function_zero_extension_off _ _ _); first by move=> [].
    by [].
Qed.
