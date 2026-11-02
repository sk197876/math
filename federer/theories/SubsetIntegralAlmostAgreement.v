(** Federer (1969), 3.2.32, pp. 269–270: supporting
    null changes of subset integrands in the countable coarea
    argument. This follows the conventions of 2.3.1 and 2.4.10. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_integral_almost_agreement]: supporting the
    preservation of the original approximate Jacobian in Federer
    3.2.32, pp. 269–270. Common defined values almost
    everywhere on A suffice to transfer its actual subset integral.
    No total completion of either original partial graph is required. *)
Lemma subset_integral_almost_agreement (R:realType) (X:choiceType)
    (rho:set X->\bar R) (hr:is_measure rho) (A:set X)
    (f g:partial_function X (extended_real_line R)) a:
  measure_almost_everywhere_on rho A (partial_function_agreement f g) ->
  is_measure_subset_integral rho A f a ->is_measure_subset_integral rho A g a.
Proof.
move=>hAgree hI.
apply:(measure_integral_almost_equal hr hI).
apply:(measure_almost_everywhere_mono hr _
  ((measure_almost_everywhere_on_implication _ _ _).1 hAgree))=>x hx.
have [hAx|hAx]:=pselect (A x).
- have [z [hf hg]]:=hx hAx; exists z; split;
    apply/partial_function_zero_extension_graph; left; by split.
- exists 0; split; apply/partial_function_zero_extension_graph; right; by split.
Qed.
