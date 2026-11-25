(** Federer (1969), 3.2.32, pp. 269–270: supporting
    removal of a source part above a null target set when
    its Jacobian vanishes almost everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_integral_zero_remainder]: supporting
    null-target control in Federer 3.2.32, pp. 269–270,
    by 3.2.22 and the subset-integral convention 2.4.10.
    An integral over B is unchanged on A contained in B
    if the integrand vanishes almost everywhere on B minus A.
    Neither A nor its remainder is assumed measurable. *)
Lemma subset_integral_zero_remainder (R:realType) (X:choiceType)
    (rho:set X->\bar R) (hr:is_measure rho) (A B:set X) (u:X->extended_real_line R) a:
  A `<=` B ->measure_almost_everywhere_on rho (B `\` A) [set x|u x=0] ->
  is_measure_subset_integral rho B (partial_function_total u) a ->
  is_measure_subset_integral rho A (partial_function_total u) a.
Proof.
move=>hAB hZero hI; apply:(measure_integral_almost_equal hr hI).
apply:(measure_almost_everywhere_mono hr _
  ((measure_almost_everywhere_on_implication _ _ _).1 hZero))=>x hx.
have [hA|hA]:=pselect (A x).
- exists (u x); split; apply/partial_function_zero_extension_graph; left; split=>//; exact:hAB x hA.
- have [hB|hB]:=pselect (B x).
  + have hUx:u x=0:=hx (conj hB hA).
    exists 0; split; apply/partial_function_zero_extension_graph.
    * left; split=>//; exact hUx.
    * right; by split.
  + exists 0; split; apply/partial_function_zero_extension_graph; right; by split.
Qed.
