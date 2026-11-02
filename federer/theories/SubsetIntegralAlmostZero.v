(** Federer (1969), 3.2.33, p. 270: an almost
    everywhere zero original subset integrand has integral
    zero, by 2.3.1 and 2.4.10, pp. 72,85. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureSubsetIntegral MeasureConullZeroIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_integral_almost_zero]: the zero
    integral conclusion in the analytic part of Federer
    3.2.33, p. 270. Apply the existing almost-zero
    integral theorem to the actual subset zero extension.
    The source subset need not be measurable or finite;
    the original partial graph need only define zero
    almost everywhere on that subset. *)
Lemma subset_integral_almost_zero (R:realType) (X:choiceType)
    (rho:set X->\bar R) (hRho:is_measure rho) (A:set X)
    (f:partial_function X (extended_real_line R)):
  measure_almost_everywhere_on rho A [set x|partial_function_graph f x 0] ->
  is_measure_subset_integral rho A f 0.
Proof.
move=>hZero; apply:(measure_almost_zero_integral hRho).
apply:(measure_almost_everywhere_mono hRho _
  ((measure_almost_everywhere_on_implication _ _ _).1 hZero))=>x hx.
apply/partial_function_zero_extension_graph.
case:(pselect (A x))=>[ha|hn].
- left; split; first exact ha; exact:hx ha.
- right; by split.
Qed.
