(** Federer (1969), 2.9.20, pp. 165–166: omit or restore interval endpoints
    in derivative integrals. Supporting null-set replacement is justified by
    2.4.3(2), p. 81, and the subset convention of 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_integral_null_replacement]: supporting endpoint
    replacement for Federer 2.9.20, p. 166 Subsets agreeing outside a null
    set have the same actual integral, including possible infinite values.
    Definedness is obtained from the original integrand's conull
    zero-extended domain; no values are assigned on missing points. *)
Lemma subset_integral_null_replacement (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R))
    (A B N : set X) (z : \bar R) :
  is_measure mu -> mu N=0 -> (forall x, ~N x -> (A x <-> B x)) ->
  is_measure_subset_integral mu A f z -> is_measure_subset_integral mu B f z.
Proof.
move=> hm hN he hI.
have hn : measure_almost_everywhere mu (~` N).
  by rewrite /measure_almost_everywhere setCK.
have hd := measurable_function_domain hI.1.
have hboth := @measure_almost_everywhere_and R X mu hm _ _ hd hn.
apply: (@measure_integral_almost_equal R X mu hm _ _ z hI).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hboth)=> x [[y hy] hxN].
exists y; split=> //.
case: (pselect (A x))=> hxA.
- have hxB := (he x hxN).1 hxA.
  apply/(partial_function_zero_extension_on _ _ _ hxB).
  exact: (partial_function_zero_extension_on _ _ _ hxA).1 hy.
- have hxB : ~B x by move=> hh; apply: hxA; exact: (he x hxN).2 hh.
  have hzero := (partial_function_zero_extension_off _ _ _ hxA).1 hy.
  by apply/(partial_function_zero_extension_off _ _ _ hxB).
Qed.
