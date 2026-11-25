(** Supporting replacement on a set, or outside a null exceptional subset,
    for the rational integral evaluations in Federer (1969), 2.6.3(2), pp.
    117–118. The integral convention is 2.4.10, p. 85, and almost equality
    is 2.4.3(2), p. 81. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureSubsetIntegral MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_subset_real_transfer_null]: supporting
    omission of the endpoint zero in the first calculation
    of Federer 2.6.3(2), p. 117, by the
    null-replacement and subset-integral conventions of
    2.4.3(2), p. 81, and 2.4.10, p. 85.
    Both total functions are restricted to the same set. *)
Lemma measure_subset_real_transfer_null (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A N : set X)
    (f g : X -> R) (z : \bar R) :
  mu N=0%E -> (forall x, A x -> ~ N x -> f x=g x) ->
  is_measure_subset_integral mu A (real_total_integrand f) z ->
  is_measure_subset_integral mu A (real_total_integrand g) z.
Proof.
move=> hN he hi; apply: (measure_integral_almost_equal hm hi).
have hcon : measure_almost_everywhere mu (~` N).
  by rewrite /measure_almost_everywhere setCK.
apply: (@measure_almost_everywhere_mono R X mu hm (~` N) _ _ hcon).
move=> x hx; case: (pselect (A x))=> hA.
- exists (f x)%:E; split.
  + by apply/(partial_function_zero_extension_on _ _ _ hA); apply/real_total_integrand_graph.
  + apply/(partial_function_zero_extension_on _ _ _ hA); apply/real_total_integrand_graph.
      by rewrite (he x hA hx).
- exists 0%E; split; by apply/(partial_function_zero_extension_off _ _ _ hA).
Qed.
