(** Federer (1969), 3.2.33, p. 270: finite
    interval integrals defining the primitive g. This helper
    uses the existing measure-integral comparison laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP MeasureSubsetIntegral
  NonnegativeSubsetIntegralComparison MeasureSubsetConstantIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_bounded_nonnegative_subset_integral_finite]:
    supporting the defining integral of g in Federer 3.2.33,
    p. 270, from 2.4.4, p. 82. A measurable
    function between zero and one has a finite real integral
    on a measurable finite-mass set, bounded by that mass.
    No integral or primitive is assumed to exist. *)
Lemma unit_bounded_nonnegative_subset_integral_finite (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X) (u:X->extended_real_line R):
  measure_measurable mu A ->mu A< +oo ->
  is_measure_measurable_function mu (partial_function_total u) ->
  (forall x,0<=u x<= 1) ->
  exists r:R,is_measure_subset_integral mu A (partial_function_total u) r%:E /\
    (0<=r)%R /\r%:E<=mu A.
Proof.
move=>hA hFinite hU hBounds.
have [a [hI hPositive]]:=nonnegative_total_subset_integral_exists hm hA hU
  (fun x=>(andP (hBounds x)).1).
have hOne:=@measure_nonnegative_constant_subset_integral R X mu A 1 hm hA (ltac:(by [])).
rewrite mul1e in hOne.
have hCompare:measure_almost_everywhere_on mu A [set x|u x<= 1%R%:E*(1:extended_real_line R)].
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=>x _ hx.
  rewrite mul1e; exact:(andP (hBounds x)).2.
have hUpper:=@subset_total_integral_positive_comparison R X mu hm A u (fun _=>1) 1 a (mu A)
  ltr01 hI hOne hCompare.
rewrite mul1e in hUpper.
have hFin:a \is a fin_num by rewrite (ge0_fin_numE hPositive); exact:(le_lt_trans hUpper hFinite).
exists (fine a); split; first by rewrite fineK.
split; first by move:hPositive; rewrite -(fineK hFin) lee_fin.
by rewrite fineK.
Qed.
