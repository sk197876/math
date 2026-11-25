(** Federer (1969), 3.2.33, p. 270: finite scalar
    integral bounds supporting differentiation of the primitive g. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral
  RestrictedIntegralIdentity FiniteMeasureBoundedNorm NonnegativeSubsetIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_subset_real_constant_bounds]: supporting
    differentiation of the integral defining g in Federer
    3.2.33, p. 270, by 2.4.4(5), p. 82.
    Real lower and upper bounds integrate on every measurable
    set of finite mass. Either bound may be negative; no
    spurious positive lower-constant hypothesis is imposed. *)
Lemma finite_subset_real_constant_bounds (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (A:set X)
    (u:X->R) (mass r c C:R):
  measure_measurable mu A ->mu A= mass%:E ->
  (forall x,A x ->(c<=u x<=C)%R) ->
  is_measure_subset_integral mu A (partial_function_total (fun x=>((u x)%:E:extended_real_line R))) r%:E ->
  (c*mass<=r<=C*mass)%R.
Proof.
move=>hA hMass hBound hI.
pose nu:=measure_restrict mu A.
have hn:=measure_restrict_is_measure hm A.
have hWhole:nu setT= mass%:E by rewrite /nu /measure_restrict setIT hMass.
have hConstant (s:R):is_measure_subset_integral mu A
    (partial_function_total (fun _:X=>(s%:E:extended_real_line R))) (s*mass)%:E.
  have hRestricted:=@finite_measure_constant_integral R X nu hn mass s hWhole.
  exact:((@restricted_integral_zero_extension_iff R X mu hm A
    (partial_function_total (fun _:X=>(s%:E:extended_real_line R))) (s*mass)%:E hA).1 hRestricted).
have hLower:measure_almost_everywhere_on mu A [set x|c%:E<= 1%R%:E*(u x)%:E].
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=>x _ hx.
  change (is_true (c%:E<= 1%R%:E*(u x)%:E)).
  rewrite mul1e lee_fin; exact:(andP (hBound x hx)).1.
have hUpper:measure_almost_everywhere_on mu A [set x|(u x)%:E<= 1%R%:E*C%:E].
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=>x _ hx.
  change (is_true ((u x)%:E<= 1%R%:E*C%:E)).
  rewrite mul1e lee_fin; exact:(andP (hBound x hx)).2.
have hLo:=@subset_total_integral_positive_comparison R X mu hm A
  (fun _=>c%:E) (fun x=>((u x)%:E:extended_real_line R)) 1 (c*mass)%:E r%:E
  ltr01 (hConstant c) hI hLower.
have hHi:=@subset_total_integral_positive_comparison R X mu hm A
  (fun x=>((u x)%:E:extended_real_line R)) (fun _=>C%:E) 1 r%:E (C*mass)%:E
  ltr01 hI (hConstant C) hUpper.
rewrite mul1e lee_fin in hLo.
rewrite mul1e lee_fin in hHi.
apply/andP; by split.
Qed.
