(** Federer (1969), 3.2.22, pp. 259–260:
    supporting existence and comparison laws for the
    nonnegative local subset integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableZeroExtension
  PartialExtendedOrderLoci ZeroExtensionNonnegative MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralBounds MeasureNonnegativeIntegral MeasureIntegralComparison MeasureIntegralScaleLaw MeasureUpperIntegralScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_total_subset_integral_exists]:
    existence of the local nonnegative integrals in Federer
    3.2.22, pp. 259–260, by 2.4.4(2),
    p. 82, and the subset convention 2.4.10, p. 85.
    Infinite integral values and null subsets are allowed. *)
Lemma nonnegative_total_subset_integral_exists (R:realType) (X:choiceType)
    (rho:set X->\bar R) (hr:is_measure rho) (A:set X) (u:X->extended_real_line R):
  measure_measurable rho A ->is_measure_measurable_function rho (partial_function_total u) ->
  (forall x,0<=u x) ->exists a,is_measure_subset_integral rho A (partial_function_total u) a /\ 0<=a.
Proof.
move=>hA hU hNonnegative.
have hPositive:measure_almost_everywhere rho (partial_extended_nonnegative_locus (partial_function_total u)).
  apply:(measure_almost_everywhere_mono hr _ (measure_almost_everywhere_true hr))=>x _.
  exists (u x); by split.
have hCut:=measurable_zero_extension hr (0:extended_real_line R) hA hU.
have hPos:=zero_extension_nonnegative_almost hr A hPositive.
have hI:=nonnegative_measurable_function_integral hr hCut hPos.
exists (measure_lower_integral rho (partial_function_zero_extension (0:extended_real_line R) A (partial_function_total u))).
exact hI.
Qed.

(** Source for [subset_total_integral_positive_comparison]:
    integration of the local lambda-power inequalities
    in Federer 3.2.22, pp. 259–260, using
    2.4.4(3),(5), p. 82. Both given integrals
    may be infinite. The comparison need hold only
    almost everywhere on the actual subset A. *)
Lemma subset_total_integral_positive_comparison (R:realType) (X:choiceType)
    (rho:set X->\bar R) (hr:is_measure rho) (A:set X)
    (u v:X->extended_real_line R) (c:R) a b:
  (0<c)%R ->
  is_measure_subset_integral rho A (partial_function_total u) a ->
  is_measure_subset_integral rho A (partial_function_total v) b ->
  measure_almost_everywhere_on rho A [set x|u x<=c%:E*v x] ->a<=c%:E*b.
Proof.
move=>hc hU hV hBound.
pose U:=partial_function_zero_extension (0:extended_real_line R) A (partial_function_total u).
pose V:=partial_function_zero_extension (0:extended_real_line R) A (partial_function_total v).
have hScaled:=measure_integral_positive_scale hr hc hV.
apply:(measure_integral_monotone hr hU hScaled).
apply:(measure_almost_everywhere_mono hr _
  ((measure_almost_everywhere_on_implication _ _ _).1 hBound))=>x hBx.
have [hx|hx]:=pselect (A x).
- exists (u x),(c%:E*v x); split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split; last exact:(hBx hx).
    exists (v x); split; last reflexivity.
    apply/partial_function_zero_extension_graph; left; by split.
- exists 0,0; split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split; last exact:lexx.
    exists 0; split; last by rewrite mule0.
    apply/partial_function_zero_extension_graph; right; by split.
Qed.
