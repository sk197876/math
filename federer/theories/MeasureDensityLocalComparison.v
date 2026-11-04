(** Federer (1969), 3.2.46, p. 282: local frozen
    Jacobian bounds give local area-measure bounds. This
    supporting integral comparison uses 2.4.3(2),(5),
    pp. 81–82, with the actual partial integrand domains
    and arbitrary outer test sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  PartialZeroExtension PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureDensityUP MeasureSubsetIntegral MeasureUpperIntegralScale MeasureUpperIntegralMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_density_local_graph_comparison]:
    an almost-everywhere local bound F<=cG gives the same
    bound on their actual density outer masses, supporting
    3.2.46, p. 282. Neither integrand nor test set
    is assumed measurable; exact graph values supply both
    domains. Infinite values of either outer mass are allowed. *)
Lemma measure_density_local_graph_comparison (R : realType) (X : choiceType)
    (phi mu nu : set X -> \bar R) (F G : partial_function X (extended_real_line R))
    (S : set X) (c : R) :
  is_measure phi -> is_measure_density phi F mu -> is_measure_density phi G nu ->
  0<c -> measure_almost_everywhere phi
    [set x | exists u v, partial_function_graph F x u /\ partial_function_graph G x v /\
      (S x -> (u<=c%:E*v)%E)] -> (mu S<=c%:E*nu S)%E.
Proof.
move=> hPhi hMu hNu hc hCompare.
rewrite (hMu S) (hNu S) /measure_subset_upper_integral
  -(@measure_upper_integral_positive_scale R X phi hPhi c
    (partial_function_zero_extension (0 : extended_real_line R) S G) hc).
apply: (@measure_upper_integral_monotone R X phi hPhi).
apply: (@measure_almost_everywhere_mono R X phi hPhi _ _ _ hCompare)=> x [u [v [hF [hG hBound]]]].
case: (boolp.pselect (S x))=> hx.
- exists u,(c%:E*v)%E; split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split.
    * exists v; split; last by [].
      apply/partial_function_zero_extension_graph; left; by split.
    * exact: hBound hx.
- exists 0,0; split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split.
    * exists 0; split; last by rewrite mule0.
      apply/partial_function_zero_extension_graph; right; by split.
    * exact: lexx.
Qed.
