(** Federer (1969), 4.1.25, p. 383: pass from
    the smooth image actions to the Lipschitz image by
    2.4.9, p. 85. The scalar limit keeps its
    original partial domain. Its measurability follows from
    the measurable smooth actions and their almost-everywhere
    limit; it is not an extra input hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology
  ExtendedRealOrderLimit PartialAbsolutePartsGraph PartialExtendedOrderLoci
  PartialDominatedConvergence PartialFunctionLowerLimitSealed
  MeasurableLowerLimit MeasureFatouConvergent MeasurableAlmostModification
  MeasureUP MeasureAlmostUP MeasureAlmostEquality MeasureIntegralUP
  MeasureIntegralUniqueness MeasureBoundedConvergence ExtendedIncreasingLimitSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [current_lipschitz_lebesgue_action_dominated_limit]:
    the dominated-convergence step of the first proof of
    4.1.25, p. 383, using the original partial
    differential integrand. The already proved scalar limit
    of smooth current actions determines its integral exactly.
    No finite ambient measure assumption is introduced. *)
Theorem current_lipschitz_lebesgue_action_dominated_limit
    (R:realType) (X:choiceType) (mu:set X->\bar R) (hm:is_measure mu)
    (f:nat->partial_function X (extended_real_line R))
    (g h:partial_function X (extended_real_line R))
    (a:nat->R) (b:R) :
  is_measure_summable mu h ->
  (forall i,is_measure_integral mu (f i) (a i)%:E) ->
  (forall i,measure_almost_everywhere mu
    (partial_extended_le_locus
      (partial_extended_function_absolute_value (f i)) h)) ->
  measure_almost_everywhere mu (partial_extended_convergence_locus f g) ->
  extended_order_limit (fun i=>(a i)%:E) b%:E ->
  is_measure_integral mu g b%:E.
Proof.
move=>hSummable hActions hBound hConvergence hValues.
pose k:=@PartialFunctionLowerLimit.value R X f.
have hK:=@PartialFunctionLowerLimit.laws R X f.
have hMeasurableK:=@measurable_partial_lower_limit R X mu hm f k
  (fun i=>(hActions i).1) hK.
have hAlmost:=@partial_convergent_lower_limit_almost_equal R X mu hm
  f g k hK hConvergence.
have hMeasurableG:=@measurable_function_almost_equal R X
  (extended_real_line R) mu hm k g hMeasurableK
  (@measure_almost_equal_sym R X (extended_real_line R) mu g k hAlmost).
have [c [error [d [hCI [hGI [_ [_ hCLimit]]]]]]] :=
  @measure_bounded_convergence R X mu hm f g h hSummable
    (fun i=>(hActions i).1) hMeasurableG hBound hConvergence.
have hC:c=a.
  apply:funext=>i.
  exact:EFin_inj (measure_integral_unique (hCI i) (hActions i)).
rewrite hC in hCLimit.
have hValue:=extended_order_limit_unique hCLimit hValues.
by rewrite hValue in hGI.
Qed.
