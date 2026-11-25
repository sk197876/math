(** Supporting the iterated projection formula in Federer (1969), 2.10.16,
    p. 178. A sequence squeezed between increasing partition counts and
    their limit has the same integral supremum as that limit. This is a
    consequence of 2.4.4(5), p. 82, and 2.4.7, p. 84, not a separate printed
    theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP
  ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum PartialFunctionBasic
  PartialExtendedOrderLoci MeasureUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralComparison MeasureNonnegativeIntegral MeasureAlmostUP MeasureAlmostBasic
  TotalIncreasingIntegralValues MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_sandwich_integral_supremum]: supporting
    limiting integral calculation for 2.10.16, p. 178.
    No monotonicity of the middle sequence is required. Its
    prescribed integral supremum suffices, even when infinite. *)
Theorem total_sandwich_integral_supremum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v : nat -> X -> extended_real_line R) (g : X -> extended_real_line R)
    (a : nat -> \bar R) b :
  (forall j x, 0<=u j x) ->
  (forall x, extended_increases_to (fun j => u j x) (g x)) ->
  (forall j, is_measure_measurable_function mu (partial_function_total (u j))) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  (forall j x, u j x<=v j x /\ v j x<=g x) ->
  (forall j, is_measure_integral mu (partial_function_total (v j)) (a j)) ->
  is_extended_real_supremum [set c | exists j, c=a j] b ->
  is_measure_integral mu (partial_function_total g) b.
Proof.
move=> hpos hlim hu hg hs hv hsup.
have hposg x : 0<=g x.
  exact: le_trans (hpos 0%N x) (le_trans (hs 0%N x).1 (hs 0%N x).2).
have hactual (f : X -> extended_real_line R) : (forall x, 0<=f x) ->
    is_measure_measurable_function mu (partial_function_total f) ->
    is_measure_integral mu (partial_function_total f)
      (measure_lower_integral mu (partial_function_total f)).
  move=> hf hmeas.
  have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total f)).
    apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
    exists (f x); by split.
  exact (@nonnegative_measurable_function_integral R X mu hm (partial_function_total f) hmeas hp).1.
have hi := hactual g hposg hg.
have hiu j := hactual (u j) (hpos j) (hu j).
have hmono (f h : X -> extended_real_line R) (r t : \bar R) : is_measure_integral mu (partial_function_total f) r ->
    is_measure_integral mu (partial_function_total h) t -> (forall x, f x<=h x) -> r<=t.
  move=> hf hh hle; apply: (@measure_integral_monotone R X mu hm _ _ _ _ hf hh).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f x),(h x); by split=> //; split.
have hvals := @total_increasing_integral_values R X mu hm u g
  (fun j => measure_lower_integral mu (partial_function_total (u j)))
  (measure_lower_integral mu (partial_function_total g)) hpos hlim hiu hi.
have he : measure_lower_integral mu (partial_function_total g)=b.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply: (extended_real_supremum_least (extended_increasing_limit_supremum hvals))=> c [j ->].
    apply: le_trans (@hmono _ _ _ _ (hiu j) (hv j) (fun x => (hs j x).1)) _.
    apply: (extended_real_supremum_upper hsup); by exists j.
  - apply: (extended_real_supremum_least hsup)=> c [j ->].
    exact: (@hmono _ _ _ _ (hv j) hi (fun x => (hs j x).2)).
by rewrite -he.
Qed.
