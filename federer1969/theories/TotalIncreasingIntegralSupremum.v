(** An extended-valued total-function adapter for the increasing convergence
    theorem cited in Federer (1969), 2.10.10, p. 176. The underlying theorem
    is 2.4.7, p. 84 The adapter identifies the integral by its prescribed
    supremum, including infinity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedRealOrderLimit
  ExtendedIncreasingLimitSupremum PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitExtremaUP PartialExtendedOrderLoci TotalExtendedLowerLimit
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIncreasingConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_increasing_integral_supremum]:
    supporting total extended-valued form of Federer 2.4.7,
    p. 84, as used in 2.10.10, p. 176.
    Measurability of the limit and existence of its integral
    are conclusions. Neither pointwise nor integral limits
    are required to be finite. *)
Theorem total_increasing_integral_supremum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : nat -> X -> extended_real_line R) (g : X -> extended_real_line R)
    (a : nat -> \bar R) (b : \bar R) :
  (forall n x, 0<=u n x) ->
  (forall x, extended_increases_to (fun n => u n x) (g x)) ->
  (forall n, is_measure_integral mu (partial_function_total (u n)) (a n)) ->
  is_extended_real_supremum [set c | exists n, c=a n] b ->
  is_measure_integral mu (partial_function_total g) b.
Proof.
move=> hp hlim hi hsup.
have hmon n m x : (n<=m)%N -> u n x<=u m x := (hlim x).1 n m.
have he : total_extended_lower_limit u=g.
  apply: funext=> x.
  exact: extended_order_limit_unique (total_extended_lower_limit_increases hmon x).2 (hlim x).2.
have hg : is_partial_function_lower_limit (fun n => partial_function_total (u n)) (partial_function_total g).
  rewrite -he; exact: total_extended_lower_limit_specification.
have hpos n : measure_almost_everywhere mu
    (partial_extended_nonnegative_locus (partial_function_total (u n))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (u n x); split=> //; exact: hp.
have hinc n : measure_almost_everywhere mu
    (partial_extended_le_locus (partial_function_total (u n)) (partial_function_total (u n.+1))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (u n x),(u n.+1 x); split=> //; split=> //.
  exact: hmon n n.+1 x (leqnSn n).
have [_ [hgi _]] := @measure_increasing_convergence R X mu hm
  (fun n => partial_function_total (u n)) (partial_function_total g) hg
  (fun n => (hi n).1) hpos hinc.
have hv := @measure_increasing_integral_values R X mu hm
  (fun n => partial_function_total (u n)) (partial_function_total g) a _ hg hpos hinc hi hgi.
have hb := extended_real_supremum_unique (extended_increasing_limit_supremum hv) hsup.
by rewrite -hb.
Qed.
