(** Supporting increasing-convergence adapter for the inverse-square
    integral in Federer (1969), 2.6.3(2), p. 118. The mathematical theorem
    is already proved as 2.4.7, p. 84; this module connects its abstract
    partial-function interface to total real functions and a specified limit
    of integral values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialExtendedOrderLoci SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIncreasingConvergence ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum
  RealTotalIntegralLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_nonnegative_increasing_integral_limit]: supporting form
    of Federer 2.4.7, p. 84, used for the improper integral in 2.6.3(2), p.
    118 Measurability of the limit and existence of its integral are
    conclusions, not premises. *)
Theorem real_nonnegative_increasing_integral_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> R) (g : X -> R) (a : nat -> \bar R) (b : \bar R) :
  (forall n x, 0 <= f n x) ->
  (forall n x, f n x <= f n.+1 x) ->
  (forall x, extended_order_limit (fun n => (f n x)%:E) (g x)%:E) ->
  (forall n, is_measure_integral mu (real_total_integrand (f n)) (a n)) ->
  extended_order_limit a b -> is_measure_integral mu (real_total_integrand g) b.
Proof.
move=> hp hmon hconv hi hlim.
have hg := real_total_pointwise_lower_limit hconv.
have hpos n : measure_almost_everywhere mu
    (partial_extended_nonnegative_locus (real_total_integrand (f n))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f n x)%:E; split; first exact/real_total_integrand_graph.
  by rewrite lee_fin; exact: hp.
have hinc n : measure_almost_everywhere mu
    (partial_extended_le_locus (real_total_integrand (f n)) (real_total_integrand (f n.+1))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f n x)%:E, (f n.+1 x)%:E; split; first exact/real_total_integrand_graph.
  split; first exact/real_total_integrand_graph.
  by rewrite lee_fin; exact: hmon.
have [_ [hgi _]] := @measure_increasing_convergence R X mu hm
  (fun n => real_total_integrand (f n)) (real_total_integrand g) hg (fun n => (hi n).1) hpos hinc.
have hvalues := @measure_increasing_integral_values R X mu hm
  (fun n => real_total_integrand (f n)) (real_total_integrand g) a _ hg hpos hinc hi hgi.
have he := extended_order_limit_unique hvalues.2 hlim.
by rewrite -he.
Qed.
