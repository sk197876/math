(** Federer (1969), 2.4.16, p. 90: integration of a countable weighted sum.
    This supporting total-function form of 2.4.8, p. 84, is used by the
    test-weight construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureIntegralUP NonnegativeSum NonnegativeSumSupport NumericalSum PartialNumericalSumUP MeasureCountableNonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_nonnegative_series_integral]: supporting
    integral interchange for the weighted test in Federer 2.4.16,
    p. 90, by the proved countable-sum theorem 2.4.8. *)
Lemma total_nonnegative_series_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : nat -> X -> extended_real_line R) (a : nat -> \bar R) :
  (forall n x, 0 <= u n x) ->
  (forall n, is_measure_integral mu (partial_function_total (u n)) (a n)) ->
  is_measure_integral mu (partial_function_total (fun x => nonnegative_sum setT (fun n => u n x)))
    (nonnegative_sum setT a).
Proof.
move=> hu hi.
refine (@measure_countable_nonnegative_integral_values R X (Choice.clone nat _) mu hm setT
  (fun n => partial_function_total (u n)) _ a (countableP _) _ _ _).
- move=> x z; split.
  + move=> hz; exists (fun n => u n x); split; first by move=> n _.
    have hp : forall n, setT n -> 0 <= u n x by move=> n _; exact: hu.
    rewrite (numerical_sum_nonnegative hp).
    by rewrite (hz : nonnegative_sum setT (fun n => u n x) = z).
  + move=> [v [hv hs]].
    have hnon n : setT n -> 0 <= v n by move=> hn; rewrite -(hv n hn : u n x = v n); exact: hu.
    rewrite (numerical_sum_nonnegative hnon) in hs; case: hs=> <-.
    apply: nonnegative_sum_ext=> n hn; exact: hv n hn.
- move=> n _ x y <-; exact: hu.
- by move=> n _.
Qed.
