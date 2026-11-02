(** Federer (1969), 2.4.8, p. 84: integration of a nonnegative countable
    numerical sum, in the total-function form used by the P1 calculation in
    2.6.2, pp. 115–116. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureIntegralUP NonnegativeSum NonnegativeSumSupport NumericalSum
  PartialNumericalSumUP MeasureCountableNonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_countable_nonnegative_integral]: supporting
    total-function, arbitrary countable-index form of Federer 2.4.8,
    p. 84, for the rectangle-family sums in 2.6.2, p. 116.
    Empty index sets and infinite integral values are allowed. *)
Lemma total_countable_nonnegative_integral (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J)
    (u : J -> X -> extended_real_line R) (a : J -> \bar R) :
  countable D -> (forall j, D j -> forall x, 0 <= u j x) ->
  (forall j, D j -> is_measure_integral mu (partial_function_total (u j)) (a j)) ->
  is_measure_integral mu (partial_function_total (fun x => nonnegative_sum D (fun j => u j x)))
    (nonnegative_sum D a).
Proof.
move=> hc hu hi.
refine (@measure_countable_nonnegative_integral_values R X J mu hm D
  (fun j => partial_function_total (u j)) _ a hc _ _ _).
- move=> x z; split.
  + move=> hz; exists (fun j => u j x); split; first by move=> j _.
    have hp : forall j, D j -> 0 <= u j x by move=> j hj; exact (hu j hj x).
    rewrite (numerical_sum_nonnegative hp).
    by rewrite (hz : nonnegative_sum D (fun j => u j x) = z).
  + move=> [v [hv hs]].
    have hnon j (hj : D j) : 0 <= v j by rewrite -(hv j hj : u j x = v j); exact (hu j hj x).
    rewrite (numerical_sum_nonnegative hnon) in hs; case: hs=> <-.
    apply: nonnegative_sum_ext=> j hj; exact: hv j hj.
- move=> j hj x y <-; exact (hu j hj x).
- exact: hi.
Qed.
