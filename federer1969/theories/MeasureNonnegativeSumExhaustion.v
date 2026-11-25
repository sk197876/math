(** Federer (1969), 2.4.8, p. 84: the
    measurable finite partial sums form an almost-everywhere
    increasing nonnegative sequence. Their common good domain
    is conull because the indexing set is countable. Source
    editions: PartialNumericalSumUP.v. These are the hypotheses
    needed to apply the increasing convergence theorem 2.4.7. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionSupremumUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureIntegralUP PartialNumericalSumUP PartialNumericalSum PartialNonnegativeSumLaws
  PartialFiniteNumericalSum PartialFamilyValueSelection CountableFiniteExhaustionUP
  NonnegativeSum MeasureFiniteNonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_nonnegative_sum_exhaustion]: supporting
    finite-sum sequence, with its integral values and almost-
    everywhere order, for Federer 2.4.8, p. 84. *)
Lemma measure_nonnegative_sum_exhaustion (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (C : nat -> {fset J})
    (f : J -> partial_function X (extended_real_line R)) (a : J -> \bar R) :
  countable D -> is_countable_finite_exhaustion D C ->
  (forall j, D j -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  (forall j, D j -> 0 <= a j) ->
  (forall j, D j -> is_measure_integral mu (f j) (a j)) ->
  let F n := partial_function_numerical_sum [set j | j \in C n] f in
  (forall n, is_measure_integral mu (F n) (\sum_(j <- C n) a j)) /\
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (F n))) /\
  (forall n, measure_almost_everywhere mu (partial_extended_le_locus (F n) (F n.+1))).
Proof.
move=> hD hC hp ha hi F.
have hsub n j : j \in C n -> D j := @finite_exhaustion_subset J D C hC n j.
have hpC n j : j \in C n -> forall x y, partial_function_graph (f j) x y -> 0 <= y.
  move=> hj; exact: hp j (hsub n j hj).
have hFi n : is_measure_integral mu (F n) (\sum_(j <- C n) a j).
  apply: (@measure_finite_nonnegative_sum_integral R X J mu hm (C n) f a (hpC n)).
  - move=> j hj; exact: ha j (hsub n j hj).
  - move=> j hj; exact: hi j (hsub n j hj).
split=> //; split.
- move=> n; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (measurable_function_domain (hFi n).1))=> x [z hz].
  exists z; split=> //.
  exact (@partial_nonnegative_sum_nonnegative R X J [set j | j \in C n] f (F n)
    (partial_function_numerical_sum_laws _ f) (hpC n) x z hz).
- move=> n.
  have he : measure_almost_everywhere mu (partial_function_common_domain D f).
    apply: (@measure_almost_everywhere_countable R X J mu hm D _ hD)=> j hj.
    exact: measurable_function_domain (hi j hj).1.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
  have [u hu] := @partial_family_common_values_exists R X J D f x hx.
  have hpoint k : partial_function_graph (F k) x (\sum_(j <- C k) u j).
    apply: (partial_numerical_finite_sum_graph (partial_function_numerical_sum_laws _ f) (hpC k) x _).2.
    exists u; split=> // j hj; exact: hu j (hsub k j hj).
  have hpos k j : j \in C k -> 0 <= u j.
    move=> hj; exact: hp j (hsub k j hj) x (u j) (hu j (hsub k j hj)).
  exists (\sum_(j <- C n) u j), (\sum_(j <- C n.+1) u j); split; first exact: hpoint.
  split; first exact: hpoint.
  rewrite -(nonnegative_sum_finite (hpos n)) -(nonnegative_sum_finite (hpos n.+1)).
  apply: nonnegative_sum_subset=> j hj.
  exact: (fsubsetP (@finite_exhaustion_increasing J D C hC n n.+1 (leqnSn n))) j hj.
Qed.
