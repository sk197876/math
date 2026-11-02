(** Federer (1969), 2.4.8, p. 84: interchange of a countable nonnegative sum
    and integration. The proof applies 2.4.7 to finite partial sums along a
    sealed finite exhaustion, and uses 2.1.1(13), p. 53, for the numerical
    sum of integral values. We retain Federer's arbitrary countable index
    set and pointwise nonnegativity, including the empty family and infinite
    sums. No relevant correction occurs in the local erratum. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureUpperIntegralNonnegative
  MeasureNonnegativeIntegral MeasureLowerLimitNonnegative MeasureIncreasingConvergence
  NonnegativeSum PartialNumericalSumUP PartialNumericalSum CountableFiniteExhaustionUP
  CountableFiniteExhaustionSealed FiniteExhaustionSumLimit ExtendedIncreasingLimitSupremum
  PartialSumExhaustion MeasureNonnegativeSumExhaustion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_countable_nonnegative_integral_values]:
    direct Federer 2.4.8, p. 84, with the summand
    integrals and pointwise sum specified by their abstract laws. *)
Theorem measure_countable_nonnegative_integral_values (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) (a : J -> \bar R) :
  countable D -> is_partial_function_numerical_sum D f g ->
  (forall j, D j -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  (forall j, D j -> is_measure_integral mu (f j) (a j)) ->
  is_measure_integral mu g (nonnegative_sum D a).
Proof.
move=> hD hg hp hi.
have hpAE j (hj : D j) : measure_almost_everywhere mu (partial_extended_nonnegative_locus (f j)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (measurable_function_domain (hi j hj).1))=> x [z hz].
  exists z; split=> //; exact: hp j hj x z hz.
have ha j : D j -> 0 <= a j.
  move=> hj; have he := @measure_upper_integral_unique R X mu (f j) _ (a j)
    (measure_upper_integral_specification mu (f j)) (hi j hj).2.1.
  rewrite -he; exact (@measure_upper_integral_nonnegative R X mu hm (f j) (hpAE j hj)).
pose C := @CountableFiniteExhaustion.value J D hD.
have hC : is_countable_finite_exhaustion D C := @CountableFiniteExhaustion.laws J D hD.
pose F n := partial_function_numerical_sum [set j | j \in C n] f.
have [hFi [hFp hFm]] := @measure_nonnegative_sum_exhaustion R X J mu hm D C f a hD hC hp ha hi.
have hlim := @partial_sum_exhaustion_lower_limit R X J D C f g hC hg hp.
have hgm := (@measure_lower_limit_nonnegative_integral R X mu hm F g hlim
  (fun n => (hFi n).1) hFp).1.
have hgi := @measure_increasing_integral_values R X mu hm F g
  (fun n => \sum_(j <- C n) a j) (measure_lower_integral mu g) hlim hFp hFm hFi hgm.
have hsum := @finite_exhaustion_nonnegative_sum_limit R J D C a hC ha.
have he := @extended_order_limit_unique R _ _ _ hgi.2 hsum.2.
by rewrite he in hgm.
Qed.

(** Source for [measure_countable_nonnegative_sum_integral]:
    complete Federer 2.4.8, p. 84: every summand
    and the sum are integrable by nonnegativity, and the integral
    of the sum is the sum of their integral values. *)
Theorem measure_countable_nonnegative_sum_integral (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J)
    (f : J -> partial_function X (extended_real_line R)) :
  countable D ->
  (forall j, D j -> is_measure_measurable_function mu (f j)) ->
  (forall j, D j -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  is_measure_integral mu (partial_function_numerical_sum D f)
    (nonnegative_sum D (fun j => measure_lower_integral mu (f j))).
Proof.
move=> hD hf hp; apply: (@measure_countable_nonnegative_integral_values R X J mu hm D f _ _ hD
  (partial_function_numerical_sum_laws D f) hp)=> j hj.
have hpAE : measure_almost_everywhere mu (partial_extended_nonnegative_locus (f j)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (measurable_function_domain (hf j hj)))=> x [z hz].
  exists z; split=> //; exact: hp j hj x z hz.
exact (@nonnegative_measurable_function_integral R X mu hm (f j) (hf j hj) hpAE).1.
Qed.
