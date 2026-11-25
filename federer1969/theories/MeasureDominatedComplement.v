(** Federer (1969), 2.4.9, p. 85: applying Fatou to the nonnegative sequence
    2h-|fn-g|, whose lower limit equals 2h almost everywhere. Source
    editions: MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedArithmetic PartialFunctionLimitExtremaUP
  PartialFunctionLowerLimitSealed MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  PartialDominatedConvergence DominatedErrorGraphs ExtendedDominatedLimit ExtendedLowerLimitUP
  ExtendedConvergentLowerLimit PartialIncreasingLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_dominated_complement_nonnegative]: the
    almost-everywhere nonnegativity required for Fatou in
    Federer 2.4.9, p. 85. *)
Lemma measure_dominated_complement_nonnegative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) n :
  measure_almost_everywhere mu (partial_dominated_real_limit_locus f g h) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_dominated_complement (f n) g h)).
Proof.
move=> he; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [u [z [c [hu [hz [hc [hb [hzb hlim]]]]]]]].
exists (c+c-`|u n-z|)%:E; split.
- exact: partial_finite_complement_graph (hu n) hz hc.
- exact: dominated_real_complement_nonnegative (hb n) hzb.
Qed.

(** Source for [measure_dominated_complement_lower_limit]: the
    pointwise limit 2h identified almost everywhere with the
    abstract lower limit of 2h-|fn-g| in Federer
    2.4.9, p. 85. This avoids changing the exact
    domains of either partial function on exceptional points. *)
Lemma measure_dominated_complement_lower_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g h k : partial_function X (extended_real_line R)) :
  is_partial_function_lower_limit (fun n => partial_dominated_complement (f n) g h) k ->
  measure_almost_everywhere mu (partial_dominated_real_limit_locus f g h) ->
  measure_almost_equal mu (partial_extended_function_add h h) k.
Proof.
move=> hk he; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [u [z [c [hu [hz [hc [hb [hzb hlim]]]]]]]].
pose v n := (c+c-`|u n-z|)%:E.
have hv n : partial_function_graph (partial_dominated_complement (f n) g h) x (v n).
  exact: partial_finite_complement_graph (hu n) hz hc.
have hd : partial_function_domain k x.
  rewrite (partial_function_lower_limit_domain hk); exists 0%N=> n _.
  by exists (v n).
have [y hy] := hd.
have hyl := @partial_lower_limit_scalar_values R X _ k x v y hk hv hy.
have hvl : is_extended_lower_limit v (c+c)%:E.
  apply: extended_convergent_lower_limit; exact: real_complement_error_limit hlim.
have ey := extended_lower_limit_unique hyl hvl.
exists (c+c)%:E; split.
- exact (@partial_finite_sum_graph R X h h x c c hc hc).
- by rewrite -ey.
Qed.
