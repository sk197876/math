(** Federer (1969), 2.3.9, p. 79: on B_j all function values exist, and
    completeness gives a pointwise limit with distance bounded by r_j. The
    statement below is the metric part of this argument, retaining exact
    partial domains. Source context: PartialFunctionPointwiseLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionLimitUP
  PartialFunctionPointwiseLimitUP NonnegativeSum NonnegativeSequenceTail
  CompleteMetricUP SummableMetricIncrementLimit SummableExceptionalTails.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_summable_metric_limit]: the pointwise
    convergence and tail bound on B_j in Federer 2.3.9,
    p. 79. This consequence uses only the specified graph
    of the limit, not its private construction. *)
Lemma partial_summable_metric_limit (R : realType) (X : Type) (Y : metricType R)
    (hY : is_complete_metric_space Y) (f : nat -> partial_function X Y)
    (h : partial_function X Y) (hh : is_partial_function_pointwise_limit f h)
    (a : nat -> \bar R) (E : nat -> set X) :
  (forall n, 0 <= a n) -> nonnegative_sum setT a < +oo ->
  (forall n x, ~ E n x -> (forall k, partial_function_domain (f k) x) /\
    forall y z, partial_function_graph (f n.+1) x y -> partial_function_graph (f n) x z ->
      (mdist y z)%:E <= a n) ->
  forall j x, ~ summable_exceptional_tail E j x ->
    partial_function_limit_locus f h x /\ forall m y z, (j <= m)%N ->
      partial_function_graph h x y -> partial_function_graph (f m) x z ->
      (mdist y z)%:E <= nonnegative_sequence_tail a m.
Proof.
move=> ha hf he j x hx.
have havoid n (hn : (j <= n)%N) : ~ E n x.
  move=> hex; apply: hx; by exists n.
have hd := (he j x (havoid j (leqnn j))).1.
pose u n := projT1 (cid (hd n)).
have hu n : partial_function_graph (f n) x (u n) := projT2 (cid (hd n)).
have hi n (hn : (j <= n)%N) : (mdist (u n.+1) (u n))%:E <= a n.
  exact: (he n x (havoid n hn)).2 (hu n.+1) (hu n).
have [v [hv hb]] := @summable_metric_increment_limit R Y hY u a j ha hf hi.
have hhv : partial_function_graph h x v.
  apply: (proj2 (hh x v)); by exists u.
split.
- exists u,v; by split=> //; split.
- move=> m y z hjm hy hz.
  have ey : y=v := partial_function_single_valued hy hhv.
  have ez : z=u m := partial_function_single_valued hz (hu m).
  rewrite ey ez; exact: hb m hjm.
Qed.
