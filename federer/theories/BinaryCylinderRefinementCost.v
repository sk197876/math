(** Equal-cost finite refinements of cylinders, supporting the
    self-contained counterexample in Federer (1969), 2.3.8, p. 78, via the
    covering infimum of 2.10.1, p. 170. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport CountingConstantSum CountingFinitePredicate
  BinaryWordRefinement BinaryCylinderCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_cylinder_refinement_sum]: the total
    cost of all length-n extensions is the cost of the prefix,
    supporting the covering measure in the local counterexample
    for Federer 2.3.8, p. 78. *)
Lemma binary_cylinder_refinement_sum (R : realType) n w (hw : (size w <= n)%N) :
  nonnegative_sum [set u : n.-tuple bool | prefix w u]
    (fun u => @binary_cylinder_cost R u) = (@binary_cylinder_cost R w).
Proof.
have he : nonnegative_sum [set u : n.-tuple bool | prefix w u]
    (fun u => @binary_cylinder_cost R u) =
    nonnegative_sum [set u : n.-tuple bool | prefix w u] (fun _ => (((2 : R)^+n)^-1)%:E).
  apply: nonnegative_sum_ext=> u _; by rewrite /binary_cylinder_cost size_tuple.
rewrite he nonnegative_constant_sum_counting; last by rewrite invr_ge0 exprn_ge0 // ler0n.
rewrite counting_finite_predicate (binary_word_prefix_card hw) (binary_cylinder_cost_refinement R hw).
have hp : (((2 : R)^+n) != 0)%R by rewrite expf_neq0 // pnatr_eq0.
rewrite muleA -EFinM (mulVf hp).
by rewrite /binary_cylinder_cost mul1r.
Qed.
