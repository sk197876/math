(** Federer (1969), 2.10.43, printed p. 201: agreement on the original
    source and preservation of its least Lipschitz bound give equality of
    optimal constants. Derive this before selecting an extension witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric LipschitzUP KirszbraunExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kirszbraun_competing_bound_restriction]: supporting
    lower bound for the optimal extension constant
    in 2.10.43, p. 201. Every global bound
    for an agreeing extension is a bound for the
    original map on its exact source. *)
Lemma kirszbraun_competing_bound_restriction (R : realType) m n S f g L M :
  @is_kirszbraun_extension R m n S f g L -> is_metric_lipschitz_bound setT g M ->
  is_metric_lipschitz_bound S f M.
Proof.
move=> hExt [hM hbound]; split=> // x y hx hy.
rewrite -(@kirszbraun_extension_agreement_law R m n S f g L hExt x hx)
  -(@kirszbraun_extension_agreement_law R m n S f g L hExt y hy).
exact: hbound x y I I.
Qed.

(** Source for [kirszbraun_extension_optimal_bound]: direct
    equality-of-optimal-constants content of 2.10.43,
    p. 201, expressed by the already specified
    least-bound laws of 2.2.7, p. 64. This
    conclusion uses no extension implementation. *)
Theorem kirszbraun_extension_optimal_bound (R : realType) m n S f g L :
  @is_kirszbraun_extension R m n S f g L ->
  is_least_metric_lipschitz_constant S f L -> is_least_metric_lipschitz_constant setT g L.
Proof.
move=> hExt hleast; constructor.
- exact: kirszbraun_extension_bound_law hExt.
- move=> M hM.
  have hr := @kirszbraun_competing_bound_restriction R m n S f g L M hExt hM.
  exact (@least_metric_lipschitz_minimal R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] S f L hleast M hr).
Qed.
