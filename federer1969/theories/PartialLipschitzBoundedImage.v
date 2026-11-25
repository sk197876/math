(** Federer (1969), 3.2.14(1), p. 251:
    a Lipschitz image of a bounded parametrizing set
    is bounded. Empty graphs and empty metric targets
    remain valid cases. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialMetricLipschitz
  CoveringFamilyUP CoveringFamilyLaws MetricClosedBalls MetricBoundedUnion
  MetricBoundedClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_lipschitz_bounded_image]: the
    bounded-image consequence of the parametrization in
    Federer 3.2.14(1), p. 251, used in the binary
    union observation on p. 252. *)
Theorem partial_lipschitz_bounded_image (R : realType)
    (X Y : metricType R) (f : partial_function X Y) (L : R) :
  is_partial_metric_lipschitz_bound f L ->
  metric_set_bounded (partial_function_domain f) ->
  metric_set_bounded (partial_function_range f).
Proof.
move=> [hL hLip] hb.
case: (pselect (partial_function_range f !=set0))=> [[a [x hx]]|he].
- have [r [hr hbound]] := metric_bounded_distance_bound x hb.
  have hsub : partial_function_range f `<=` metric_closed_ball a (L*r).
    move=> b [y hy]; change (is_true (mdist a b<=L*r)).
    have hdy : partial_function_domain f y by exists b.
    exact: le_trans (hLip x y a b hx hy) (ler_wpM2l hL (hbound y hdy)).
  exact: (metric_bounded_subset hsub (covering_closed_ball_bounded a (mulr_ge0 hL hr))).
- have hzero : partial_function_range f=set0.
    apply/seteqP; split=> y; first by move=> hy; exfalso; apply: he; exists y.
    by move=> [].
  rewrite hzero; exact: metric_bounded_empty.
Qed.
