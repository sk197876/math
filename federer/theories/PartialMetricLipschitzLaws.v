(** Federer (1969), 3.2.14(1), p. 251:
    compatibility of actual partial parametrizations
    with the Lipschitz convention of 2.2.7,
    pp. 63–64. A nonnegative bound can always
    be increased to a strictly positive bound. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialMetricLipschitz LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_metric_lipschitz_positive_bound]:
    compatibility with the positive Lipschitz bound
    of Federer 2.2.7, pp. 63–64, in the
    parametrization of 3.2.14(1), p. 251. *)
Lemma partial_metric_lipschitz_positive_bound (R : realType)
    (X Y : metricType R) (f : partial_function X Y) (L : R) :
  is_partial_metric_lipschitz_bound f L ->
  exists C, 0<C /\ is_partial_metric_lipschitz_bound f C.
Proof.
move=> [hL hLip]; exists (L+1); split.
- have hh := ler_ltD hL (ltr01 : (0<1 :> R)).
  by rewrite add0r in hh.
- split; first exact: addr_ge0 hL ler01.
  move=> x y a b ha hb.
  have hLC : L<=L+1.
    have hh := lerD (lexx L) (ler01 : (0<=1 :> R)).
    by rewrite addr0 in hh.
  exact (le_trans (hLip x y a b ha hb) (ler_wpM2r (mdist_ge0 x y) hLC)).
Qed.

(** Source for [partial_total_restriction_range]:
    the exact image in Federer 3.2.14(1), p. 251,
    for a given total map restricted to its source set. *)
Lemma partial_total_restriction_range (X Y : Type) (A : set X) (u : X -> Y) :
  partial_function_range (partial_function_source_restrict A (partial_function_total u))=u @` A.
Proof.
apply/seteqP; split=> y.
- by move=> [x [hx <-]]; exists x.
- by move=> [x hx <-]; exists x; split.
Qed.

(** Source for [partial_total_restriction_lipschitz]:
    agreement of the graph distance law with the
    Lipschitzian parametrization of Federer 3.2.14(1),
    p. 251. This law assigns no values outside A. *)
Lemma partial_total_restriction_lipschitz (R : realType)
    (X Y : metricType R) (A : set X) (u : X -> Y) (L : R) :
  is_partial_metric_lipschitz_bound
    (partial_function_source_restrict A (partial_function_total u)) L <->
  is_metric_lipschitz_bound A u L.
Proof.
split.
- move=> [hL hLip]; split=> // x y hx hy.
  have hax : partial_function_graph
    (partial_function_source_restrict A (partial_function_total u)) x (u x) by split.
  have hay : partial_function_graph
    (partial_function_source_restrict A (partial_function_total u)) y (u y) by split.
  exact (@hLip x y (u x) (u y) hax hay).
- move=> [hL hLip]; split=> // x y a b [hx <-] [hy <-].
  exact: hLip x y hx hy.
Qed.
