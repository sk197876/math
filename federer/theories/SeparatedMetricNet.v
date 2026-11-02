(** Federer (1969), 2.2.16, p. 71: maximality makes A_n a 2/n-net in the
    support. This consequence uses only the abstract maximal separated-set
    laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import SeparatedMetricSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [maximal_separated_subset_covers]: direct
    consequence in the first paragraph of Federer 2.2.16,
    p. 71: each point of the ambient set is
    within r of a point of a maximal strictly r-separated
    subset. The nonnegative radius includes the zero case. *)
Theorem maximal_separated_subset_covers (R : realType) (X : metricType R)
    (A S : set X) (r : R) : 0 <= r -> is_maximal_separated_subset A r S ->
  forall x, A x -> exists y, S y /\ mdist x y <= r.
Proof.
move=> hr h x hx.
case: (pselect (exists y, S y /\ mdist x y <= r))=> hn; first exact hn.
exfalso.
have hfar y : S y -> r < mdist x y.
  move=> hy; rewrite ltNge; apply/negP=> hd; apply: hn; exists y; by split.
have hsep : is_strictly_separated_metric_set r (S `|` [set x]).
  move=> u v [hu|hu] [hv|hv] huv.
  - exact: (@separated_subset_separation R X A r S h u v hu hv huv).
  - rewrite hv metric_sym; exact: hfar hu.
  - rewrite hu; exact: hfar hv.
  - exfalso; apply: huv; by rewrite hu hv.
have hin : S `|` [set x] `<=` A.
  move=> y [hy|->]=> //; exact: (@separated_subset_inside R X A r S h y hy).
have hsub : S `<=` S `|` [set x] by move=> y hy; left.
have hsx : S x := @separated_subset_maximal R X A r S h (S `|` [set x]) hin hsep hsub x (or_intror (erefl _)).
apply: hn; exists x; split=> //; by rewrite mdistxx.
Qed.
