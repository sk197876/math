(** Strict line-length inequality supporting Federer (1969), 2.10.31, p.
    196, final paragraph. A compact subset of a closed interval which misses
    an interior point has strictly smaller scalar Lebesgue measure. Expand
    the printed observation using a missing open interval and the two
    remaining closed intervals. Source context: CenteredSectionBounds.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal
  topology lra.
From Federer Require Import RealMetricBackground MetricClosedBalls MetricClosedSeparation
  LebesgueScalarMeasure MeasureUP MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_scalar_missing_interior_length]: supporting
    strict H^1 inequality for the line L
    in 2.10.31, p. 196. This scalar form
    includes the empty compact source and requires
    the missing point to be strictly interior. *)
Theorem compact_scalar_missing_interior_length (R : realType)
    (A : set (real_line_metric R)) (r t : R) :
  compact A -> (forall x, A x -> `|x|<=r) -> -r<t -> t<r -> ~A t ->
  (lebesgue_scalar_measure A<(r+r)%:E)%E.
Proof.
move=> hc hb hlt htr ht.
have hclosed : closed A := compact_closed (@metric_hausdorff R (real_line_metric R)) hc.
have [e [he hgap]] := closed_set_missing_closed_ball hclosed ht.
pose m := Num.min e (Num.min (r-t) (r+t)).
pose d := m/2.
have hm : 0<m by rewrite /m lt_min he lt_min !subr_gt0; apply/andP; split=> //; lra.
have hme : m<=e by rewrite /m ge_min lexx.
have hmr : m<=r-t by rewrite /m ge_min ge_min lexx orbT.
have hml : m<=r+t by rewrite /m ge_min ge_min lexx !orbT.
have hd : 0<d by rewrite /d divr_gt0 // ltr0n.
have hde : d<=e by rewrite /d; lra.
have hleft : -r<=t-d by rewrite /d; lra.
have hright : t+d<=r by rewrite /d; lra.
have hcover : A `<=` `[-r,t-d] `|` `[t+d,r].
  move=> x hx; have /andP[hx0 hx1] : -r<=x<=r by rewrite -ler_norml; exact: hb x hx.
  case: (leP x (t-d))=> hxd.
  - left; by rewrite /= in_itv /= hx0 hxd.
  - right; rewrite /= in_itv /= hx1 andbT.
    apply/negP=> hbad.
    have hxd1 : x<t+d by rewrite ltNge; apply/negP; exact hbad.
    exfalso; apply: (hgap x _ hx).
    rewrite /metric_closed_ball /= real_line_metric_distanceE ler_norml.
    apply/andP; split; lra.
have hh := @measure_binary_cover R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) A `[-r,t-d] `[t+d,r] hcover.
rewrite (lebesgue_scalar_segment hleft) (lebesgue_scalar_segment hright) -EFinD in hh.
apply: le_lt_trans hh _; rewrite lte_fin; lra.
Qed.
