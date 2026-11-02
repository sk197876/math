(** Federer (1969), 3.2.36, p. 272:
    nonempty compact bodies in one Hausdorff
    neighbourhood have a common actual norm bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded CompactProfileNearest
  HausdorffTubeControl HausdorffDistanceUP HausdorffDistance MetricSetDistanceUP MetricSetDistanceBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_euclidean_local_norm_bound]:
    supporting a uniform tube-volume bound for
    compact-convex continuity in Federer 3.2.36,
    p. 272. A fixed compact body has
    a finite positive containing radius. The
    actual Hausdorff distance and a local nearest
    point enlarge that radius uniformly for all
    neighbours. Convexity is unnecessary here. *)
Theorem hausdorff_euclidean_local_norm_bound (R:realType) n
    (A:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))):
  exists c:R,0<c /\ forall B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)),
    mdist A B<1 ->forall x,val B x ->inner_norm (@euclidean_inner_productP R n) x<=c.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have [r [hr hRadius]]:=compact_metric_set_ball_bound A (0%R:X).
exists (r+1); split; first lra.
move=>B hAB x hx.
have hDiff:=hausdorff_compact_profile_difference_bound B A x.
have hZero:=metric_set_distance_member (compact_set_distance_profile_specification B) hx.
rewrite hZero subr0 (metric_sym B A) in hDiff.
have [a [ha hNear]]:=compact_profile_nearest_point A x.
have hA:=hRadius a ha.
change (is_true (mdist (0%R:X) a<=r)) in hA.
have hTriangle:=metric_triangle (0%R:X) a x.
rewrite (metric_sym a x) hNear in hTriangle.
change (is_true (inner_norm (@euclidean_inner_productP R n) x<=r+1)).
have hNorm:mdist (0%R:X) x=inner_norm (@euclidean_inner_productP R n) x.
  by rewrite inner_metric_distanceE sub0r inner_normN.
rewrite -hNorm.
lra.
Qed.
