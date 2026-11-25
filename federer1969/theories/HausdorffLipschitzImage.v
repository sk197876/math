(** Federer (1969), 3.2.36, p. 272:
    supporting Hausdorff control of compact images.
    The distance laws, nearest points and an
    actual Lipschitz bound prove the estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactProfileNearest
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance MetricSetDistanceUP MetricSetDistanceBasic LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_hausdorff_lipschitz_image_bound]:
    supporting continuity of (p,S) -> p(S)
    in Federer 3.2.36, p. 272.
    Arbitrary compact images specified by their
    exact image laws satisfy the expected
    Lipschitz Hausdorff bound. No compact-image
    operator or selected nearest-point field
    is postulated. Convexity and finite dimension
    are unnecessary for this metric support. *)
Theorem compact_hausdorff_lipschitz_image_bound (R:realType) (X Y:metricType R)
    (F:X->Y) (c:R) (A B:compact_hausdorff_space X)
    (P Q:compact_hausdorff_space Y):
  is_metric_lipschitz_bound setT F c ->val P=F @` val A ->val Q=F @` val B ->
  mdist P Q<=c*mdist A B.
Proof.
move=>[hc hF] hP hQ.
have hd:0<=mdist A B:=mdist_ge0 A B.
have hDirected:=(@hausdorff_distance_directed_bound R X (@hausdorff_distance R X)
  (@hausdorff_distance_specification R X) A B (mdist A B) hd).1
  ltac:(by rewrite -compact_hausdorff_distanceE).
have hBound (C D:compact_hausdorff_space X) (U V:compact_hausdorff_space Y):
    val U=F @` val C ->val V=F @` val D ->
    (forall a,val C a ->compact_set_distance_profile D a<=mdist A B) ->
    forall y,val U y ->compact_set_distance_profile V y<=c*mdist A B.
  move=>hU hV hCD y; rewrite hU=>[[a ha <-]].
  have [b [hb hNear]]:=compact_profile_nearest_point D a.
  have hFb:val V (F b) by rewrite hV; exists b.
  have hLower:=@metric_set_distance_lower R Y (val V) (compact_set_distance_profile V)
    (compact_set_distance_profile_specification V) (F a) (F b) hFb.
  apply:le_trans hLower _; apply:le_trans (hF a b I I) _.
  rewrite hNear; exact:ler_pM hc (metric_set_distance_nonnegative
    (compact_set_distance_profile_specification D) a) (lexx c) (hCD a ha).
rewrite compact_hausdorff_distanceE.
apply ((@hausdorff_distance_directed_bound R Y (@hausdorff_distance R Y)
  (@hausdorff_distance_specification R Y) P Q (c*mdist A B) (mulr_ge0 hc hd)).2).
split.
- exact:hBound hP hQ hDirected.1.
- exact:hBound hQ hP hDirected.2.
Qed.
