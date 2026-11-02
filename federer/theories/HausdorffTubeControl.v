(** Federer (1969), 3.2.36, p. 272:
    actual Hausdorff profile bounds control
    the original distance tubes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric
  HausdorffDistanceUP HausdorffDistance MetricSetDistanceUP MetricSetDistanceBasic
  MetricDistanceTube MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_compact_profile_difference_bound]:
    supporting the compact-convex volume continuity
    in Federer 3.2.36, p. 272.
    The already specified Hausdorff supremum bounds
    the signed difference of actual distance
    profiles. Neither convexity nor finite
    dimension is needed for this metric support. *)
Lemma hausdorff_compact_profile_difference_bound (R:realType) (X:metricType R)
    (A B:compact_hausdorff_space X) x:
  compact_set_distance_profile B x-compact_set_distance_profile A x<=mdist A B.
Proof.
apply:le_trans (ler_norm _) _; rewrite compact_hausdorff_distanceE.
exact:hausdorff_distance_profile_upper_law (@hausdorff_distance_specification R X) A B x.
Qed.

(** Source for [hausdorff_compact_tube_transport]:
    supporting the tube comparisons used to
    deduce continuity in Federer 3.2.36,
    p. 272, from Steiner's formula.
    The complete original tubes satisfy the
    radius transport estimate, with arbitrary real
    cutoffs and without convexity assumptions. *)
Lemma hausdorff_compact_tube_transport (R:realType) (X:metricType R)
    (A B:compact_hausdorff_space X) (r s:R):
  mdist A B<=s ->
  [set x|compact_set_distance_profile A x<r] `<=`
    [set x|compact_set_distance_profile B x<r+s].
Proof.
move=>hDistance x hx.
have hDiff:=hausdorff_compact_profile_difference_bound A B x.
change (is_true (compact_set_distance_profile A x<r)) in hx.
change (is_true (compact_set_distance_profile B x<r+s)).
lra.
Qed.

(** Source for [hausdorff_compact_source_in_tube]:
    supporting the two compact-source containments
    in the continuity argument of Federer
    3.2.36, p. 272. An original source
    point has zero distance to its own set,
    so strict Hausdorff closeness puts the
    entire original source inside the other tube. *)
Lemma hausdorff_compact_source_in_tube (R:realType) (X:metricType R)
    (A B:compact_hausdorff_space X) (r:R):
  mdist A B<r ->val A `<=` [set x|compact_set_distance_profile B x<r].
Proof.
move=>hr x hx.
have hDiff:=hausdorff_compact_profile_difference_bound A B x.
have hZero:=metric_set_distance_member (compact_set_distance_profile_specification A) hx.
rewrite hZero subr0 in hDiff; exact:le_lt_trans hDiff hr.
Qed.
