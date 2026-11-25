(** Hausdorff continuity of the least containing radius supporting Federer
    (1969), 2.10.31, p. 195. A nearest point in one compact set transfers a
    centred-ball bound to the other with at most the Hausdorff distance as
    loss. This uses only the abstract radius and Hausdorff-distance laws.
    Source context: CompactEnclosingRadiusUP.v and CompactProfileNearest.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealMetricBackground MetricClosedBalls CompactSetDistanceProfile CompactProfileNearest
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance CompactHausdorffMetric
  CompactEnclosingRadiusUP CompactEnclosingRadius NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_radius_hausdorff_transfer]: supporting
    radius control under Hausdorff perturbation in
    the compactness argument of 2.10.31, p. 195. *)
Lemma compact_radius_hausdorff_transfer (R : realType) (X : metricType R)
    (a : X) (C D : compact_metric_set X) (r s : R) :
  is_compact_enclosing_radius a C r -> is_compact_enclosing_radius a D s ->
  s<=r+hausdorff_distance C D.
Proof.
move=> hr hs.
have hd := hausdorff_distance_nonnegative_law (@hausdorff_distance_specification R X) C D.
have hb := (hausdorff_distance_directed_bound (@hausdorff_distance_specification R X) C D hd).1 (lexx _).
apply: (enclosing_radius_least_law hs (addr_ge0 (enclosing_radius_nonnegative_law hr) hd))=> x hx.
have [y [hy hxy]] := compact_profile_nearest_point C x.
have hay := enclosing_radius_contains_law hr hy.
have hdx := hb.2 x hx.
change (is_true (mdist a x<=r+hausdorff_distance C D)).
apply: le_trans (metric_triangle a y x) _.
rewrite (metric_sym y x) hxy; exact: lerD hay hdx.
Qed.

(** Source for [compact_enclosing_radius_lipschitz]: supporting
    continuity of the minimised radius in 2.10.31,
    p. 195. The Lipschitz constant is one. *)
Lemma compact_enclosing_radius_lipschitz (R : realType) (X : metricType R)
    (a : X) (C D : compact_metric_set X) :
  `|compact_enclosing_radius a C-compact_enclosing_radius a D|<=hausdorff_distance C D.
Proof.
have hC := compact_enclosing_radius_specification a C.
have hD := compact_enclosing_radius_specification a D.
have h1 := compact_radius_hausdorff_transfer hC hD.
have h2 := compact_radius_hausdorff_transfer hD hC.
rewrite (hausdorff_distance_symmetric_law (@hausdorff_distance_specification R X) D C) in h2.
rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [compact_enclosing_radius_continuous]: supporting
    radius continuity on the Hausdorff space used
    to attain the infimum in 2.10.31, p. 195. *)
Theorem compact_enclosing_radius_continuous (R : realType) (X : metricType R) (a : X) :
  continuous (fun C : compact_hausdorff_space X=>(compact_enclosing_radius a C : real_line_metric R)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R (compact_hausdorff_space X)
  [the metricType R of real_line_metric R] _ 1 (@ler01 R))=> C D.
rewrite real_line_metric_distanceE mul1r compact_hausdorff_distanceE.
exact: compact_enclosing_radius_lipschitz.
Qed.
