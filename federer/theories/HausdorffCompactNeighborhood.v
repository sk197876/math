(** Federer (1969), 2.10.22, p. 185:
    sufficiently close source compact generators lie
    in every prescribed open neighbourhood of their
    limit generator. This supporting upper-neighbourhood
    fact follows from the Hausdorff distance and a
    uniform thickening of a compact set. Source
    editions and proof context: CompactGeneratorCostUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactSetDistanceProfile CompactProfileNearest CompactHausdorffMetric
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance MetricOpenThickening
  MetricCompactNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_compact_open_neighborhood]: supporting
    finite-prefix containment in 2.10.22, p. 185.
    No bounded compactness of the ambient space is
    needed for the neighbourhood of a given compact set. *)
Theorem hausdorff_compact_open_neighborhood (R : realType) (X : metricType R)
    (D : compact_metric_set X) (V : set X) :
  open V -> val D `<=` V -> exists eps : R, 0<eps /\
    forall C : compact_metric_set X, hausdorff_distance D C<eps -> val C `<=` V.
Proof.
move=> hV hDV.
have [eps [heps hthick]] := compact_metric_open_thickening (set_valP D).1 hV hDV.
exists eps; split=> // C hclose x hx; apply: hthick.
have h0 := hausdorff_distance_nonnegative_law (@hausdorff_distance_specification R X) D C.
have hdir := (proj1 (hausdorff_distance_directed_bound (@hausdorff_distance_specification R X) D C h0)) (lexx _).
have [y [hy hxy]] := compact_profile_nearest_point D x.
exists y; first exact hy.
change (is_true (mdist y x<eps)).
rewrite (metric_sym y x) hxy; exact: le_lt_trans (hdir.2 x hx) hclose.
Qed.
