(** Federer (1969), 2.10.21, p. 183, last paragraph: the diameter map on
    nonempty compact subsets has Lipschitz constant two for the Hausdorff
    metric. Expand the short assertion by nearest points and the metric
    triangle inequality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import CompactSetDistanceProfile CompactProfileNearest CompactMetricBounded
  MetricDiameterUP MetricDiameter HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance
  CompactHausdorffMetric LipschitzUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_diameter_one_sided_bound]: supporting
    one-sided diameter estimate in 2.10.21,
    p. 183. Replace the two points of C
    by nearest points in D and pay at most
    one Hausdorff distance at each endpoint. *)
Lemma hausdorff_diameter_one_sided_bound (R : realType) (X : metricType R)
    (C D : compact_metric_set X) :
  compact_metric_diameter C<=compact_metric_diameter D+2*hausdorff_distance C D.
Proof.
pose h := hausdorff_distance C D.
have h0 : 0<=h := hausdorff_distance_nonnegative_law (@hausdorff_distance_specification R X) C D.
have hd0 : 0<=compact_metric_diameter D.
  have hh := metric_diameter_nonnegative (extended_metric_diameter_specification (val D)).
  by rewrite compact_metric_diameter_finite_value lee_fin in hh.
have hdir := (proj1 (hausdorff_distance_directed_bound (@hausdorff_distance_specification R X) C D h0)) (lexx h).
have hbound : (extended_metric_diameter (val C)<=(compact_metric_diameter D+2*h)%:E)%E.
  apply: (@metric_diameter_least R X (val C) (extended_metric_diameter (val C))
    (extended_metric_diameter_specification (val C)) (compact_metric_diameter D+2*h)%:E).
  - rewrite lee_fin.
    have htwo : (0<=2 :> R) by rewrite ler0n.
    exact: addr_ge0 hd0 (mulr_ge0 htwo h0).
  - move=> x y hx hy.
    have [u [hu hxu]] := compact_profile_nearest_point D x.
    have [v [hv hyv]] := compact_profile_nearest_point D y.
    have hxuBound : mdist x u<=h by rewrite hxu; exact: hdir.1 x hx.
    have hyvBound : mdist y v<=h by rewrite hyv; exact: hdir.1 y hy.
    have hdiam := metric_diameter_upper (extended_metric_diameter_specification (val D)) hu hv.
    rewrite compact_metric_diameter_finite_value lee_fin in hdiam.
    have h1 := metric_triangle x u y; have h2 := metric_triangle u v y.
    rewrite (metric_sym v y) in h2.
    rewrite lee_fin; lra.
rewrite compact_metric_diameter_finite_value lee_fin in hbound; exact hbound.
Qed.

(** Source for [hausdorff_diameter_lipschitz]: direct
    two-Lipschitz diameter assertion of 2.10.21,
    p. 183. It holds in every metric space. *)
Theorem hausdorff_diameter_lipschitz (R : realType) (X : metricType R)
    (C D : compact_metric_set X) :
  `|compact_metric_diameter C-compact_metric_diameter D|<=2*hausdorff_distance C D.
Proof.
have hCD := hausdorff_diameter_one_sided_bound C D.
have hDC := hausdorff_diameter_one_sided_bound D C.
rewrite (hausdorff_distance_symmetric_law (@hausdorff_distance_specification R X) D C) in hDC.
rewrite ler_norml; apply/andP; split; lra.
Qed.
