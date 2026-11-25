(** Federer (1969), 2.10.4, p. 172, final displayed equality: C^1=H^1. Use
    the proved closed convex alternative, where the actual gauge is the
    diameter. The closure of a convex hull replaces any nonempty Hausdorff
    generator with the same diameter. Empty convex generators can be
    replaced by a zero-cost singleton when comparing to the nonempty
    Hausdorff family. Source context and intermediate geometry:
    ProjectedVolumeDegreeOne.v and ProjectionClosedOpenComparison.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  ConvexHull EuclideanConvexDiameter InnerConvexNeighbourhoods
  ProjectedVolumeGauge ProjectedVolumeDegreeOne ProjectionMeasureUP ProjectionMeasure
  ProjectionClosedOpenComparison MetricDiameterUP MetricDiameter MetricDiameterMaps MetricDiameterClosure
  HausdorffLengthUP HausdorffLength HausdorffMeasure HausdorffLengthCompatibility
  CaratheodoryFamilyReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_convex_projection_one_hausdorff_agreement]:
    supporting comparison for the final equality of
    Federer 2.10.4, p. 172, using independently
    specified closed convex and Hausdorff constructions.
    The chosen-point singleton only replaces empty
    generators of zero diameter and zero cost. *)
Theorem closed_convex_projection_one_hausdorff_agreement (R : realType) (n : nat)
    (mu nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  (1<=n)%N -> is_closed_convex_projection_measure 1 mu -> is_hausdorff_length nu ->
  forall A, mu A=nu A.
Proof.
move=> hn hm hh A.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have hlo : mu A<=nu A.
  apply: (@caratheodory_family_replacement R E (@nonempty_metric_sets R E)
    (closed_convex_euclidean_sets R n) (fun j => val j) (fun j => val j)
    (fun j => extended_metric_diameter (val j)) (fun j => projected_volume_gauge 1 (val j))
    nu mu hh hm _ _ A).
  - move=> j; exact: projected_volume_gauge_nonnegative.
  - move=> j.
    pose C : set E := @closure E (@convex_hull R (R_n R n) (val j)).
    have hc : closed C := @closed_closure E (@convex_hull R (R_n R n) (val j)).
    have hv : @is_inner_convex R (R_n R n) C := @inner_convex_closure R (R_n R n)
      (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
      (@convex_hull R (R_n R n) (val j)) (@convex_hull_convex R (R_n R n) (val j)).
    pose k : closed_convex_euclidean_sets R n :=
      @exist _ (fun B : set E => B \in [set B : set E | closed B /\ @is_inner_convex R (R_n R n) B])
        C (mem_set (conj hc hv)).
    have hdiam : extended_metric_diameter C=extended_metric_diameter (val j).
      by rewrite /C extended_metric_diameter_closure euclidean_metric_diameter_convex_hull.
    exists k; split.
    + move=> x hx; apply: subset_closure; exact: (@convex_hull_includes R (R_n R n) (val j) x hx).
    + split; first by change (extended_metric_diameter C<=extended_metric_diameter (val j)); rewrite hdiam.
      change (projected_volume_gauge 1 C<=extended_metric_diameter (val j)).
      by rewrite (@projected_volume_one_convex_diameter R n C hn hv) hdiam.
have hhi : nu A<=mu A.
  apply: (@caratheodory_family_replacement R E (closed_convex_euclidean_sets R n)
    (@nonempty_metric_sets R E) (fun j => val j) (fun j => val j)
    (fun j => projected_volume_gauge 1 (val j)) (fun j => extended_metric_diameter (val j))
    mu nu hm hh _ _ A).
  - move=> j; exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
  - move=> j; case: (pselect (val j !=set0))=> [hne|hno].
    + pose k : @nonempty_metric_sets R E :=
        @exist _ (fun B : set E => B \in [set B : set E | B !=set0]) (val j) (mem_set hne).
      exists k; split; first by move=> x hx.
      split=> //.
      change (extended_metric_diameter (val j)<=projected_volume_gauge 1 (val j)).
      by rewrite (@projected_volume_one_convex_diameter R n (val j) hn (set_valP j).2).
    + have he : val j=set0.
        apply/seteqP; split=> x hx; last by [].
        exfalso; apply: hno; by exists x.
      pose k : @nonempty_metric_sets R E :=
        @exist _ (fun B : set E => B \in [set B : set E | B !=set0]) [set (0:E)%R]
          (mem_set (ex_intro _ 0%R (erefl 0%R))).
      exists k; split; first by rewrite he=> x.
      split.
      * change (extended_metric_diameter [set (0:E)%R]<=extended_metric_diameter (val j)).
        rewrite extended_metric_diameter_singleton; exact: metric_diameter_nonnegative (extended_metric_diameter_specification (val j)).
      * change (extended_metric_diameter [set (0:E)%R]<=projected_volume_gauge 1 (val j)).
        by rewrite extended_metric_diameter_singleton he (@projected_volume_gauge_empty R n 1 hn).
by apply/eqP; rewrite eq_le hlo hhi.
Qed.

(** Source for [caratheodory_projection_one_hausdorff_measure]:
    direct final equality C^1=H^1 in Federer 2.10.4,
    p. 172, for the independently selected actual
    measures on arbitrary subsets of R^n. *)
Theorem caratheodory_projection_one_hausdorff_measure (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (1<=n)%N -> @caratheodory_projection_measure R n 1 A=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 1 A.
Proof.
move=> hn; rewrite hausdorff_measure_one_length.
exact (@closed_convex_projection_one_hausdorff_agreement R n _ _ hn
  (@caratheodory_projection_closed_cover_specification R n 1 hn)
  (@hausdorff_length_specification R (inner_metric_space (@euclidean_inner_productP R n))) A).
Qed.
