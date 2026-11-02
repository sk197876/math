(** Federer (1969), 2.10.3, p. 172: restricting generators to convex sets
    gives the same measure. Prove the comparison from unchanged metric
    diameter and exterior gauge under the abstract hull operator. The convex
    family is reused from 2.10.2, and its Caratheodory specification is
    independent of the unrestricted measure. Source context and the
    separate- affinity proof: ExteriorDiameterUP.v and
    ExteriorDiameterConvexity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  ConvexHull HausdorffLengthUP HausdorffConvexCovers ExteriorMeasureGauge ExteriorMeasureUP
  ExteriorMeasure ExteriorDiameterConvexity EuclideanConvexDiameter
  MetricDiameter CaratheodoryLimitUP CaratheodoryMeasure CaratheodoryFamilyReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_convex_exterior_diameter_measure]:
    independent convex-cover specification for the alternative
    measure of Federer 2.10.3, p. 172. Convexity
    refers to the actual Euclidean vector space, while
    the size restriction uses its given Euclidean metric. *)
Definition is_convex_exterior_diameter_measure (R : realType) (n m : nat)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :=
  is_caratheodory_limit
    (fun j : nonempty_convex_sets (R_n R n) =>
      (val j : set (inner_metric_space (@euclidean_inner_productP R n))))
    (fun j => exterior_diameter_cost m (val j)) nu.

(** Source for [exterior_convex_cover_agreement]: direct
    convex-cover equality in Federer 2.10.3, p. 172,
    using independently specified measures. The hull
    comparison preserves both size and normalized cost. *)
Theorem exterior_convex_cover_agreement (R : realType) (n m : nat)
    (mu nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  is_exterior_diameter_measure m mu -> is_convex_exterior_diameter_measure m nu ->
  forall A, mu A=nu A.
Proof.
move=> hm hn A.
have hc : nu A<=mu A.
  apply: (@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
    (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
    (nonempty_convex_sets (R_n R n))
    (fun j => (val j : set (inner_metric_space (@euclidean_inner_productP R n))))
    (fun j => (val j : set (inner_metric_space (@euclidean_inner_productP R n))))
    (fun j => exterior_diameter_cost m (val j))
    (fun j => exterior_diameter_cost m (val j)) mu nu hm hn _ _ A).
  - move=> j; exact: exterior_diameter_cost_nonnegative.
  - move=> j.
    have hne : @convex_hull R (R_n R n) (val j) !=set0.
      have [x hx] := set_valP j; exists x; exact: (@convex_hull_includes R (R_n R n) (val j) x hx).
    pose k : nonempty_convex_sets (R_n R n) :=
      @exist _ (fun B : set (R_n R n) => B \in [set B | B !=set0 /\ InnerConvex.is_inner_convex B])
        (@convex_hull R (R_n R n) (val j))
        (mem_set (conj hne (@convex_hull_convex R (R_n R n) (val j)))).
    exists k; split; first exact: (@convex_hull_includes R (R_n R n) (val j)).
    split.
    + change (@extended_metric_diameter R (inner_metric_space (@euclidean_inner_productP R n))
        (@convex_hull R (R_n R n) (val j))<=extended_metric_diameter (val j)).
      by rewrite euclidean_metric_diameter_convex_hull.
    + change (exterior_diameter_cost m (@convex_hull R (R_n R n) (val j))<=exterior_diameter_cost m (val j)).
      by rewrite exterior_diameter_cost_convex_hull.
have ha : mu A<=nu A.
  apply: (@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
    (nonempty_convex_sets (R_n R n))
    (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
    (fun j => (val j : set (inner_metric_space (@euclidean_inner_productP R n))))
    (fun j => (val j : set (inner_metric_space (@euclidean_inner_productP R n))))
    (fun j => exterior_diameter_cost m (val j))
    (fun j => exterior_diameter_cost m (val j)) nu mu hn hm _ _ A).
  - move=> j; exact: exterior_diameter_cost_nonnegative.
  - move=> j.
    pose k : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) :=
      @exist _ (fun B : set (inner_metric_space (@euclidean_inner_productP R n)) => B \in [set B | B !=set0])
        (val j) (mem_set (set_valP j).1).
    exists k; split; first by move=> x hx.
    by split.
by apply/eqP; rewrite eq_le ha hc.
Qed.

(** Source for [exterior_measure_convex_cover_specification]:
    direct assertion that the selected T^m satisfies
    the convex-cover construction of Federer 2.10.3,
    p. 172. The alternative infimum exists by the
    sealed general construction; equality is a theorem. *)
Theorem exterior_measure_convex_cover_specification (R : realType) (n m : nat) :
  is_convex_exterior_diameter_measure m (@exterior_diameter_measure R n m).
Proof.
pose S := fun j : nonempty_convex_sets (R_n R n) =>
  (val j : set (inner_metric_space (@euclidean_inner_productP R n))).
pose c := fun j : nonempty_convex_sets (R_n R n) => exterior_diameter_cost m (val j).
pose nu := caratheodory_measure S c.
have hn : is_convex_exterior_diameter_measure m nu := caratheodory_measure_specification S c.
have he : @exterior_diameter_measure R n m=nu.
  apply: funext=> A; exact (@exterior_convex_cover_agreement R n m _ _
    (@exterior_diameter_measure_specification R n m) hn A).
by rewrite he.
Qed.
