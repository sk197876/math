(** Supporting Federer (1969), 2.10.47, p. 204: the coordinate range of a
    compact set is a closed interval whose length is bounded by its
    diameter. Applied to the closure of a small covering set, these extrema
    select at most two grid cells per coordinate. Only general compactness
    and the Euclidean coordinate nonexpansion are used. Source context:
    DyadicCubeGridUP.v *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanCoordinateMetric EuclideanCoordinateTopology CompactMaximum MetricDiameter MetricDiameterUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_euclidean_coordinate_extremes]: supporting
    attained coordinate range in the small-set covering
    argument of 2.10.47, p. 204. The range
    length is bounded by any finite diameter bound. *)
Theorem compact_euclidean_coordinate_extremes (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (i : 'I_n) (d : R) :
  compact S -> S!=set0 -> (extended_metric_diameter S<=d%:E)%E ->
  exists l u, [/\ S l, S u,
    (forall x, S x -> l i<=x i<=u i) & u i-l i<=d].
Proof.
move=> hS hne hd.
have hf := @euclidean_coordinate_continuous R n i.
have hn : continuous (fun x : inner_metric_space (@euclidean_inner_productP R n)=>(-x i : R^o)).
  move=> x; exact: continuousN (hf x).
have [u [hu hmax]] := @continuous_compact_maximum R _ S (fun x=>(x i : R^o)) hne hS hf.
have [l [hl hmin]] := @continuous_compact_maximum R _ S (fun x=>(-x i : R^o)) hne hS hn.
exists l,u; split=> //.
- move=> x hx; apply/andP; split; last exact: hmax x hx.
  have hh := hmin x hx; by rewrite lerN2 in hh.
- have hcoord := @euclidean_coordinate_nonexpanding R n i u l.
  rewrite real_line_metric_distanceE in hcoord.
  have hdist := @metric_diameter_upper R _ S _ (extended_metric_diameter_specification S) u l hu hl.
  have hbound := le_trans hdist hd; rewrite lee_fin in hbound.
  exact: le_trans (ler_norm _) (le_trans hcoord hbound).
Qed.
