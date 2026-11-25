(** Federer (1969), 2.10.29, pp. 194–195: the actual scalar pairing of the
    Euclidean plane is a homeomorphism. These supporting topology facts
    transport Borel regularity of the competing product measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanRealPlane
  TopologicalProductMaps MetricCartesianProductUP NormMetricScaleContinuity LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PlaneTopology.
Variable R : realType.
Local Notation L := (real_line_metric R).
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).

(** Source for [euclidean_real_plane_pair_continuous]: supporting
    forward homeomorphism property for the actual
    Cartesian identification in 2.10.29, pp. 194–195. *)
Lemma euclidean_real_plane_pair_continuous :
  continuous (fun p : L*L=>euclidean_real_plane_pair p.1 p.2).
Proof.
have hl : continuous (fun p : L*L=>euclidean_one_embed p.1).
  move=> p; exact: continuous_comp (@first_projection_continuous L L p) (@euclidean_one_embed_continuous R p.1).
have hr : continuous (fun p : L*L=>euclidean_one_embed p.2).
  move=> p; exact: continuous_comp (@second_projection_continuous L L p) (@euclidean_one_embed_continuous R p.2).
have hp := topological_pair_continuous hl hr.
move=> p; exact: continuous_comp (hp p) (@euclidean_block_join_continuous R 1 1 (euclidean_one_embed p.1,euclidean_one_embed p.2)).
Qed.

(** Source for [euclidean_real_plane_coordinates_continuous]: supporting
    inverse homeomorphism property for 2.10.29,
    pp. 194–195, from the two proved
    nonexpanding coordinate bounds. *)
Lemma euclidean_real_plane_coordinates_continuous :
  continuous (fun p : E 2=>(euclidean_real_plane_first p,euclidean_real_plane_second p)).
Proof.
apply: topological_pair_continuous.
- apply: (@metric_fixed_lipschitz_continuous R [the metricType R of E 2] [the metricType R of L]
    (@euclidean_real_plane_first R) 1 ler01)=> x y.
  exact: (metric_product_first_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 x y Logic.I Logic.I.
- apply: (@metric_fixed_lipschitz_continuous R [the metricType R of E 2] [the metricType R of L]
    (@euclidean_real_plane_second R) 1 ler01)=> x y.
  exact: (metric_product_second_nonexpanding (@euclidean_real_plane_is_metric_product R)).2 x y Logic.I Logic.I.
Qed.
End PlaneTopology.
