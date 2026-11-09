(** Federer (1969), 3.4.4, p. 318: the
    actual Euclidean product with one original scalar Cantor factor. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanMetricProduct EuclideanRealPlane
  RealMetricBackground MetricCartesianProductUP EuclideanCoordinateTopology TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LastScalar.
Variable R:realType.
Variable n:nat.
Local Notation E k:=(inner_metric_space (@euclidean_inner_productP R k)).
Local Notation L:=(real_line_metric R).

(** Source for [euclidean_scalar_last_pair]: append the
    original scalar Cantor coordinate in the product of
    3.4.4, p. 318, through the canonical
    block identification of 2.6.5, p. 120. *)
Definition euclidean_scalar_last_pair (x:E n) (t:L):E (n+1):=
  euclidean_block_join (x,euclidean_one_embed t).

(** Source for [euclidean_scalar_last_first]: the actual
    original preceding coordinate block, 3.4.4, p. 318. *)
Definition euclidean_scalar_last_first (z:E (n+1)):E n:=
  (@euclidean_block_split R n 1 z).1.

(** Source for [euclidean_scalar_last_second]: the actual
    original appended scalar coordinate, 3.4.4, p. 318. *)
Definition euclidean_scalar_last_second (z:E (n+1)):L:=
  euclidean_one_project (@euclidean_block_split R n 1 z).2.

(** Source for [euclidean_scalar_last_metric_product]: both
    projections of the actual product are nonexpanding, as
    used in the 2.10.27 appeal in 3.4.4,
    p. 318. The canonical inverse laws include n=0. *)
Lemma euclidean_scalar_last_metric_product:
  is_metric_cartesian_product euclidean_scalar_last_pair
    euclidean_scalar_last_first euclidean_scalar_last_second.
Proof.
constructor.
- move=>x t;by rewrite /euclidean_scalar_last_first /euclidean_scalar_last_pair euclidean_block_joinK.
- move=>x t;by rewrite /euclidean_scalar_last_second /euclidean_scalar_last_pair
    euclidean_block_joinK euclidean_one_embedK.
- move=>z;rewrite /euclidean_scalar_last_pair /euclidean_scalar_last_first /euclidean_scalar_last_second
    euclidean_one_projectK;exact:euclidean_block_splitK.
- split;first exact:ler01.
  move=>z w _ _.
  exact:(metric_product_first_nonexpanding (@euclidean_blocks_are_metric_product R n 1)).2 z w Logic.I Logic.I.
- split;first exact:ler01.
  move=>z w _ _;rewrite mul1r /euclidean_scalar_last_second -euclidean_one_project_distance.
  have h:=(metric_product_second_nonexpanding (@euclidean_blocks_are_metric_product R n 1)).2 z w Logic.I Logic.I.
  by rewrite mul1r in h.
Qed.

(** Source for [euclidean_scalar_last_pair_continuous]: the
    actual pairing is continuous for the original topologies,
    supporting product measurability in 3.4.4, p. 318. *)
Lemma euclidean_scalar_last_pair_continuous:
  continuous (fun z:E n*L=>euclidean_scalar_last_pair z.1 z.2).
Proof.
apply:euclidean_map_continuous=>i.
case:(split_ordP i)=>[j ->|j ->].
- have hEqual:(fun z:E n*L=>euclidean_scalar_last_pair z.1 z.2 (lshift 1 j))=
      (fun z:E n*L=>z.1 j).
    apply:funext=>z;exact:euclidean_block_join_left.
  rewrite hEqual=>z.
  exact:continuous_comp (@first_projection_continuous (E n) L z)
    (@euclidean_coordinate_continuous R n j z.1).
- have hEqual:(fun z:E n*L=>euclidean_scalar_last_pair z.1 z.2 (rshift n j))=
      (fun z:E n*L=>z.2).
    by apply:funext=>z;rewrite /euclidean_scalar_last_pair euclidean_block_join_right
      /euclidean_one_embed ffunE.
  rewrite hEqual;exact:second_projection_continuous.
Qed.

(** Source for [euclidean_scalar_last_first_continuous]: continuity
    of the actual preceding coordinate block, supporting
    closed original product sets in 3.4.4, p. 318. *)
Lemma euclidean_scalar_last_first_continuous:continuous euclidean_scalar_last_first.
Proof.
apply:euclidean_map_continuous=>i.
have hEqual:(fun z:E (n+1)=>euclidean_scalar_last_first z i)=
    (fun z:E (n+1)=>z (lshift 1 i)).
  by apply:funext=>z;rewrite /euclidean_scalar_last_first /euclidean_block_split ffunE.
rewrite hEqual;exact:euclidean_coordinate_continuous.
Qed.

(** Source for [euclidean_scalar_last_second_continuous]: continuity
    of the actual appended scalar coordinate, supporting
    closed original product sets in 3.4.4, p. 318. *)
Lemma euclidean_scalar_last_second_continuous:continuous euclidean_scalar_last_second.
Proof.
have hEqual:euclidean_scalar_last_second=(fun z:E (n+1)=>z (rshift n ord0)).
  by apply:funext=>z;rewrite /euclidean_scalar_last_second /euclidean_one_project
    /euclidean_block_split ffunE.
rewrite hEqual;exact:euclidean_coordinate_continuous.
Qed.
End LastScalar.
