(** Federer (1969), 2.10.27, pp. 190–191: Euclidean Cartesian geometry
    supporting the sharp spherical section inequality. The actual block
    joining and splitting from 2.6.5, p. 120, realize the abstract product
    laws. Squared norms split orthogonally and both projections are
    nonexpanding. These are proved consequences of the existing Euclidean
    inner-product interface; no replacement norm or metric is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  ConcatenatedFamilies InnerNorm InnerNormedTopology EuclideanBlockCoordinates EuclideanBlockLinear MetricCartesianProductUP LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_join_squared_norm]: supporting
    Pythagorean identity in the ball-section computation
    of 2.10.27, pp. 190–191. Both coordinate
    blocks may have dimension zero. *)
Lemma euclidean_block_join_squared_norm (R : realType) m n
    (p : inner_metric_space (@euclidean_inner_productP R m)*
      inner_metric_space (@euclidean_inner_productP R n)) :
  `|euclidean_block_join p|^+2=`|p.1|^+2+`|p.2|^+2.
Proof.
by rewrite !inner_norm_topologyE !inner_norm_sqr euclidean_block_join_inner.
Qed.

(** Source for [euclidean_block_join_difference]: supporting
    translation of the ball centre in 2.10.27,
    p. 190. This is the difference law of
    the existing linear block identification. *)
Lemma euclidean_block_join_difference (R : realType) m n
    (p q : inner_metric_space (@euclidean_inner_productP R m)*
      inner_metric_space (@euclidean_inner_productP R n)) :
  euclidean_block_join (p-q)=euclidean_block_join p-euclidean_block_join q.
Proof.
apply: euclidean_block_vectors_ext.
- move=> i; by rewrite euclidean_block_join_left !ffunE ?euclidean_block_join_left ?concatenate_family_l.
- move=> i; by rewrite euclidean_block_join_right !ffunE ?euclidean_block_join_right ?concatenate_family_r.
Qed.

(** Source for [euclidean_block_squared_distance]: supporting
    squared-distance formula for Euclidean ball sections
    in 2.10.27, pp. 190–191, from the
    actual block joining and splitting laws. *)
Lemma euclidean_block_squared_distance (R : realType) m n
    (p q : inner_metric_space (@euclidean_inner_productP R (m+n))) :
  mdist p q^+2=mdist (euclidean_block_split p).1 (euclidean_block_split q).1^+2+
    mdist (euclidean_block_split p).2 (euclidean_block_split q).2^+2.
Proof.
rewrite !inner_metric_normE.
rewrite -(euclidean_block_splitK q) -(euclidean_block_splitK p)
  -euclidean_block_join_difference euclidean_block_join_squared_norm.
by rewrite !euclidean_block_joinK.
Qed.

(** Source for [euclidean_blocks_are_metric_product]: supporting
    actual Euclidean realization of the product hypotheses
    in 2.10.27, p. 190. Projection bounds one
    include empty blocks; the pairing and projections
    are the pre-existing coordinate maps. *)
Theorem euclidean_blocks_are_metric_product (R : realType) m n :
  is_metric_cartesian_product (fun y z=>@euclidean_block_join R m n (y,z))
    (fun p=>(@euclidean_block_split R m n p).1)
    (fun p=>(@euclidean_block_split R m n p).2).
Proof.
constructor.
- move=> y z; by rewrite euclidean_block_joinK.
- move=> y z; by rewrite euclidean_block_joinK.
- exact: euclidean_block_splitK.
- split; first exact: ler01.
  move=> p q _ _; rewrite mul1r.
  rewrite -ler_sqr ?nnegrE ?mdist_ge0 // (@euclidean_block_squared_distance R m n p q) lerDl; exact: sqr_ge0.
- split; first exact: ler01.
  move=> p q _ _; rewrite mul1r.
  rewrite -ler_sqr ?nnegrE ?mdist_ge0 // (@euclidean_block_squared_distance R m n p q) lerDr; exact: sqr_ge0.
Qed.
