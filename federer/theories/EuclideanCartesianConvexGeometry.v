(** Federer (1969), 3.2.36, pp. 272--273:
    exact Cartesian geometry for the original
    bounded convex factors. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps EuclideanCartesianMap
  EuclideanCartesianBorel Hom TopologicalCartesianClosure HomeomorphicImageClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_cartesian_nonempty]: supporting
    nonempty original product in Federer 3.2.36,
    p. 272. The existing block pairing
    transports one point from each factor,
    including empty coordinate blocks. *)
Lemma euclidean_cartesian_nonempty (R:realType) n v (A:set (R_n R n)) (B:set (R_n R v)):
  A!=set0 ->B!=set0 ->euclidean_cartesian_set A B!=set0.
Proof.
move=>[a ha] [b hb]; exists (euclidean_block_join (a,b)).
change (A (euclidean_block_split (euclidean_block_join (a,b))).1 /\
  B (euclidean_block_split (euclidean_block_join (a,b))).2).
by rewrite euclidean_block_joinK; split.
Qed.

(** Source for [euclidean_cartesian_convex]: supporting
    convexity of the original Cartesian body
    in Federer 3.2.36, pp. 272--273.
    The two actual linear coordinate projections
    preserve every convex combination. No
    source measurability or compactness is used. *)
Lemma euclidean_cartesian_convex (R:realType) n v (A:set (R_n R n)) (B:set (R_n R v)):
  is_inner_convex A ->is_inner_convex B ->is_inner_convex (euclidean_cartesian_set A B).
Proof.
move=>hA hB x y [hxA hxB] [hyA hyB] t ht0 ht1.
change (A (hom_as_linear (@euclidean_first_block_map R n v) ((1-t)*:x+t*:y)) /\
  B (hom_as_linear (@euclidean_last_block_map R n v) ((1-t)*:x+t*:y))).
rewrite !linearD !linearZ.
split.
- exact:hA _ _ hxA hyA t ht0 ht1.
- exact:hB _ _ hxB hyB t ht0 ht1.
Qed.

(** Source for [euclidean_cartesian_closure]: supporting
    compact-closure reduction of the original
    convex product formula in Federer 3.2.36,
    pp. 272--273. Exact Cartesian closure
    in the existing product topology and
    the actual block homeomorphism give the
    identity on every pair of subsets;
    Borel or Suslin hypotheses are unnecessary. *)
Lemma euclidean_cartesian_closure (R:realType) n v
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (B:set (inner_metric_space (@euclidean_inner_productP R v))):
  @closure (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (euclidean_cartesian_set A B)=euclidean_cartesian_set (closure A) (closure B).
Proof.
rewrite !euclidean_cartesian_set_join_image.
rewrite (@homeomorphic_image_closure
  [the topologicalType of (inner_metric_space (@euclidean_inner_productP R n)*
    inner_metric_space (@euclidean_inner_productP R v))%type]
  (inner_metric_space (@euclidean_inner_productP R (n+v)))
  (@euclidean_block_join R n v) (@euclidean_block_split R n v) (A `*` B)
  (@euclidean_block_joinK R n v) (@euclidean_block_splitK R n v)
  (@euclidean_block_join_continuous R n v) (@euclidean_block_split_continuous R n v)).
by rewrite topological_cartesian_closure.
Qed.
