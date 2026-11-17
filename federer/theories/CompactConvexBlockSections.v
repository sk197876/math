(** The original compact convex sections in Federer
    (1969), 3.2.45, p. 279, under the existing
    Euclidean block identification of 2.6.5, p. 120. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanBlockCoordinates EuclideanBlockLinear ConcatenatedFamilies TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_section_compact]: supporting
    compactness of each original section in Federer
    3.2.45, p. 279. Intersect the compact K
    with the closed first-coordinate fibre, and project
    onto the second coordinate block. Exact inverse
    block laws identify its image with the stated
    section. Empty sections and either empty block
    are included. *)
Lemma euclidean_block_section_compact (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (y : inner_metric_space (@euclidean_inner_productP R m)) :
  compact K -> @compact (inner_metric_space (@euclidean_inner_productP R n))
    [set z | K (@euclidean_block_join R m n (y,z))].
Proof.
move=> hCompact.
pose X := inner_metric_space (@euclidean_inner_productP R (m+n)).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose Z := inner_metric_space (@euclidean_inner_productP R n).
pose p := fun x : X => (@euclidean_block_split R m n x).1.
pose q := fun x : X => (@euclidean_block_split R m n x).2.
have hP : continuous p.
  move=> x; exact: continuous_comp (@euclidean_block_split_continuous R m n x)
    (@first_projection_continuous Y Z (@euclidean_block_split R m n x)).
have hQ : continuous q.
  move=> x; exact: continuous_comp (@euclidean_block_split_continuous R m n x)
    (@second_projection_continuous Y Z (@euclidean_block_split R m n x)).
have hFibre : @closed X (p @^-1` [set y]).
  exact: (continuous_closedP p).1 hP _
    (compact_closed (@metric_hausdorff R Y) (@compact_set1 Y y)).
have hImage : q @` (K `&` p @^-1` [set y])=[set z | K (@euclidean_block_join R m n (y,z))].
  apply/seteqP; split=> z.
  - move=> [x [hx hp] <-].
    change (K (@euclidean_block_join R m n (y,q x))).
    change (p x=y) in hp; rewrite -hp.
    by rewrite /p /q -surjective_pairing euclidean_block_splitK.
  - move=> hz; exists (@euclidean_block_join R m n (y,z)).
    + split=> //; change ((@euclidean_block_split R m n (@euclidean_block_join R m n (y,z))).1=y).
      by rewrite euclidean_block_joinK.
    + by rewrite /q euclidean_block_joinK.
rewrite -hImage.
exact: continuous_compact (continuous_subspaceT hQ) (compact_closedI hCompact hFibre).
Qed.

(** Source for [euclidean_block_section_inner_convex]: supporting
    convexity of each original section in Federer
    3.2.45, p. 279. The first coordinate y
    stays fixed under each convex combination, and
    the second coordinates are the original ones.
    The existing coordinate evaluations prove the
    affine identity, including zero-dimensional blocks. *)
Lemma euclidean_block_section_inner_convex (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (y : inner_metric_space (@euclidean_inner_productP R m)) :
  is_inner_convex K -> @is_inner_convex R (R_n R n)
    [set z | K (@euclidean_block_join R m n (y,z))].
Proof.
move=> hConvex z w hz hw t ht0 ht1.
have h := hConvex _ _ hz hw t ht0 ht1.
have hJoin : @euclidean_block_join R m n (y,(1-t)*:z+t*:w)=
    (1-t)*:(@euclidean_block_join R m n (y,z))+t*:(@euclidean_block_join R m n (y,w)).
  apply: euclidean_block_vectors_ext.
  - move=> i; rewrite euclidean_block_join_left !ffunE ?euclidean_block_join_left ?concatenate_family_l.
    change (y i=(1-t)*y i+t*y i); ring.
  - move=> j; by rewrite euclidean_block_join_right !ffunE ?euclidean_block_join_right ?concatenate_family_r.
change (K (@euclidean_block_join R m n (y,(1-t)*:z+t*:w))).
by rewrite hJoin.
Qed.
