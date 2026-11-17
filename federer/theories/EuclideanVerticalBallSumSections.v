(** The actual vertical-ball sections used by Fubini
    in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLinearMaps EuclideanBlockCoordinates EuclideanPrefixStretchBlock VectorSetSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_vertical_ball_image]: supporting
    the original vertical ball T in Federer 3.2.45,
    p. 279. Zeroing the first m coordinates of
    the original closed radius-r ambient ball gives
    exactly the zero-first-block inclusion of the
    original second-block ball. The proved norm and
    block identities supply both inclusions, retaining
    either empty block and every real radius. *)
Lemma euclidean_vertical_ball_image (R : realType) m n (r : R) :
  (@euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then 0 else 1)) @`
    [set x | inner_norm (@euclidean_inner_productP R (m+n)) x<=r]=
  (fun z : R_n R n => @euclidean_block_join R m n (0,z)) @`
    [set z | inner_norm (@euclidean_inner_productP R n) z<=r].
Proof.
apply/seteqP; split=> w.
- move=> [x hx <-].
  exists (@euclidean_block_split R m n x).2.
  + change (is_true (inner_norm (@euclidean_inner_productP R n) (@euclidean_block_split R m n x).2<=r)).
    apply: le_trans (@euclidean_block_right_norm_bound R m n
      (@euclidean_block_split R m n x).1 (@euclidean_block_split R m n x).2) _.
    by rewrite euclidean_block_splitK.
  + have hFoot := @euclidean_prefix_stretch_block R m n 0
      (@euclidean_block_split R m n x).1 (@euclidean_block_split R m n x).2.
    rewrite euclidean_block_splitK scale0r in hFoot.
    exact: esym hFoot.
- move=> [z hz <-].
  exists (@euclidean_block_join R m n (0,z)).
  + change (is_true (inner_norm (@euclidean_inner_productP R (m+n))
      (@euclidean_block_join R m n (0,z))<=r)).
    by rewrite euclidean_block_zero_first_norm.
  + by rewrite euclidean_prefix_stretch_block scale0r.
Qed.

(** Source for [euclidean_vertical_sum_section]: supporting
    exact section operation in Federer 3.2.45, p. 279.
    An arbitrary original vertical increment fixes the
    first coordinate. The section of the actual sum
    is the original section plus the increment set.
    Empty sources and both empty blocks are included. *)
Theorem euclidean_vertical_sum_section (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (y : inner_metric_space (@euclidean_inner_productP R m))
    (B : set (R_n R n)) :
  [set z | (vector_set_sum K
    ((fun w : R_n R n => @euclidean_block_join R m n (0,w)) @` B))
      (@euclidean_block_join R m n (y,z))]=
  vector_set_sum [set z | K (@euclidean_block_join R m n (y,z))] B.
Proof.
apply/seteqP; split=> z.
- move=> /vector_set_sum_membership [a [b [ha [[v hv <-] hEqual]]]].
  have hIdentity : a+@euclidean_block_join R m n (0,v)=
      @euclidean_block_join R m n
        ((@euclidean_block_split R m n a).1,(@euclidean_block_split R m n a).2+v).
    rewrite -{1}(@euclidean_block_splitK R m n a); exact: euclidean_block_vertical_increment.
  have hCoordinates := congr1 (@euclidean_block_split R m n) hEqual.
  rewrite hIdentity !euclidean_block_joinK in hCoordinates.
  have hFirst : (@euclidean_block_split R m n a).1=y := esym (congr1 fst hCoordinates).
  have hSecond : (@euclidean_block_split R m n a).2+v=z := esym (congr1 snd hCoordinates).
  apply/vector_set_sum_membership; exists (@euclidean_block_split R m n a).2,v.
  split.
  + change (K (@euclidean_block_join R m n (y,(@euclidean_block_split R m n a).2))).
    by rewrite -hFirst -surjective_pairing euclidean_block_splitK.
  + by split.
- move=> /vector_set_sum_membership [u [v [hu [hv ->]]]].
  have hVertical : ((fun w : R_n R n => @euclidean_block_join R m n (0,w)) @` B)
      (@euclidean_block_join R m n (0,v)) by exists v.
  have hOriginal : K (@euclidean_block_join R m n (y,u)) := hu.
  have hSum := vector_set_sum_contains hOriginal hVertical.
  by rewrite euclidean_block_vertical_increment in hSum.
Qed.

(** Source for [euclidean_vertical_ball_sum_section]: supporting
    exact section identity in the first Fubini display
    of Federer 3.2.45, p. 279. A vertical
    ball increment fixes the original first coordinate.
    Its section is therefore the original section
    of K plus the original second-block ball.
    Arbitrary K, empty sections and both empty
    coordinate blocks are retained. *)
Theorem euclidean_vertical_ball_sum_section (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (y : inner_metric_space (@euclidean_inner_productP R m)) (r : R) :
  [set z | (vector_set_sum K
    ((@euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then 0 else 1)) @`
      [set x | inner_norm (@euclidean_inner_productP R (m+n)) x<=r]))
      (@euclidean_block_join R m n (y,z))]=
  vector_set_sum [set z | K (@euclidean_block_join R m n (y,z))]
    [set z | inner_norm (@euclidean_inner_productP R n) z<=r].
Proof. rewrite euclidean_vertical_ball_image; exact: euclidean_vertical_sum_section. Qed.
