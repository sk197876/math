(** Original open vertical-ball sections in Federer
    (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLinearMaps EuclideanBlockCoordinates VectorSetSum EuclideanVerticalBallSumSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_vertical_open_ball_image]: supporting
    the exact original open vertical ball T in
    Federer 3.2.45, p. 279. Apply the proved
    closed-ball image identity at each original point's
    norm. Its closed bound remains strictly below
    r, giving both open-ball inclusions. No new
    coordinate or projection argument is assumed.
    Either empty coordinate block is retained. *)
Lemma euclidean_vertical_open_ball_image (R : realType) m n (r : R) :
  (@euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then 0 else 1)) @`
    [set x | inner_norm (@euclidean_inner_productP R (m+n)) x<r]=
  (fun z : R_n R n => @euclidean_block_join R m n (0,z)) @`
    [set z | inner_norm (@euclidean_inner_productP R n) z<r].
Proof.
pose D := @euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then 0 else 1).
apply/seteqP; split=> w.
- move=> [x hx <-].
  have hClosed : (D @` [set z | inner_norm (@euclidean_inner_productP R (m+n)) z<=
      inner_norm (@euclidean_inner_productP R (m+n)) x]) (D x).
    exists x=> //; exact: lexx.
  rewrite /D euclidean_vertical_ball_image in hClosed.
  have [z hz hEqual] := hClosed; exists z=> //.
  exact: le_lt_trans hz hx.
- move=> [z hz <-].
  have hClosed : ((fun v : R_n R n => @euclidean_block_join R m n (0,v)) @`
      [set v | inner_norm (@euclidean_inner_productP R n) v<=
        inner_norm (@euclidean_inner_productP R n) z]) (@euclidean_block_join R m n (0,z)).
    exists z=> //; exact: lexx.
  rewrite -euclidean_vertical_ball_image in hClosed.
  have [x hx hEqual] := hClosed; exists x=> //.
  exact: le_lt_trans hx hz.
Qed.

(** Source for [euclidean_vertical_open_ball_sum_section]: direct
    original section identity in the first Fubini
    display of Federer 3.2.45, p. 279. Use
    the proved original open-ball image and the
    generic vertical-sum section law. Arbitrary original
    K, empty sections and both empty blocks remain. *)
Theorem euclidean_vertical_open_ball_sum_section (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (y : inner_metric_space (@euclidean_inner_productP R m)) (r : R) :
  [set z | (vector_set_sum K
    ((@euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then 0 else 1)) @`
      [set x | inner_norm (@euclidean_inner_productP R (m+n)) x<r]))
      (@euclidean_block_join R m n (y,z))]=
  vector_set_sum [set z | K (@euclidean_block_join R m n (y,z))]
    [set z | inner_norm (@euclidean_inner_productP R n) z<r].
Proof. rewrite euclidean_vertical_open_ball_image; exact: euclidean_vertical_sum_section. Qed.
