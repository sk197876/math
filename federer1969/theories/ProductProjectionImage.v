(** Federer (1969), 2.10.46, printed p. 203: p[f(S times T)]=q(T) for the
    common factors of f and the second-coordinate projection. The displayed
    equality uses the nonempty first factor (a positive-radius closed ball
    in the book). State that requirement explicitly for arbitrary S. Source
    context: EuclideanRightBlockProjection.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanSquaredProduct SquaredMetricProductLaws MetricProductRectangles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [product_projection_factor_image]: direct
    projected-image equality after the common-factor
    identity in 2.10.46, p. 203. The equality
    is proved for arbitrary nonempty S and arbitrary T;
    no compactness or measurability is used at this step. *)
Theorem product_projection_factor_image (R : realType) m n k
    (f : R_n R (m+n) -> R_n R (m+k))
    (p : R_n R (m+k) -> R_n R k) (q : R_n R n -> R_n R k)
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (T : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (forall x y, p (f (@euclidean_block_join R m n (x,y)))=q y) -> S !=set0 ->
  p @` (f @` (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) S T))=q @` T.
Proof.
move=> he [a ha].
apply/seteqP; split=> z.
- move=> [w [v [hS hT] <-] <-].
  exists ((@euclidean_block_split R m n v).2)=> //.
  have hh := he ((@euclidean_block_split R m n v).1) ((@euclidean_block_split R m n v).2).
  rewrite euclidean_block_splitK in hh; exact: esym hh.
- move=> [y hy <-].
  exists (f (@euclidean_block_join R m n (a,y))); last exact: he.
  exists (@euclidean_block_join R m n (a,y))=> //.
  exact: (metric_product_rectangle_pair
    (squared_metric_product_cartesian (euclidean_blocks_are_squared_metric_product R m n)) S T a y).2 (conj ha hy).
Qed.
