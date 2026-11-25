(** Federer (1969), 3.2.47, p. 283: supporting
    Hilbert Hom pairing of a rank-one operator with an arbitrary
    operator. It derives the horizontal and vertical splitting
    directly from the inner-product formula of 1.7.9, p. 35. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct CoordinateProjection EuclideanCoordinateTopology InnerProductUP InnerProductLaws
  HomInner HomInnerCoordinates EuclideanHomInnerCharts EuclideanStiefelInnerSplitting EuclideanRankOneInner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_rank_one_operator_pairing]: the actual
    Hilbert pairing (w tensor v).h=v.h(w), by
    1.7.9, p. 35, supporting the horizontal calculation
    for D Phi in 3.2.47, p. 283. *)
Theorem euclidean_rank_one_operator_pairing (R:realType) m n
    (w:R_n R m) (v:R_n R n) (h:Hom (R_n R m) (R_n R n)):
  euclidean_hom_inner_product (euclidean_rank_one_hom w v) h=
    euclidean_inner_product v (h w).
Proof.
have hExpansion:h w=\sum_i w i*:h (@coordinate_basis R m i).
  rewrite -{1}(euclidean_coordinate_expansion w) linear_sum.
  apply:eq_bigr=>i _; exact:linearZ.
rewrite /euclidean_hom_inner_product
  (@hom_inner_orthonormal_sum R (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    m (@coordinate_basis R m) (@coordinate_basisP R m)
    m (@coordinate_basis R m) (@coordinate_basisP R m)
    (@euclidean_coordinate_orthonormal_family R m)) hExpansion.
rewrite (big_morph (fun z=>euclidean_inner_product v z)
  (linD ((inner_bilinear (@euclidean_inner_productP R n)).2 v))
  (lin0 ((inner_bilinear (@euclidean_inner_productP R n)).2 v))).
apply:eq_bigr=>i _.
change (euclidean_inner_product
  (euclidean_inner_product (@coordinate_basis R m i) w*:v) (h (@coordinate_basis R m i))=
  euclidean_inner_product v (w i*:h (@coordinate_basis R m i))).
rewrite (bilZl (inner_bilinear (@euclidean_inner_productP R n)))
  (bilZr (inner_bilinear (@euclidean_inner_productP R n)))
  (inner_symmetric (@euclidean_inner_productP R m) (@coordinate_basis R m i) w)
  euclidean_inner_basis; reflexivity.
Qed.
