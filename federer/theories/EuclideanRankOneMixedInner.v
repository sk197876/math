(** Federer (1969), 3.2.28(3), printed pp. 265–266:
    pair the rank-one maps used in the adapted tangent
    bases. The actual Hilbert Hom product is that of
    1.7.9, p. 35, independently of its implementation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct CoordinateProjection InnerProductUP InnerProductLaws
  HomInner HomInnerCoordinates EuclideanHomInnerCharts EuclideanStiefelInnerSplitting
  EuclideanRankOneInner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_rank_one_mixed_inner_pairing]: the
    products of the w_i tensor v_j maps used for the
    orthonormal tangent bases in Federer 3.2.28(3),
    pp. 265–266. Both domain and target factors
    are paired in their actual inner products. *)
Theorem euclidean_rank_one_mixed_inner_pairing (R:realType) m n
    (w a:R_n R m) (v z:R_n R n):
  euclidean_hom_inner_product (euclidean_rank_one_hom w v) (euclidean_rank_one_hom a z)=
    euclidean_inner_product w a*euclidean_inner_product v z.
Proof.
rewrite /euclidean_hom_inner_product
  (@hom_inner_orthonormal_sum R (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    m (@coordinate_basis R m) (@coordinate_basisP R m)
    m (@coordinate_basis R m) (@coordinate_basisP R m)
    (@euclidean_coordinate_orthonormal_family R m)).
have hEntry i:euclidean_inner_product
    (euclidean_rank_one_hom w v (@coordinate_basis R m i))
    (euclidean_rank_one_hom a z (@coordinate_basis R m i))=
    w i*a i*euclidean_inner_product v z.
  change (euclidean_inner_product (euclidean_inner_product (@coordinate_basis R m i) w*:v)
    (euclidean_inner_product (@coordinate_basis R m i) a*:z)=w i*a i*euclidean_inner_product v z).
  rewrite (bilZl (inner_bilinear (@euclidean_inner_productP R n)))
    (bilZr (inner_bilinear (@euclidean_inner_productP R n)))
    (inner_symmetric (@euclidean_inner_productP R m) (@coordinate_basis R m i) w)
    (inner_symmetric (@euclidean_inner_productP R m) (@coordinate_basis R m i) a)
    !euclidean_inner_basis.
  exact:mulrA.
under eq_bigr do rewrite hEntry.
rewrite -mulr_suml; reflexivity.
Qed.
