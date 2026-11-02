(** Federer (1969), 3.2.28(3), printed p. 266:
    changing only the last adapted frame vector is
    isometric for the Hilbert Hom metric of 1.7.9,
    p. 35. The supporting rank-one pairing is
    computed from the public orthonormal-sum law. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct CoordinateProjection InnerProductUP InnerProductLaws InnerNorm
  HomInner HomInnerCoordinates EuclideanHomInnerCharts EuclideanStiefelInnerSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_rank_one_hom]: the rank-one
    change x to (x.e_m)v in a fibre of S,
    supporting Federer 3.2.28(3), p. 266,
    and the rank-one maps of 1.4.5, p. 21. *)
Definition euclidean_rank_one_hom (R:realType) m n (w:R_n R m) (v:R_n R n):
    Hom (R_n R m) (R_n R n).
Proof.
apply:(@HomMap R (R_n R m) (R_n R n) (fun x=>euclidean_inner_product x w*:v)).
apply/asboolP=>c x y.
by rewrite (bilDl (inner_bilinear (@euclidean_inner_productP R m)))
  (bilZl (inner_bilinear (@euclidean_inner_productP R m))) scalerDl scalerA.
Defined.

(** Source for [euclidean_rank_one_inner_pairing]: the Hom
    inner product of the two last-vector changes is
    |e_m|^2(v.z), supporting the fibre isometry in
    Federer 3.2.28(3), p. 266, by 1.7.9, p. 35. *)
Theorem euclidean_rank_one_inner_pairing (R:realType) m n
    (w:R_n R m) (v z:R_n R n):
  euclidean_hom_inner_product (euclidean_rank_one_hom w v) (euclidean_rank_one_hom w z)=
    euclidean_inner_product w w*euclidean_inner_product v z.
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
    (euclidean_rank_one_hom w z (@coordinate_basis R m i))=
    w i*w i*euclidean_inner_product v z.
  change (euclidean_inner_product (euclidean_inner_product (@coordinate_basis R m i) w*:v)
    (euclidean_inner_product (@coordinate_basis R m i) w*:z)=w i*w i*euclidean_inner_product v z).
  rewrite (bilZl (inner_bilinear (@euclidean_inner_productP R n)))
    (bilZr (inner_bilinear (@euclidean_inner_productP R n)))
    (inner_symmetric (@euclidean_inner_productP R m)) euclidean_inner_basis.
  exact:mulrA.
under eq_bigr do rewrite hEntry.
rewrite -mulr_suml; reflexivity.
Qed.

(** Source for [euclidean_unit_rank_one_norm]: changing a
    unit normal fibre vector changes the Hom element by
    exactly the same distance, Federer 3.2.28(3), p. 266.
    The result uses the Hilbert Hom norm, with no
    replacement by its operator norm. *)
Theorem euclidean_unit_rank_one_norm (R:realType) m n
    (w:R_n R m) (v:R_n R n):
  euclidean_inner_product w w= 1 ->
  inner_norm (@euclidean_hom_inner_productP R m n) (euclidean_rank_one_hom w v)=
    inner_norm (@euclidean_inner_productP R n) v.
Proof.
move=>hw; apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr; symmetry.
by rewrite euclidean_rank_one_inner_pairing hw mul1r.
Qed.
