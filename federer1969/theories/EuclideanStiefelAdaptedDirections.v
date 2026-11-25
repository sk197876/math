(** Federer (1969), 3.2.28(3), printed p. 265:
    the skew and normal rank-one directions in the actual
    Stiefel tangent. The adapted orthonormal frames are
    parameters; no global frame construction defines the tangent. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws AdjointLaws OrthogonalMaps OrthonormalFamilies EuclideanRectangularAdjoint
  EuclideanGramDifferentialAlgebra EuclideanGramTangentAlgebra EuclideanStiefelTangentSplit
  EuclideanRankOneInner EuclideanRankOneMixedInner EuclideanHomInnerCharts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_stiefel_skew_direction]: the
    a_ij=2^(-1/2)(w_i tensor v_j-w_j tensor v_i)
    of Federer 3.2.28(3), p. 265. The
    normalization c is explicit until its scalar law
    is used in the orthonormality proof. *)
Definition euclidean_stiefel_skew_direction (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)) (e:'I_m->R_n R m) (c:R) i j:=
  c*:(euclidean_rank_one_hom (e i) (g (e j))-
    euclidean_rank_one_hom (e j) (g (e i))).

(** Source for [euclidean_stiefel_skew_direction_tangent]:
    the a_ij directions satisfy the actual Gram-kernel
    equation, Federer 3.2.28(3), p. 265,
    by the displayed tangent equations in part (1). *)
Theorem euclidean_stiefel_skew_direction_tangent (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)) (e:'I_m->R_n R m) c i j:
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (hom_as_linear g) ->
  euclidean_gram_differential g (euclidean_stiefel_skew_direction g e c i j)=0.
Proof.
move=>hG; apply:hom_ext=>y.
apply:(inner_vectors_ext (@euclidean_inner_productP R m))=>x.
rewrite hom_zeroE (bil0r (inner_bilinear (@euclidean_inner_productP R m)))
  euclidean_gram_differential_pairing.
change (euclidean_inner_product
    (c*:(euclidean_inner_product x (e i)*:g (e j)-euclidean_inner_product x (e j)*:g (e i))) (g y)+
  euclidean_inner_product (g x)
    (c*:(euclidean_inner_product y (e i)*:g (e j)-euclidean_inner_product y (e j)*:g (e i)))=0).
rewrite (bilZl (inner_bilinear (@euclidean_inner_productP R n)))
  (bilZr (inner_bilinear (@euclidean_inner_productP R n)))
  (bilBl (inner_bilinear (@euclidean_inner_productP R n)))
  (bilBr (inner_bilinear (@euclidean_inner_productP R n)))
  !(bilZl (inner_bilinear (@euclidean_inner_productP R n)))
  !(bilZr (inner_bilinear (@euclidean_inner_productP R n))) !hG
  (inner_symmetric (@euclidean_inner_productP R m) (e i) y)
  (inner_symmetric (@euclidean_inner_productP R m) (e j) y).
change (c*(euclidean_inner_product x (e i)*euclidean_inner_product y (e j)-
  euclidean_inner_product x (e j)*euclidean_inner_product y (e i))+
  c*(euclidean_inner_product y (e i)*euclidean_inner_product x (e j)-
  euclidean_inner_product y (e j)*euclidean_inner_product x (e i))=0).
ring.
Qed.

(** Source for [euclidean_stiefel_normal_direction_tangent]:
    the b_ij=w_i tensor v_j directions with v_j
    perpendicular to im g belong to Z(g), hence to
    the actual tangent, Federer 3.2.28(3), p. 265. *)
Theorem euclidean_stiefel_normal_direction_tangent (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)) w v:
  euclidean_rectangular_adjoint g v=0 ->
  euclidean_gram_differential g (euclidean_rank_one_hom w v)=0.
Proof.
move=>hV; apply:euclidean_stiefel_horizontal_kernel.
apply:hom_ext=>x.
change (euclidean_rectangular_adjoint g (euclidean_inner_product x w*:v)=0).
rewrite linearZ; change (euclidean_inner_product x w*:euclidean_rectangular_adjoint g v=0).
by rewrite hV scaler0.
Qed.

(** Source for [euclidean_stiefel_skew_direction_pairing]:
    the rank-one scalar-product calculation underlying the
    orthonormal a_ij family of Federer 3.2.28(3),
    p. 265. The formula retains arbitrary indices
    before using their strict ordering and normalization. *)
Theorem euclidean_stiefel_skew_direction_pairing (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)) (e:'I_m->R_n R m) c i j k l:
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (hom_as_linear g) ->
  euclidean_hom_inner_product (euclidean_stiefel_skew_direction g e c i j)
    (euclidean_stiefel_skew_direction g e c k l)=
  (2*c*c)*(euclidean_inner_product (e i) (e k)*euclidean_inner_product (e j) (e l)-
    euclidean_inner_product (e i) (e l)*euclidean_inner_product (e j) (e k)).
Proof.
move=>hG.
rewrite /euclidean_stiefel_skew_direction
  (bilZl (inner_bilinear (@euclidean_hom_inner_productP R m n)))
  (bilZr (inner_bilinear (@euclidean_hom_inner_productP R m n)))
  (bilBl (inner_bilinear (@euclidean_hom_inner_productP R m n)))
  !(bilBr (inner_bilinear (@euclidean_hom_inner_productP R m n)))
  !euclidean_rank_one_mixed_inner_pairing !hG.
change (c*(c*((euclidean_inner_product (e i) (e k)*euclidean_inner_product (e j) (e l)-
    euclidean_inner_product (e i) (e l)*euclidean_inner_product (e j) (e k))-
  (euclidean_inner_product (e j) (e k)*euclidean_inner_product (e i) (e l)-
    euclidean_inner_product (e j) (e l)*euclidean_inner_product (e i) (e k))))=
  (2*c*c)*(euclidean_inner_product (e i) (e k)*euclidean_inner_product (e j) (e l)-
    euclidean_inner_product (e i) (e l)*euclidean_inner_product (e j) (e k))).
ring.
Qed.
