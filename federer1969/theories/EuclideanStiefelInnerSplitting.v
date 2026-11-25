(** Federer (1969), 3.2.28(2), printed pp. 264–265:
    the horizontal and vertical summands are orthogonal for
    the actual Hom inner product; R_g(u)= g u is isometric.
    Proofs use the public orthonormal-sum law of 1.7.9. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  FiniteCoordinates CoordinateProjection EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm HomInner HomInnerCoordinates
  OrthogonalMaps OrthonormalFamilies EuclideanRectangularAdjoint
  EuclideanHomInnerCharts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_orthonormal_family]:
    standard orthonormal coordinates, 1.7.1, p. 28, used
    in the Hom computations of Federer 3.2.28, pp. 264–266. *)
Lemma euclidean_coordinate_orthonormal_family (R:realType) m:
  orthonormal_family (@euclidean_inner_product R m) (@coordinate_basis R m).
Proof. by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym. Qed.

(** Source for [euclidean_stiefel_horizontal_vertical_orthogonal]:
    h.(g u)= trace(h* g u)= 0 for h in Z(g), Federer
    3.2.28(2), p. 264. The equivalent orthonormal-sum
    computation avoids choosing a trace representation. *)
Theorem euclidean_stiefel_horizontal_vertical_orthogonal (R:realType) m n
    (g h:Hom (R_n R m) (R_n R n)) (u:Hom (R_n R m) (R_n R m)):
  hom_comp (euclidean_rectangular_adjoint g) h= 0 ->
  euclidean_hom_inner_product h (hom_comp g u)= 0.
Proof.
move=>hz.
rewrite /euclidean_hom_inner_product.
rewrite (@hom_inner_orthonormal_sum R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  (@euclidean_coordinate_orthonormal_family R m)).
apply:big1=>i _.
have hZ:=congr1 (fun f:Hom (R_n R m) (R_n R m)=>f (@coordinate_basis R m i)) hz.
change (euclidean_rectangular_adjoint g (h (@coordinate_basis R m i))=0) in hZ.
rewrite hom_compE (inner_symmetric (@euclidean_inner_productP R n))
  -euclidean_rectangular_adjoint_pairing.
by rewrite hZ (bil0r (inner_bilinear (@euclidean_inner_productP R m))).
Qed.

(** Source for [euclidean_stiefel_vertical_inner_isometry]: R_g
    is an isometry, Federer 3.2.28(2), p. 265. The product
    identity holds on the full endomorphism space, so its
    restriction to SO(m) needs no additional estimate. *)
Theorem euclidean_stiefel_vertical_inner_isometry (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  forall u v:Hom (R_n R m) (R_n R m),
    euclidean_hom_inner_product (hom_comp g u) (hom_comp g v)=
      euclidean_hom_inner_product u v.
Proof.
move=>hg u v.
rewrite /euclidean_hom_inner_product
  (@hom_inner_orthonormal_sum R (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    m (@coordinate_basis R m) (@coordinate_basisP R m)
    m (@coordinate_basis R m) (@coordinate_basisP R m)
    (@euclidean_coordinate_orthonormal_family R m))
  (@hom_inner_orthonormal_sum R (R_n R m) (R_n R m)
    (@euclidean_inner_product R m) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R m)
    m (@coordinate_basis R m) (@coordinate_basisP R m)
    m (@coordinate_basis R m) (@coordinate_basisP R m)
    (@euclidean_coordinate_orthonormal_family R m)).
apply:eq_bigr=>i _; rewrite !hom_compE; exact:hg.
Qed.

(** Source for [euclidean_stiefel_vertical_norm_isometry]:
    |g u|= |u| in the Hom norms, supporting the fibre
    isometry of Federer 3.2.28(2), p. 265. *)
Lemma euclidean_stiefel_vertical_norm_isometry (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  forall u:Hom (R_n R m) (R_n R m),
    inner_norm (@euclidean_hom_inner_productP R m n) (hom_comp g u)=
      inner_norm (@euclidean_hom_inner_productP R m m) u.
Proof.
move=>hg u; apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr; symmetry; exact:euclidean_stiefel_vertical_inner_isometry.
Qed.
