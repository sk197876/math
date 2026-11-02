(** Federer (1969), 3.2.28(3), printed pp. 265–266:
    split the source into im alpha and the last adapted
    unit normal. These exact laws support the spherical
    fibre identification of the forgetful map. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws OrthogonalMaps AdjointCriteria
  EuclideanRectangularAdjoint EuclideanHyperplaneNormalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_hyperplane_decomposition]: the source
    adapted basis in Federer 3.2.28(3), p. 265,
    splits each vector into its alpha component and its
    e_m component. Both components are actual scalar
    products and adjoints, with no chosen coordinates. *)
Theorem euclidean_hyperplane_decomposition (R:realType) k
    (alpha:Hom (R_n R k) (R_n R k.+1)) w:
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->forall x,
    x=alpha (euclidean_rectangular_adjoint alpha x)+euclidean_inner_product x w*:w.
Proof.
move=>hA hW x.
pose p:=euclidean_rectangular_adjoint alpha.
have hCan:cancel alpha p:=(orthogonal_iff_adjoint_left_inverse
  (@euclidean_inner_productP R k) (euclidean_rectangular_adjoint_pairing alpha)).1 hA.
pose z:=x-alpha (p x).
have hz:p z=0.
  rewrite /z linearB.
  change (p x-p (alpha (p x))=0).
  by rewrite hCan subrr.
have hSpan:=hyperplane_normal_span hW hz.
have hCross:euclidean_inner_product (alpha (p x)) w=0.
  rewrite -euclidean_rectangular_adjoint_pairing
    (hyperplane_normal_perpendicular hW).
  by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R k))).
have hCoeff:euclidean_inner_product z w=euclidean_inner_product x w.
  by rewrite /z (bilBl (inner_bilinear (@euclidean_inner_productP R k.+1))) hCross subr0.
rewrite hCoeff in hSpan.
have hRec:x=alpha (p x)+z by rewrite /z addrC subrK.
rewrite hSpan in hRec; exact hRec.
Qed.

(** Source for [euclidean_hyperplane_inner_decomposition]:
    orthogonality of the two adapted source components,
    supporting the fibre-isometry argument in Federer
    3.2.28(3), pp. 265–266. *)
Theorem euclidean_hyperplane_inner_decomposition (R:realType) k
    (alpha:Hom (R_n R k) (R_n R k.+1)) w:
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->is_euclidean_hyperplane_normal alpha w ->forall x y,
  euclidean_inner_product x y=
    euclidean_inner_product (euclidean_rectangular_adjoint alpha x)
      (euclidean_rectangular_adjoint alpha y)+
    euclidean_inner_product x w*euclidean_inner_product y w.
Proof.
move=>hA hW x y.
have hSplit:=euclidean_hyperplane_decomposition hA hW x.
rewrite {1}hSplit (bilDl (inner_bilinear (@euclidean_inner_productP R k.+1)))
  (bilZl (inner_bilinear (@euclidean_inner_productP R k.+1)))
  -euclidean_rectangular_adjoint_pairing
  (inner_symmetric (@euclidean_inner_productP R k.+1) w y).
reflexivity.
Qed.
