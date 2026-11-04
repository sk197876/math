(** Federer (1969), 3.2.47, p. 283: the explicit
    horizontal lift is linear in the original sphere tangent
    vector. Supporting the actual horizontal quotient and its
    r-th exterior Jacobian, without a chosen tangent frame. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP EuclideanRectangularAdjoint EuclideanRankOneInner SphericalHorizontalLift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_horizontal_lift_linear]: linearity
    of the actual skew horizontal lift supporting D Phi
    in 3.2.47, p. 283. It follows from the
    two rank-one terms and the public adjoint laws. *)
Lemma spherical_horizontal_lift_linear (R:realType) N
    (g:Hom (R_n R N) (R_n R N)) (c:R_n R N):
  linear (spherical_horizontal_lift g c).
Proof.
move=>a v w; apply:hom_ext=>x.
change (euclidean_inner_product x c*:(a*:v+w)-
  euclidean_inner_product x (euclidean_rectangular_adjoint g (a*:v+w))*:g c=
  a*:(euclidean_inner_product x c*:v-
    euclidean_inner_product x (euclidean_rectangular_adjoint g v)*:g c)+
  (euclidean_inner_product x c*:w-
    euclidean_inner_product x (euclidean_rectangular_adjoint g w)*:g c)).
have hAdj:euclidean_rectangular_adjoint g (a*:v+w)=
    a*:euclidean_rectangular_adjoint g v+euclidean_rectangular_adjoint g w by rewrite linearP.
rewrite hAdj (bilDr (inner_bilinear (@euclidean_inner_productP R N)))
  (bilZr (inner_bilinear (@euclidean_inner_productP R N))) scalerDr scalerDl
  scalerBr !scalerA [euclidean_inner_product x c*a]mulrC.
by rewrite opprD addrACA.
Qed.
