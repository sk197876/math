(** Federer (1969), 3.2.47, p. 283: supporting actual
    horizontal lift for D Phi(g)w=w(c). Its tangent
    equation, exact evaluation, Hilbert length and pairing are
    proved directly from the actual rank-one operators. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws AdjointLaws InnerNorm OrthogonalMaps EuclideanRectangularAdjoint
  EuclideanOrthogonalAdjointInverse EuclideanHomInnerCharts EuclideanRankOneInner
  EuclideanRankOneMixedInner EuclideanRankOneOperatorPairing
  EuclideanGramDifferentialAlgebra EuclideanGramTangentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_horizontal_lift]: the actual skew
    rank-one lift of a tangent vector to the sphere,
    supporting W(g) and D Phi(g) in 3.2.47,
    p. 283. This is a formula in public linear
    and adjoint operations, with no chosen auxiliary frame. *)
Definition spherical_horizontal_lift (R:realType) N
    (g:Hom (R_n R N) (R_n R N)) (c v:R_n R N):=
  euclidean_rank_one_hom c v-
    euclidean_rank_one_hom (euclidean_rectangular_adjoint g v) (g c).

(** Source for [spherical_horizontal_lift_tangent]: the actual
    lift satisfies the Gram tangent equation of 3.2.28,
    p. 263, supporting the horizontal calculation in
    3.2.47, p. 283. *)
Theorem spherical_horizontal_lift_tangent (R:realType) N
    (g:Hom (R_n R N) (R_n R N)) (c v:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  euclidean_gram_differential g (spherical_horizontal_lift g c v)=0.
Proof.
move=>hg; apply:hom_ext=>y; apply:(inner_vectors_ext (@euclidean_inner_productP R N))=>x.
rewrite hom_zeroE (bil0r (inner_bilinear (@euclidean_inner_productP R N)))
  euclidean_gram_differential_pairing.
change (euclidean_inner_product
    (euclidean_inner_product x c*:v-euclidean_inner_product x (euclidean_rectangular_adjoint g v)*:g c) (g y)+
  euclidean_inner_product (g x)
    (euclidean_inner_product y c*:v-euclidean_inner_product y (euclidean_rectangular_adjoint g v)*:g c)=0).
rewrite (bilBl (inner_bilinear (@euclidean_inner_productP R N)))
  (bilBr (inner_bilinear (@euclidean_inner_productP R N)))
  !(bilZl (inner_bilinear (@euclidean_inner_productP R N)))
  !(bilZr (inner_bilinear (@euclidean_inner_productP R N)))
  !hg (inner_symmetric (@euclidean_inner_productP R N) v (g y))
  -!euclidean_rectangular_adjoint_pairing
  (inner_symmetric (@euclidean_inner_productP R N) c y).
change (euclidean_inner_product x c*euclidean_inner_product y (euclidean_rectangular_adjoint g v)-
  euclidean_inner_product x (euclidean_rectangular_adjoint g v)*euclidean_inner_product y c+
  (euclidean_inner_product y c*euclidean_inner_product x (euclidean_rectangular_adjoint g v)-
   euclidean_inner_product y (euclidean_rectangular_adjoint g v)*euclidean_inner_product x c)=0).
ring.
Qed.

(** Source for [spherical_horizontal_lift_evaluation]: for an
    actual unit c and v perpendicular to g(c), the
    original D Phi sends the lift exactly to v,
    supporting surjectivity in 3.2.47, p. 283. *)
Theorem spherical_horizontal_lift_evaluation (R:realType) N
    (g:Hom (R_n R N) (R_n R N)) (c v:R_n R N):
  euclidean_inner_product c c= 1 ->euclidean_inner_product (g c) v=0 ->
  spherical_horizontal_lift g c v c=v.
Proof.
move=>hc hv.
change (euclidean_inner_product c c*:v-
  euclidean_inner_product c (euclidean_rectangular_adjoint g v)*:g c=v).
by rewrite hc euclidean_rectangular_adjoint_pairing hv scale1r scale0r subr0.
Qed.

(** Source for [spherical_horizontal_lift_square]: the lift
    magnifies squared lengths by two, hence D Phi has
    horizontal scale 2^(-1/2), 3.2.47, p. 283.
    The equality is in the actual Hilbert Hom metric. *)
Theorem spherical_horizontal_lift_square (R:realType) N
    (g:Hom (R_n R N) (R_n R N)) (c v:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  euclidean_inner_product c c= 1 ->euclidean_inner_product (g c) v=0 ->
  euclidean_hom_inner_product (spherical_horizontal_lift g c v) (spherical_horizontal_lift g c v)=
    2*euclidean_inner_product v v.
Proof.
move=>hg hc hv.
have hCross:euclidean_inner_product c (euclidean_rectangular_adjoint g v)=0.
  by rewrite euclidean_rectangular_adjoint_pairing hv.
have hNorm:euclidean_inner_product (euclidean_rectangular_adjoint g v)
    (euclidean_rectangular_adjoint g v)=euclidean_inner_product v v.
  exact (@euclidean_orthogonal_adjoint_orthogonal R N g hg v v).
rewrite /spherical_horizontal_lift
  (bilBl (inner_bilinear (@euclidean_hom_inner_productP R N N)))
  !(bilBr (inner_bilinear (@euclidean_hom_inner_productP R N N)))
  !euclidean_rank_one_mixed_inner_pairing hg hc hNorm hCross.
have hCrossReverse:euclidean_inner_product (euclidean_rectangular_adjoint g v) c=0.
  by rewrite (inner_symmetric (@euclidean_inner_productP R N)) hCross.
rewrite hCrossReverse; ring.
Qed.

(** Source for [spherical_horizontal_lift_pairing]: the lift's
    pairing with every actual Gram tangent w is twice
    v.w(c); this identifies the printed orthogonal complement
    W(g) without assuming a horizontal splitting, 3.2.47,
    p. 283. *)
Theorem spherical_horizontal_lift_pairing (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)) (c v:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  euclidean_gram_differential g w=0 ->
  euclidean_hom_inner_product (spherical_horizontal_lift g c v) w=
    2*euclidean_inner_product v (w c).
Proof.
move=>hg hw.
have hPair:=@euclidean_gram_differential_pairing R N N g w
  (euclidean_rectangular_adjoint g v) c.
rewrite hw hom_zeroE (bil0r (inner_bilinear (@euclidean_inner_productP R N)))
  (euclidean_orthogonal_adjoint_cancel_reverse hg)
  (inner_symmetric (@euclidean_inner_productP R N)
    (w (euclidean_rectangular_adjoint g v)) (g c)) in hPair.
rewrite /spherical_horizontal_lift
  (bilBl (inner_bilinear (@euclidean_hom_inner_productP R N N)))
  !euclidean_rank_one_operator_pairing.
have hCancel:euclidean_inner_product (g c) (w (euclidean_rectangular_adjoint g v))=
    -euclidean_inner_product v (w c).
  by nra.
rewrite hCancel; ring.
Qed.
