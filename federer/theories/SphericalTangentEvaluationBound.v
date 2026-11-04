(** Federer (1969), 3.2.47, p. 283: evaluation
    has norm at most 2^(-1/2) on every actual
    orthogonal-group tangent. This supporting bound also applies to
    tangent planes of arbitrary rectifiable subsets, without a
    measurable-hull excess or exact-preimage tangent assumption. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm OrthogonalMaps EuclideanHomInnerCharts
  EuclideanGramDifferentialAlgebra SphericalHorizontalLift SphericalHorizontalSpace
  EuclideanStiefelHalfNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_tangent_evaluation_square_bound]: every
    tangent splits into its actual horizontal lift and a
    perpendicular vertical remainder, hence 2|w(c)|^2<=|w|^2;
    supporting the horizontal computation in 3.2.47, p. 283. *)
Theorem spherical_tangent_evaluation_square_bound (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)) (c:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  euclidean_inner_product c c= 1 ->euclidean_gram_differential g w=0 ->
  2*euclidean_inner_product (w c) (w c)<=euclidean_hom_inner_product w w.
Proof.
move=>hg hc hw.
pose p:=spherical_horizontal_lift g c (w c).
pose z:=w-p.
have hPerpendicular:=@spherical_gram_tangent_evaluation_perpendicular R N g w c hw.
have hp:=@spherical_horizontal_lift_tangent R N g c (w c) hg.
have hValue:p c=w c.
  exact (@spherical_horizontal_lift_evaluation R N g c (w c) hc hPerpendicular).
have hz:euclidean_gram_differential g z=0.
  exact (eq_trans (linB (hom_linear (euclidean_gram_differential g)) w p)
    (eq_trans (congr2 (fun a b:Hom (R_n R N) (R_n R N)=>a-b) hw hp)
      (subrr (0:Hom (R_n R N) (R_n R N))))).
have hZValue:z c=0.
  exact (eq_trans (linB (@hom_eval_linear R (R_n R N) (R_n R N) c) w p)
    (eq_trans (congr1 (fun a=>w c-a) hValue) (subrr (w c)))).
have hPZ:euclidean_hom_inner_product p z=0.
  rewrite /p (@spherical_horizontal_lift_pairing R N g z c (w c) hg hz) hZValue
    (bil0r (inner_bilinear (@euclidean_inner_productP R N))) mulr0; reflexivity.
have hSquare:euclidean_hom_inner_product p p= 2*euclidean_inner_product (w c) (w c).
  exact (@spherical_horizontal_lift_square R N g c (w c) hg hc hPerpendicular).
have hPair:euclidean_hom_inner_product p w-euclidean_hom_inner_product p p=0.
  exact (eq_trans (esym (bilBr (inner_bilinear (@euclidean_hom_inner_productP R N N)) p w p)) hPZ).
have hNonnegative:=inner_nonnegative (@euclidean_hom_inner_productP R N N) z.
rewrite /z (bilBl (inner_bilinear (@euclidean_hom_inner_productP R N N)) w p (w-p))
  (bilBr (inner_bilinear (@euclidean_hom_inner_productP R N N)) w w p)
  (bilBr (inner_bilinear (@euclidean_hom_inner_productP R N N)) p w p) in hNonnegative.
have hSymmetry:euclidean_hom_inner_product w p=euclidean_hom_inner_product p w.
  exact (@inner_symmetric R (Hom (R_n R N) (R_n R N)) _
    (@euclidean_hom_inner_productP R N N) w p).
change (is_true (0<=euclidean_hom_inner_product w w-euclidean_hom_inner_product w p-
  (euclidean_hom_inner_product p w-euclidean_hom_inner_product p p))) in hNonnegative.
rewrite hSymmetry in hNonnegative.
rewrite hSquare in hPair hNonnegative.
by nra.
Qed.

(** Source for [spherical_tangent_evaluation_norm_bound]: actual
    evaluation has norm at most 2^(-1/2) on every
    actual Gram tangent, supporting the unrestricted-source
    mass comparison in 3.2.47(3), p. 283. *)
Theorem spherical_tangent_evaluation_norm_bound (R:realType) N
    (g w:Hom (R_n R N) (R_n R N)) (c:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N) (@euclidean_inner_product R N) (hom_as_linear g) ->
  euclidean_inner_product c c= 1 ->euclidean_gram_differential g w=0 ->
  inner_norm (@euclidean_inner_productP R N) (w c)<=
    (Num.sqrt (2:R))^-1*inner_norm (@euclidean_hom_inner_productP R N N) w.
Proof.
move=>hg hc hw.
have hBound:=@spherical_tangent_evaluation_square_bound R N g w c hg hc hw.
have [hPositive hCoefficient]:=euclidean_stiefel_half_normalization R.
rewrite -(ler_sqr (inner_norm_nonnegative (@euclidean_inner_productP R N) (w c))
  (mulr_ge0 (ltW hPositive) (inner_norm_nonnegative (@euclidean_hom_inner_productP R N N) w)))
  exprMn !inner_norm_sqr.
have hMult:=ler_wpM2l (sqr_ge0 ((Num.sqrt (2:R))^-1)) hBound.
have hFactor:((Num.sqrt (2:R))^-1)^+2*(2*euclidean_inner_product (w c) (w c))=
    euclidean_inner_product (w c) (w c).
  rewrite expr2.
  have hRearrange:(Num.sqrt (2:R))^-1*(Num.sqrt (2:R))^-1*
      (2*euclidean_inner_product (w c) (w c))=
    (2*(Num.sqrt (2:R))^-1*(Num.sqrt (2:R))^-1)*euclidean_inner_product (w c) (w c) by ring.
  by rewrite hRearrange hCoefficient mul1r.
by rewrite hFactor in hMult.
Qed.
