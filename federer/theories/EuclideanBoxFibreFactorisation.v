(** Federer (1969), 3.1.18, p. 230: F=f composed with g inverse
    is constant on each W-fibre and equals psi composed with r. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP
  NormFiniteLinearBound NormOpenDomainLaws NormLinearDomainLaws
  EuclideanBlockLinearMaps EuclideanProductBox NormAffineFibreConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Factorisation.
Variable R:realType.
Variables v l:nat.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Local Notation X:=(R_n R (v+l)).
Local Notation V:=(R_n R v).
Local Notation W:=(R_n R l).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R (v+l))).
Local Notation NW:=(inner_norm (@euclidean_inner_productP R l)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R (v+l))).
Local Notation hNW:=(inner_norm_real_norm (@euclidean_inner_productP R l)).
Local Notation p:=(@euclidean_first_block_map R v l).
Local Notation q:=(@euclidean_last_block_map R v l).
Local Notation i:=(@euclidean_first_injection_map R v l).
Local Notation j:=(@euclidean_last_injection_map R v l).

(** Source for [euclidean_box_fibre_factorisation]: the fibre-constancy
    conclusion F=psi r in Federer 3.1.18, p. 230, obtained from the
    zero derivative in complementary directions and convexity of W.
    Zero-dimensional blocks are included. *)
Theorem euclidean_box_fibre_factorisation (c:X) e (F:X->Y) (D:X->Hom X Y) :
  0<e ->
  (forall x, @euclidean_product_box R v l c e x ->
    has_norm_differential NX NY (@euclidean_product_box R v l c e) F x (D x)) ->
  (forall x, @euclidean_product_box R v l c e x -> forall w, D x (j w)=0) ->
  forall x, @euclidean_product_box R v l c e x -> F x=F (i (p x)+j (q c)).
Proof.
move=>he hD hzero x hx.
pose C:=@euclidean_product_box R v l c e.
pose W0:=fun w:W=>NW (w-q c)<e.
have hW:=@norm_open_ball_convex R W NW hNW (q c) e.
have hopen w (hw:W0 w):norm_domain_interior NW W0 w.
  exact (@norm_open_ball_domain_interior R W NW hNW (q c) e w hw).
have hj:=@norm_finite_linear_bounded R W X NW NX hNW hNX l
  (@coordinate_basis R l) (@coordinate_basisP R l) j.
have hmap w (hw:W0 w):C (i (p x)+j w).
  apply: (@euclidean_product_box_coordinates R v l c e (p x) w).2.
  exact: conj hx.1 hw.
have hkill w (hw:W0 w) z:D (i (p x)+j w) (j z)=0.
  exact: hzero _ (hmap w hw) z.
have hcenter:W0 (q c) by rewrite /W0 subrr inner_norm0.
have hh:=@norm_affine_fibre_constant R W X Y NW NX NY hNW hNX hNY W0 C j
  (i (p x)) F D hW hopen hj hmap hD hkill (q x) (q c) hx.2 hcenter.
have hd:=@euclidean_block_linear_decomposition R v l x.
exact (eq_trans (congr1 F hd) hh).
Qed.
End Factorisation.
