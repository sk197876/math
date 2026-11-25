(** Federer (1969), 4.1.14, pp. 371–372: the
    affine chain exists under the original segment
    condition on spt T alone. Its independent law
    retains every allowed time/source neighbourhood.
    Derive the neighbourhood and the flat product;
    uniqueness removes their choices before sealing. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces FlatCurrentsUP CurrentHomotopyUP CurrentHomotopyDomain
  CurrentCartesianDomain CurrentAffineHomotopySealed CurrentLipschitzAffineChainUP
  CurrentLipschitzAffineNeighbourhood CurrentAffineNeighbourhoodProductFlat
  CurrentLipschitzAffineNeighbourhoodIndependence CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzAffineChainExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypotheses (hFLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f)
  (hGLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g).
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Hypothesis hBand:forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
  V ((1-t)*:f x+t*:g x).
Local Notation Chain := (@is_current_lipschitz_affine_chain R h2 n nu m
  U V hU hV f g hFLocal hGLocal T).

(** Source for [current_lipschitz_affine_chain_exists]: the
    original affine interval-product image exists, Federer
    4.1.14, p. 372, with segment containment only
    over spt T. Every compact flat source is admitted. *)
Theorem current_lipschitz_affine_chain_exists :
  exists Q:@current_space R h2 nu V hV (1+m)%N,Chain Q.
Proof.
have [A [hA [W [hW [hWU [hSupport hImage]]]]]] :=
  @current_lipschitz_affine_neighbourhood_exists R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand.
pose hProduct := @current_affine_neighbourhood_product_flat R h2 n m
  A hA U W hU hW hWU T hFlat hSupport.
pose Q := @current_affine_neighbourhood_pushforward R h2 n nu m U V hU hV
  f g hFLocal hGLocal T A hA W hW hWU hImage hProduct.
exists Q; split.
- exact: (@CurrentFlatLipschitzPushforward.laws R h2 (1+n)%N nu (1+m)%N
    (@current_homotopy_product_domain R n A W) V
    (@current_cartesian_domain_open R 1%N n (@current_homotopy_time_domain R A)
      W (@current_homotopy_time_domain_open R A hA) hW) hV
    (@CurrentAffineHomotopy.value R n nu f g)
    (@current_affine_neighbourhood_image R n nu A W V f g hImage)
    (@current_affine_neighbourhood_local R n nu U W hW hWU f g hFLocal hGLocal A hA)
    (@current_affine_neighbourhood_product R h2 n m A hA U W hU hW hWU T)
    hProduct).1.
- move=> A1 hA1 W1 hW1 hW1U hSupport1 hImage1 hProduct1.
  exact: (@current_lipschitz_affine_neighbourhood_images_agree R h2 n nu m
    U V hU hV f g hFLocal hGLocal T hFlat A A1 W W1 hA hA1 hW hW1
    hWU hW1U hSupport hSupport1 hImage hImage1 hProduct hProduct1).
Qed.

(** Source for [current_lipschitz_affine_chain_unique]: every
    current satisfying the original neighbourhood law is
    the same affine chain, supporting Federer 4.1.14,
    pp. 371–372. The derived neighbourhood is hidden. *)
Theorem current_lipschitz_affine_chain_unique
    (Q P:@current_space R h2 nu V hV (1+m)%N) :
  Chain Q->Chain P->Q = P.
Proof.
move=> hQ hP.
have [A [hA [W [hW [hWU [hSupport hImage]]]]]] :=
  @current_lipschitz_affine_neighbourhood_exists R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand.
pose hProduct := @current_affine_neighbourhood_product_flat R h2 n m
  A hA U W hU hW hWU T hFlat hSupport.
exact: eq_trans (hQ.2 A hA W hW hWU hSupport hImage hProduct)
  (esym (hP.2 A hA W hW hWU hSupport hImage hProduct)).
Qed.
End CurrentLipschitzAffineChainExistence.
