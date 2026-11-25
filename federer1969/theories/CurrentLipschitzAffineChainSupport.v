(** Federer (1969), 4.1.14, pp. 371–372: the
    original affine chain has support in the exact
    union of segments over sptT. Derive this
    from the earlier interval-product support, open-restriction
    support and compact-image support. No support-coincidence
    theorem from 4.1.15 is used, and the
    original segment condition is only over sptT. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap LipschitzUP CurrentSpaces FlatCurrentsUP
  CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianSupportEquality
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  CurrentAffineHomotopyUP CurrentAffineHomotopySealed CurrentAffineHomotopyClass
  CurrentAffineSegmentHull CurrentLipschitzAffineNeighbourhood
  CurrentAffineNeighbourhoodProductFlat CurrentLipschitzAffineChainUP
  CurrentLipschitzAffineChainSealed CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentLipschitzAffineChainSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypothesis hFLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Hypothesis hBand:forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
  V ((1-t)*:f x+t*:g x).
Local Notation hull:=(@current_affine_segment_hull R h2 n nu m U hU f g T).
Local Notation H:=(@CurrentAffineHomotopy.value R n nu f g).

(** Source for [current_lipschitz_affine_chain_candidate_support]:
    every current satisfying the original independent
    affine-chain law has support in the original
    segment union of 4.1.13, p. 369,
    as used in Federer 4.1.14, pp. 371–372.
    No representation, normality or finite mass is assumed. *)
Theorem current_lipschitz_affine_chain_candidate_support
    (Q:@current_space R h2 nu V hV (1+m)%N):
  @is_current_lipschitz_affine_chain R h2 n nu m U V hU hV
    f g hFLocal hGLocal T Q->
  @current_support R h2 nu V hV (1+m)%N Q `<=` hull.
Proof.
move=>hQ.
have[A [hA [W [hW [hWU [hSupport hImage]]]]]]:=
  @current_lipschitz_affine_neighbourhood_exists R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand.
pose AT:=@current_homotopy_time_domain R A.
pose hAT:=@current_homotopy_time_domain_open R A hA.
pose AW:=@current_homotopy_product_domain R n A W.
pose hAW:=@current_cartesian_domain_open R 1%N n AT W hAT hW.
pose S:=@current_open_restriction R h2 n m W U hW hU hWU T.
pose interval:=@current_homotopy_time_segment R A hA h2.
pose product:=@current_affine_neighbourhood_product R h2 n m
  A hA U W hU hW hWU T.
pose hProduct:=@current_affine_neighbourhood_product_flat R h2 n m
  A hA U W hU hW hWU T hFlat hSupport.
have hQEqual:=hQ.2 A hA W hW hWU hSupport hImage hProduct.
have hImageSupport:=@current_flat_lipschitz_pushforward_support R h2 (1+n)%N nu
  (1+m)%N AW V hAW hV H
  (@current_affine_neighbourhood_image R n nu A W V f g hImage)
  (@current_affine_neighbourhood_local R n nu U W hW hWU f g
    hFLocal hGLocal A hA) product hProduct.
move=>y hy.
have hImageY:@current_support R h2 nu V hV (1+m)%N
    (@current_affine_neighbourhood_pushforward R h2 n nu m U V hU hV
      f g hFLocal hGLocal T A hA W hW hWU hImage hProduct) y.
  by rewrite -hQEqual.
have[z hz hzy]:=@hImageSupport y hImageY.
change (@current_support R h2 (1+n)%N AW hAW (1+m)%N
  (@CartesianCurrentProduct.value R h2 1%N n 1%N m AT W hAT hW interval S) z) in hz.
rewrite (@current_cartesian_support R h2 1%N n 1%N m
  AT W hAT hW interval S) in hz.
exists (@euclidean_one_project R (@euclidean_first_block_map R 1%N n z)),
  (@euclidean_last_block_map R 1%N n z);split.
- exact:(@current_homotopy_time_segment_support R A hA h2 _ hz.1).
- split.
  + exact:(@current_open_restriction_support_subset R h2 n m W U hW hU hWU
      T _ hz.2).
  + apply:(eq_trans _ hzy).
    apply:esym;exact:current_affine_homotopy_coordinates.
Qed.

(** Source for [current_lipschitz_affine_chain_support]: the
    actual opaque affine chain is supported in
    the exact original segment hull, Federer 4.1.14,
    pp. 371–372. All compact flat sources and
    support-only segment-image conditions are retained. *)
Theorem current_lipschitz_affine_chain_support:
  @current_support R h2 nu V hV (1+m)%N
    (@CurrentLipschitzAffineChain.value R h2 n nu m U V hU hV
      f g hFLocal hGLocal T hFlat hBand) `<=` hull.
Proof.
exact:(@current_lipschitz_affine_chain_candidate_support
  (@CurrentLipschitzAffineChain.value R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand)
  (@CurrentLipschitzAffineChain.laws R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand)).
Qed.
End CurrentLipschitzAffineChainSupport.
