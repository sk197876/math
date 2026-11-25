(** Federer (1969), 4.1.14, pp. 371–372:
    two derived open affine-homotopy neighbourhoods give
    the same original chain. Compare them on the
    intersection of their time intervals and source sets,
    using exact interval-product restriction and the
    original flat-image source-neighbourhood law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP
  CurrentSpaces CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentOpenRestrictionTransitive CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentAffineHomotopySealed CurrentLipschitzAffineChainUP
  CurrentAffineNeighbourhoodProductFlat CurrentFlatSupportNeighbourhoodRestriction
  CurrentLipschitzCompactImage FlatCurrentsUP
  CurrentFlatTimeProductImageNeighbourhood CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzAffineNeighbourhoodIndependence.
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
Local Notation H := (@CurrentAffineHomotopy.value R n nu f g).
Local Notation Product := (fun A hA W hW hWU =>
  @current_affine_neighbourhood_product R h2 n m A hA U W hU hW hWU T).
Local Notation OpenProduct := (fun A hA W hW =>
  @current_cartesian_domain_open R 1%N n (@current_homotopy_time_domain R A)
    W (@current_homotopy_time_domain_open R A hA) hW).
Local Notation FlatProduct := (fun A hA W hW hWU =>
  @is_flat_current R h2 (1+n)%N (1+m)%N
    (@current_homotopy_product_domain R n A W) (OpenProduct A hA W hW)
    (Product A hA W hW hWU)).
Local Notation Image := (fun A hA W hW hWU hBand hP =>
  @current_affine_neighbourhood_pushforward R h2 n nu m
    U V hU hV f g hFLocal hGLocal T A hA W hW hWU hBand hP).

(** Source for [current_lipschitz_affine_nested_neighbourhoods]:
    one original affine chain is unchanged by shrinking
    its time/source neighbourhood, supporting Federer 4.1.14,
    pp. 371–372. Actual current restriction handles the
    product; equality merely on support is not used. *)
Theorem current_lipschitz_affine_nested_neighbourhoods
    (A B:set R) (W0 W1:set X)
    (hA:@is_homotopy_parameter_interval R A)
    (hB:@is_homotopy_parameter_interval R B)
    (hW0:forall x,W0 x->norm_domain_interior NX W0 x)
    (hW1:forall x,W1 x->norm_domain_interior NX W1 x)
    (hW0U:forall x,W0 x->U x) (hW1U:forall x,W1 x->U x)
    (hBA:forall t,B t->A t) (hW1W0:forall x,W1 x->W0 x)
    (hSupport:@current_support R h2 n U hU m T `<=` W1)
    (hBand0:forall t x,A t->W0 x->V ((1-t)*:f x+t*:g x))
    (hBand1:forall t x,B t->W1 x->V ((1-t)*:f x+t*:g x))
    (hP0:FlatProduct A hA W0 hW0 hW0U)
    (hP1:FlatProduct B hB W1 hW1 hW1U) :
  Image A hA W0 hW0 hW0U hBand0 hP0=
  Image B hB W1 hW1 hW1U hBand1 hP1.
Proof.
pose S0 := @current_open_restriction R h2 n m W0 U hW0 hU hW0U T.
have hSupport0 : @current_support R h2 n U hU m T `<=` W0.
  move=> x hx; exact: @hW1W0 x (@hSupport x hx).
have [hS0 _] := @flat_current_support_neighbourhood_restriction
  R h2 n m U W0 hU hW0 hW0U T hFlat hSupport0.
have [K0 hK0] := hS0.
have hCompact0 := @flat_supported_current_compact R h2 n m W0 hW0 K0 S0 hK0.
have hSupportS0 : @current_support R h2 n W0 hW0 m S0 `<=` W1.
  move=> x hx; apply: hSupport.
  exact: (@current_open_restriction_support_subset R h2 n m W0 U
    hW0 hU hW0U T x hx).
have hTransitive := @current_open_restriction_transitive R h2 n m W1 W0 U
  hW1 hW0 hU hW1W0 hW0U hW1U T.
pose BT := @current_homotopy_time_domain R B.
pose hBT := @current_homotopy_time_domain_open R B hB.
pose timeB := @current_homotopy_time_segment R B hB h2.
pose Small := @CartesianCurrentProduct.value R h2 1%N n 1%N m BT W1 hBT hW1
  timeB (@current_open_restriction R h2 n m W1 W0 hW1 hW0 hW1W0 S0).
have hSmallEquality : Small=Product B hB W1 hW1 hW1U.
  by rewrite /Small hTransitive.
have hSmallFlat : @is_flat_current R h2 (1+n)%N (1+m)%N
    (@current_homotopy_product_domain R n B W1) (OpenProduct B hB W1 hW1) Small.
  by rewrite hSmallEquality.
pose hImage0 := @current_affine_neighbourhood_image R n nu A W0 V f g hBand0.
pose hImage1 := @current_affine_neighbourhood_image R n nu B W1 V f g hBand1.
pose hLocal0 := @current_affine_neighbourhood_local R n nu U W0 hW0 hW0U
  f g hFLocal hGLocal A hA.
pose hLocal1 := @current_affine_neighbourhood_local R n nu U W1 hW1 hW1U
  f g hFLocal hGLocal B hB.
have hFirst := @current_flat_time_product_image_neighbourhood R h2 n nu m
  A B W0 W1 V hA hB hW0 hW1 hV hBA hW1W0 H
  hImage0 hImage1 hLocal0 hLocal1 S0 hCompact0 hSupportS0 hP0 hSmallFlat.
have hSecond := @current_flat_lipschitz_pushforward_congruence R h2 (1+n)%N nu
  (1+m)%N (@current_homotopy_product_domain R n B W1) V
  (OpenProduct B hB W1 hW1) hV H hImage1 hLocal1
  Small (Product B hB W1 hW1 hW1U) hSmallFlat hP1 hSmallEquality.
exact: eq_trans hFirst hSecond.
Qed.

(** Source for [current_lipschitz_affine_neighbourhood_images_agree]:
    compare every two original affine support-neighbourhood
    images through their time/source intersection, supporting
    the well-defined chain of Federer 4.1.14, pp. 371–372.
    Empty source intersections are included. *)
Theorem current_lipschitz_affine_neighbourhood_images_agree
    (A0 A1:set R) (W0 W1:set X)
    (hA0:@is_homotopy_parameter_interval R A0)
    (hA1:@is_homotopy_parameter_interval R A1)
    (hW0:forall x,W0 x->norm_domain_interior NX W0 x)
    (hW1:forall x,W1 x->norm_domain_interior NX W1 x)
    (hW0U:forall x,W0 x->U x) (hW1U:forall x,W1 x->U x)
    (hSupport0:@current_support R h2 n U hU m T `<=` W0)
    (hSupport1:@current_support R h2 n U hU m T `<=` W1)
    (hBand0:forall t x,A0 t->W0 x->V ((1-t)*:f x+t*:g x))
    (hBand1:forall t x,A1 t->W1 x->V ((1-t)*:f x+t*:g x))
    (hP0:FlatProduct A0 hA0 W0 hW0 hW0U)
    (hP1:FlatProduct A1 hA1 W1 hW1 hW1U) :
  Image A0 hA0 W0 hW0 hW0U hBand0 hP0=
  Image A1 hA1 W1 hW1 hW1U hBand1 hP1.
Proof.
pose B := A0 `&` A1.
have hB : @is_homotopy_parameter_interval R B.
  constructor.
  - exact: openI (homotopy_parameter_open hA0) (homotopy_parameter_open hA1).
  - move=> s t u hs ht hu; split.
    + exact: (@homotopy_parameter_between R A0 hA0 s t u hs.1 ht.1 hu).
    + exact: (@homotopy_parameter_between R A1 hA1 s t u hs.2 ht.2 hu).
  - exact: conj (homotopy_parameter_zero hA0) (homotopy_parameter_zero hA1).
  - exact: conj (homotopy_parameter_one hA0) (homotopy_parameter_one hA1).
pose W2 := W0 `&` W1.
have hW2 : forall x,W2 x->norm_domain_interior NX W2 x.
  move=> x hx.
  apply: (@norm_domain_interior_neighbourhood R X NX hNX W2 x).2.
  exact: filterI
    ((@norm_domain_interior_neighbourhood R X NX hNX W0 x).1 (@hW0 x hx.1))
    ((@norm_domain_interior_neighbourhood R X NX hNX W1 x).1 (@hW1 x hx.2)).
pose hW2U := fun x (hx:W2 x) => @hW0U x hx.1.
have hSupport2 : @current_support R h2 n U hU m T `<=` W2.
  move=> x hx; exact: conj (@hSupport0 x hx) (@hSupport1 x hx).
pose hBand2 := fun t x (ht:B t) (hx:W2 x) => @hBand0 t x ht.1 hx.1.
pose hP2 := @current_affine_neighbourhood_product_flat R h2 n m B hB U W2
  hU hW2 hW2U T hFlat hSupport2.
have hFirst := @current_lipschitz_affine_nested_neighbourhoods A0 B W0 W2
  hA0 hB hW0 hW2 hW0U hW2U (fun t ht => ht.1) (fun x hx => hx.1)
  hSupport2 hBand0 hBand2 hP0 hP2.
have hSecond := @current_lipschitz_affine_nested_neighbourhoods A1 B W1 W2
  hA1 hB hW1 hW2 hW1U hW2U (fun t ht => ht.2) (fun x hx => hx.2)
  hSupport2 hBand1 hBand2 hP1 hP2.
exact: eq_trans hFirst (esym hSecond).
Qed.
End CurrentLipschitzAffineNeighbourhoodIndependence.
