(** Federer (1969), 4.1.9, p. 363: the endpoint
    products become fixed-time pushforwards under h.
    Reuse delta_t times T=epsilon_t#T from 4.1.8,
    p. 362, the composite-proper pushforward law of
    4.1.7, p. 359, and the proved current congruence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces CurrentDirac
  CurrentProperSupport CurrentProperSupportMapAgreement CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianPointInclusion CurrentCartesianPointInclusionProper CurrentCartesianPointProduct
  CurrentCompositeProperness CurrentPushforwardSealed CurrentPushforwardCongruence CurrentPushforwardComposition
  CurrentPushforwardMapAgreement SmoothFormPullbackComposition CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentHomotopyCylinder CurrentHomotopySliceClass CurrentHomotopySliceProper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopyPointProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Variable T:@current_space R h2 n U hU j.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T.
Variable t:R.
Hypothesis hBand:0<=t<=1.
Local Notation z := (@euclidean_one_embed R t).
Local Notation slice := (@current_homotopy_slice_map R n nu h t).
Local Notation slice_image := (@current_homotopy_band_slice_image R n nu A U V f g h geometry t hBand).
Local Notation slice_class := (@current_smooth_homotopy_slice_class R n nu A U V f g h hHomotopy t
  (@current_homotopy_closed_time_band R A hInterval t hBand)).
Local Notation slice_proper := (@current_homotopy_slice_proper R h2 n nu j A U V f g h geometry T
  t hBand hProper).

(** Source for [current_homotopy_time_point_member]: each
    original closed-band time gives a point in the
    actual open time domain, supporting the endpoint
    products in Federer 4.1.9, p. 363. *)
Lemma current_homotopy_time_point_member:AT z.
Proof.
change (A (@euclidean_one_project R z));rewrite euclidean_one_embedK.
exact:(@current_homotopy_closed_time_band R A hInterval t hBand).
Qed.
Local Notation inclusion := (@current_cartesian_point_inclusion R 1%N n z).
Local Notation inclusion_image := (fun x hx=>@current_cartesian_point_inclusion_image R 1%N n AT U
  z current_homotopy_time_point_member x hx).
Local Notation inclusion_class := (@current_cartesian_point_inclusion_smooth R 1%N n U hU z).
Local Notation composite := (fun x:X=>h (inclusion x)).
Local Notation composite_image := (@current_smooth_composite_image R n (1+n)%N nu U AU V
  inclusion h inclusion_image image).
Local Notation composite_class := (@current_smooth_composite_class R n (1+n)%N nu U AU
  inclusion h inclusion_image inclusion_class hHomotopy.2).

(** Source for [current_homotopy_point_composite_proper]:
    h composed with epsilon_t is proper on spt T
    for each original closed-band time, supporting
    Federer 4.1.9, p. 363. This is the proved
    slice properness with the same map values. *)
Lemma current_homotopy_point_composite_proper:
  @is_current_proper_on_support R h2 n nu j U hU V T composite composite_image.
Proof.
exact:(@current_proper_support_map_agreement R h2 n nu j U V hU T slice composite
  slice_image composite_image (fun x (_:U x)=>erefl (slice x)) slice_proper).
Qed.
Local Notation proper_data := (@current_composite_support_properness R h2 n (1+n)%N nu j U AU V
  hU inclusion h inclusion_image image inclusion_class hHomotopy.2 T current_homotopy_point_composite_proper).
Local Notation included := (@CurrentPushforward.value R h2 n (1+n)%N j U AU hU hAU
  T inclusion inclusion_image inclusion_class proper_data.1).
Local Notation included_proper := (@current_composite_pushed_support_proper R h2 n (1+n)%N nu j
  U AU V hU hAU inclusion h inclusion_image image inclusion_class hHomotopy.2 T
  current_homotopy_point_composite_proper).
Local Notation point_product := (@CartesianCurrentProduct.value R h2 1%N n 0%N j AT U hAT hU
  (@dirac_current R h2 1%N AT hAT z) T).

(** Source for [current_homotopy_point_product_identified]:
    the actual delta_t times T is the point-inclusion
    pushforward also with the properness proof supplied
    by composition, supporting Federer 4.1.9, p. 363,
    by the original 4.1.8 point-product identity. *)
Lemma current_homotopy_point_product_identified:point_product=included.
Proof.
apply:(eq_trans (@current_cartesian_point_product R h2 1%N n j AT U hAT hU z
  current_homotopy_time_point_member T)).
exact:(@current_pushforward_current_congruence R h2 n (1+n)%N j U AU hU hAU
  inclusion inclusion_image inclusion_class T T _ proper_data.1 (erefl T)).
Qed.

(** Source for [current_homotopy_point_product_proper]:
    h is proper on the original endpoint-product
    support, supporting its actual pushforward in
    Federer 4.1.9, p. 363. The original cylinder
    hypothesis alone supplies this restriction. *)
Theorem current_homotopy_point_product_proper:
  @is_current_proper_on_support R h2 (1+n)%N nu j AU hAU V point_product h image.
Proof.
rewrite current_homotopy_point_product_identified;exact:included_proper.
Qed.

(** Source for [current_homotopy_point_product_pushforward]:
    h#(delta_t times T)=(h_t)#T, supporting the two
    endpoint terms of the original current homotopy
    formula in Federer 4.1.9, p. 363. Both sides
    are the actual currents; no compactness or
    integration representation of T is assumed. *)
Theorem current_homotopy_point_product_pushforward:
  @CurrentPushforward.value R h2 (1+n)%N nu j AU V hAU hV point_product h image hHomotopy.2
    current_homotopy_point_product_proper=
  @CurrentPushforward.value R h2 n nu j U V hU hV T slice slice_image slice_class slice_proper.
Proof.
have hPoint:=@current_pushforward_current_congruence R h2 (1+n)%N nu j AU V hAU hV h image
  hHomotopy.2 point_product included current_homotopy_point_product_proper included_proper
  current_homotopy_point_product_identified.
apply:(eq_trans hPoint).
have hComposition:=@current_pushforward_composition R h2 n (1+n)%N nu j U AU V hU hAU hV
  inclusion h inclusion_image image inclusion_class hHomotopy.2 T
  current_homotopy_point_composite_proper.
apply:(eq_trans (esym hComposition)).
exact:(@current_pushforward_map_agreement R h2 n nu j U V hU hV
  composite slice composite_image slice_image composite_class slice_class T
  current_homotopy_point_composite_proper slice_proper (fun x (_:U x)=>erefl (slice x))).
Qed.
End CurrentHomotopyPointProduct.
