(** Federer (1969), 4.1.9, p. 363: the original
    endpoint products push forward to f#T and g#T.
    Use the checked fixed-time product identity and
    the original endpoint equalities only on U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces CurrentDirac
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentPushforwardSealed CurrentPushforwardMapAgreement
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain CurrentHomotopyCylinder
  CurrentHomotopySliceClass CurrentHomotopySliceProper CurrentHomotopyEndpointProper CurrentHomotopyPointProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopyEndpointPushforward.
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
Local Notation endpoints := (@current_homotopy_endpoint_images R n nu A U V f g h geometry).
Local Notation endpoint_classes := (@current_smooth_homotopy_endpoint_classes R n nu A U V f g h hHomotopy).
Variable T:@current_space R h2 n U hU j.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T.
Local Notation point_product := (fun t:R=>@CartesianCurrentProduct.value R h2 1%N n 0%N j AT U hAT hU
  (@dirac_current R h2 1%N AT hAT (@euclidean_one_embed R t)) T).
Local Notation initial_proper := (@current_homotopy_start_proper R h2 n nu j A U V f g h geometry T hProper).
Local Notation final_proper := (@current_homotopy_end_proper R h2 n nu j A U V f g h geometry T hProper).

(** Source for [current_homotopy_initial_point_pushforward]:
    h#(delta_0 times T)=f#T, the initial endpoint
    term in the original current homotopy formula,
    Federer 4.1.9, p. 363. The maps are compared
    only on their actual original domain U. *)
Theorem current_homotopy_initial_point_pushforward (hZero:0<=(0:R)<=1):
  @CurrentPushforward.value R h2 (1+n)%N nu j AU V hAU hV (point_product 0) h image hHomotopy.2
    (@current_homotopy_point_product_proper R h2 n nu j A U V f g h hHomotopy T hProper 0 hZero)=
  @CurrentPushforward.value R h2 n nu j U V hU hV T f endpoints.1 endpoint_classes.1 initial_proper.
Proof.
apply:(eq_trans (@current_homotopy_point_product_pushforward R h2 n nu j A U V f g h
  hHomotopy T hProper 0 hZero)).
exact:(@current_pushforward_map_agreement R h2 n nu j U V hU hV
  (@current_homotopy_slice_map R n nu h 0) f
  (@current_homotopy_band_slice_image R n nu A U V f g h geometry 0 hZero) endpoints.1
  (@current_smooth_homotopy_slice_class R n nu A U V f g h hHomotopy 0
    (@current_homotopy_closed_time_band R A hInterval 0 hZero)) endpoint_classes.1 T
  (@current_homotopy_slice_proper R h2 n nu j A U V f g h geometry T 0 hZero hProper)
  initial_proper (@current_homotopy_start R n nu A U V f g h geometry)).
Qed.

(** Source for [current_homotopy_final_point_pushforward]:
    h#(delta_1 times T)=g#T, the final endpoint
    term in the original current homotopy formula,
    Federer 4.1.9, p. 363. The original cylinder
    properness supplies all three pushforwards. *)
Theorem current_homotopy_final_point_pushforward (hOne:0<=(1:R)<=1):
  @CurrentPushforward.value R h2 (1+n)%N nu j AU V hAU hV (point_product 1) h image hHomotopy.2
    (@current_homotopy_point_product_proper R h2 n nu j A U V f g h hHomotopy T hProper 1 hOne)=
  @CurrentPushforward.value R h2 n nu j U V hU hV T g endpoints.2 endpoint_classes.2 final_proper.
Proof.
apply:(eq_trans (@current_homotopy_point_product_pushforward R h2 n nu j A U V f g h
  hHomotopy T hProper 1 hOne)).
exact:(@current_pushforward_map_agreement R h2 n nu j U V hU hV
  (@current_homotopy_slice_map R n nu h 1) g
  (@current_homotopy_band_slice_image R n nu A U V f g h geometry 1 hOne) endpoints.2
  (@current_smooth_homotopy_slice_class R n nu A U V f g h hHomotopy 1
    (@current_homotopy_closed_time_band R A hInterval 1 hOne)) endpoint_classes.2 T
  (@current_homotopy_slice_proper R h2 n nu j A U V f g h geometry T 1 hOne hProper)
  final_proper (@current_homotopy_end R n nu A U V f g h geometry)).
Qed.
End CurrentHomotopyEndpointPushforward.
