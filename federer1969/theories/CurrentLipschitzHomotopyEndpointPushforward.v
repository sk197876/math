(** Federer (1969), 4.1.14, p. 371: the
    original locally Lipschitz deformation chain retains
    the endpoint identities of 4.1.9, p. 363.
    The actual point product is its point-inclusion
    image by 4.1.8, p. 362. Composition and
    the original endpoint equalities identify its
    image under h. Properness is imposed only
    on the original closed time cylinder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockLinearMaps EuclideanCartesianMap LipschitzUP
  MetricLocalLipschitzComposition NormLocalLipschitzScalarProduct
  CurrentSpaces CurrentDirac DiracCurrentBounds CurrentBoundary
  CurrentBoundarySupport CurrentProperSupport CurrentProperSupportMapAgreement
  CurrentProperSupportRestriction CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianSupportEquality
  CurrentCartesianPointInclusion CurrentCartesianPointInclusionProper
  CurrentCartesianPointProduct CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentHomotopyCylinder CurrentHomotopySliceProper
  CurrentHomotopyEndpointProper CurrentHomotopyTimeSegment
  CurrentHomotopyProductSupport FlatCurrentsUP CurrentLocallyFlatBoundary
  CurrentLocallyFlatTimeCylinder CurrentLipschitzHomotopyUP
  CurrentLipschitzHomotopySlices CurrentLipschitzPushforwardUP
  CurrentLipschitzPushforwardSealed CurrentLipschitzPushforwardBasic
  CurrentLipschitzImageUniqueness CurrentLipschitzImageSmoothAgreement
  CurrentLipschitzImagesComposition CurrentLipschitzPushforwardExtensional
  CurrentLipschitzPushforwardBoundary CurrentLipschitzDeformationChainUP
  CurrentLipschitzDeformationChainSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentLipschitzHomotopyPointProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h.
Local Notation geometry:=hHomotopy.1.
Local Notation hU:=(current_homotopy_source_open geometry).
Local Notation hV:=(current_homotopy_target_open geometry).
Local Notation hA:=(current_homotopy_parameter_interval geometry).
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hA).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation image:=(current_homotopy_image geometry).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_locally_flat_current R h2 n j U hU T.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j
  A U V f g h geometry T.
Variable t:R.
Hypothesis hBand:0<=t<=1.
Local Notation z:=(@euclidean_one_embed R t).
Local Notation slice:=(@current_homotopy_slice_map R n nu h t).
Local Notation slice_image:=(@current_homotopy_band_slice_image R n nu
  A U V f g h geometry t hBand).
Local Notation slice_local:=(@current_lipschitz_homotopy_slice R n nu
  A U V f g h geometry hHomotopy.2 t
  (@current_homotopy_closed_time_band R A hA t hBand)).
Local Notation slice_proper:=(@current_homotopy_slice_proper R h2 n nu j
  A U V f g h geometry T t hBand hProper).
Local Notation point_product:=(@CartesianCurrentProduct.value R h2 1%N n
  0%N j AT U hAT hU (@dirac_current R h2 1%N AT hAT z) T).

(** Source for [current_lipschitz_homotopy_time_point_member]:
    each time in the original closed band belongs
    to A, supporting the endpoint products in
    Federer 4.1.14, p. 371, by 4.1.9,
    p. 363. *)
Local Lemma current_lipschitz_homotopy_time_point_member:AT z.
Proof.
change (A (@euclidean_one_project R z));rewrite euclidean_one_embedK.
exact:(@current_homotopy_closed_time_band R A hA t hBand).
Qed.
Local Notation inclusion:=(@current_cartesian_point_inclusion R 1%N n z).
Local Notation inclusion_image:=(fun x hx=>
  @current_cartesian_point_inclusion_image R 1%N n AT U
    z current_lipschitz_homotopy_time_point_member x hx).
Local Notation inclusion_class:=(@current_cartesian_point_inclusion_smooth
  R 1%N n U hU z).
Local Notation inclusion_proper:=(@current_cartesian_point_inclusion_proper
  R h2 1%N n j AT U hAT hU z
  current_lipschitz_homotopy_time_point_member T).

(** Source for [current_lipschitz_homotopy_point_inclusion_local]:
    the original point inclusion is locally Lipschitz
    by its preceding affine smoothness, supporting
    Federer 4.1.14, p. 371. *)
Local Lemma current_lipschitz_homotopy_point_inclusion_local:
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNZ) U inclusion.
Proof.
apply:(@norm_class_one_locally_metric_lipschitz R X Z NX NZ hNX hNZ
  U inclusion).
exact:((@norm_class_firstP R X Z NX NZ hNX hNZ U inclusion).1
  (inclusion_class 1%N)).
Qed.
Local Notation inclusion_local:=current_lipschitz_homotopy_point_inclusion_local.

(** Source for [current_lipschitz_homotopy_point_product_image]:
    delta_t times T is the actual point-inclusion
    image in the independent local Lipschitz sense,
    supporting Federer 4.1.14, p. 371, by
    the original 4.1.8 identity. *)
Local Lemma current_lipschitz_homotopy_point_product_image:
  @is_current_lipschitz_image R h2 n (1+n)%N j U AU hU hAU
    inclusion inclusion_image inclusion_local T point_product.
Proof.
pose Q:=@CurrentLipschitzPushforward.value R h2 n (1+n)%N j
  U AU hU hAU inclusion inclusion_image inclusion_local T hT inclusion_proper.
have hQ:=@CurrentLipschitzPushforward.laws R h2 n (1+n)%N j
  U AU hU hAU inclusion inclusion_image inclusion_local T hT inclusion_proper.
have hSame:Q=point_product.
  rewrite (@current_cartesian_point_product R h2 1%N n j AT U hAT hU
    z current_lipschitz_homotopy_time_point_member T).
  exact:(@current_lipschitz_image_smooth_agreement R h2 n (1+n)%N j
    U AU hU hAU inclusion inclusion_image inclusion_local inclusion_class
    T hT inclusion_proper Q hQ).
by rewrite -hSame.
Qed.

(** Source for [current_lipschitz_homotopy_point_product_locally_flat]:
    the original delta_t times T is locally flat
    whenever T is locally flat, supporting the
    endpoint terms in Federer 4.1.14, p. 371.
    T may have noncompact support and infinite mass. *)
Theorem current_lipschitz_homotopy_point_product_locally_flat:
  @is_locally_flat_current R h2 (1+n)%N j AU hAU point_product.
Proof.
exact:current_lipschitz_homotopy_point_product_image.1.
Qed.

(** Source for [current_lipschitz_homotopy_point_product_proper]:
    h is proper on the support of delta_t
    times T under only its original cylinder
    properness, supporting Federer 4.1.14, p. 371.
    No smoothness of h is assumed. *)
Theorem current_lipschitz_homotopy_point_product_proper:
  @is_current_proper_on_support R h2 (1+n)%N nu j
    AU hAU V point_product h image.
Proof.
apply:(@current_homotopy_contained_current_proper R h2 n nu j
  A U V f g h geometry T j point_product);last exact:hProper.
rewrite (@current_cartesian_support R h2 1%N n 0%N j
  AT U hAT hU (@dirac_current R h2 1%N AT hAT z) T).
move=>a [ha hx];split;last exact:hx.
have he:@euclidean_first_block_map R 1%N n a=z.
  exact:(@dirac_current_support_subset R h2 1%N AT hAT z
    current_lipschitz_homotopy_time_point_member _ ha).
change (0<=@euclidean_one_project R
  (@euclidean_first_block_map R 1%N n a)<=1).
by rewrite he euclidean_one_embedK.
Qed.
Local Notation product_local:=current_lipschitz_homotopy_point_product_locally_flat.
Local Notation product_proper:=current_lipschitz_homotopy_point_product_proper.
Local Notation composite:=(fun x:X=>h (inclusion x)).
Let composite_image:forall x,U x->V (composite x):=
  fun x hx=>@current_homotopy_image R n nu A U V f g h geometry
    (inclusion x) (@current_cartesian_point_inclusion_image R 1%N n
      AT U z current_lipschitz_homotopy_time_point_member x hx).
Let composite_local:=@metric_local_lipschitz_composition R
  (real_norm_metric_space hNX) (real_norm_metric_space hNZ)
  (real_norm_metric_space hNY) U AU inclusion h
  inclusion_image inclusion_local hHomotopy.2.

(** Source for [current_lipschitz_homotopy_point_composite_proper]:
    the composite h epsilon_t is the original
    slice map on U, and hence is proper
    on spt T by the cylinder hypothesis,
    supporting Federer 4.1.14, p. 371. *)
Local Lemma current_lipschitz_homotopy_point_composite_proper:
  @is_current_proper_on_support R h2 n nu j U hU V
    T composite composite_image.
Proof.
exact:(@current_proper_support_map_agreement R h2 n nu j U V hU T
  slice composite slice_image composite_image
  (fun x (_:U x)=>erefl (slice x)) slice_proper).
Qed.

(** Source for [current_lipschitz_homotopy_point_product_pushforward]:
    h#(delta_t times T)=(h_t)#T for every
    locally flat original current, supporting Federer
    4.1.14, p. 371. Use the point-product
    identity and composition under original properness;
    all currents and images are the actual opaque values. *)
Theorem current_lipschitz_homotopy_point_product_pushforward:
  @CurrentLipschitzPushforward.value R h2 (1+n)%N nu j AU V hAU hV
    h image hHomotopy.2 point_product product_local product_proper=
  @CurrentLipschitzPushforward.value R h2 n nu j U V hU hV
    slice slice_image slice_local T hT slice_proper.
Proof.
pose C:=@CurrentLipschitzPushforward.value R h2 n nu j U V hU hV
  composite composite_image composite_local T hT
  current_lipschitz_homotopy_point_composite_proper.
have hComposition:=@current_lipschitz_images_composition R h2 n (1+n)%N nu j
  U AU V hU hAU hV inclusion h inclusion_image image inclusion_local
  hHomotopy.2 T hT current_lipschitz_homotopy_point_composite_proper
  point_product
  (@CurrentLipschitzPushforward.value R h2 (1+n)%N nu j AU V hAU hV
    h image hHomotopy.2 point_product product_local product_proper) C
  current_lipschitz_homotopy_point_product_image
  (@CurrentLipschitzPushforward.laws R h2 (1+n)%N nu j AU V hAU hV
    h image hHomotopy.2 point_product product_local product_proper)
  (@CurrentLipschitzPushforward.laws R h2 n nu j U V hU hV
    composite composite_image composite_local T hT
    current_lipschitz_homotopy_point_composite_proper).
apply:(eq_trans (esym hComposition)).
exact:(@current_lipschitz_pushforward_data_independent R h2 n nu j
  U V hU hV composite composite_image composite_local slice_image slice_local
  T hT hT current_lipschitz_homotopy_point_composite_proper slice_proper).
Qed.
End CurrentLipschitzHomotopyPointProduct.

Section CurrentLipschitzHomotopyEndpointPushforward.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables f g:R_n R n->R_n R nu.
Variable h:R_n R (1+n)%N->R_n R nu.
Hypothesis hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h.
Local Notation geometry:=hHomotopy.1.
Local Notation hU:=(current_homotopy_source_open geometry).
Local Notation hV:=(current_homotopy_target_open geometry).
Local Notation hA:=(current_homotopy_parameter_interval geometry).
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hA).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation image:=(current_homotopy_image geometry).
Local Notation endpoints:=(current_homotopy_endpoint_images geometry).
Local Notation endpoint_local:=(@current_lipschitz_homotopy_endpoints R n nu
  A U V f g h geometry hHomotopy.2).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_locally_flat_current R h2 n j U hU T.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j
  A U V f g h geometry T.
Local Notation point_product:=(fun t:R=>@CartesianCurrentProduct.value R h2
  1%N n 0%N j AT U hAT hU
  (@dirac_current R h2 1%N AT hAT (@euclidean_one_embed R t)) T).
Local Notation initial_proper:=(@current_homotopy_start_proper R h2 n nu j
  A U V f g h geometry T hProper).
Local Notation final_proper:=(@current_homotopy_end_proper R h2 n nu j
  A U V f g h geometry T hProper).

(** Source for [current_lipschitz_homotopy_initial_point_pushforward]:
    h#(delta_0 times T)=f#T for the actual
    locally flat images, supporting the original
    homotopy formulas in Federer 4.1.14, p. 371.
    Only h_0=f on the original U is used. *)
Theorem current_lipschitz_homotopy_initial_point_pushforward
    (hZero:0<=(0:R)<=1):
  @CurrentLipschitzPushforward.value R h2 (1+n)%N nu j AU V hAU hV
    h image hHomotopy.2 (point_product 0)
    (@current_lipschitz_homotopy_point_product_locally_flat R h2 n nu j
      A U V f g h hHomotopy T hT 0 hZero)
    (@current_lipschitz_homotopy_point_product_proper R h2 n nu j
      A U V f g h hHomotopy T hProper 0 hZero)=
  @CurrentLipschitzPushforward.value R h2 n nu j U V hU hV
    f endpoints.1 endpoint_local.1 T hT initial_proper.
Proof.
apply:(eq_trans (@current_lipschitz_homotopy_point_product_pushforward R h2
  n nu j A U V f g h hHomotopy T hT hProper 0 hZero)).
exact:(@current_lipschitz_pushforward_domain_agreement R h2 n nu j
  U V hU hV (@current_homotopy_slice_map R n nu h 0) f
  (@current_homotopy_band_slice_image R n nu A U V f g h geometry 0 hZero)
  endpoints.1
  (@current_lipschitz_homotopy_slice R n nu A U V f g h geometry hHomotopy.2
    0 (@current_homotopy_closed_time_band R A hA 0 hZero))
  endpoint_local.1 (@current_homotopy_start R n nu A U V f g h geometry)
  T hT (@current_homotopy_slice_proper R h2 n nu j
    A U V f g h geometry T 0 hZero hProper) initial_proper).
Qed.

(** Source for [current_lipschitz_homotopy_final_point_pushforward]:
    h#(delta_1 times T)=g#T for the actual
    locally flat images, supporting the original
    homotopy formulas in Federer 4.1.14, p. 371.
    The original cylinder properness supplies both images. *)
Theorem current_lipschitz_homotopy_final_point_pushforward
    (hOne:0<=(1:R)<=1):
  @CurrentLipschitzPushforward.value R h2 (1+n)%N nu j AU V hAU hV
    h image hHomotopy.2 (point_product 1)
    (@current_lipschitz_homotopy_point_product_locally_flat R h2 n nu j
      A U V f g h hHomotopy T hT 1 hOne)
    (@current_lipschitz_homotopy_point_product_proper R h2 n nu j
      A U V f g h hHomotopy T hProper 1 hOne)=
  @CurrentLipschitzPushforward.value R h2 n nu j U V hU hV
    g endpoints.2 endpoint_local.2 T hT final_proper.
Proof.
apply:(eq_trans (@current_lipschitz_homotopy_point_product_pushforward R h2
  n nu j A U V f g h hHomotopy T hT hProper 1 hOne)).
exact:(@current_lipschitz_pushforward_domain_agreement R h2 n nu j
  U V hU hV (@current_homotopy_slice_map R n nu h 1) g
  (@current_homotopy_band_slice_image R n nu A U V f g h geometry 1 hOne)
  endpoints.2
  (@current_lipschitz_homotopy_slice R n nu A U V f g h geometry hHomotopy.2
    1 (@current_homotopy_closed_time_band R A hA 1 hOne))
  endpoint_local.2 (@current_homotopy_end R n nu A U V f g h geometry)
  T hT (@current_homotopy_slice_proper R h2 n nu j
    A U V f g h geometry T 1 hOne hProper) final_proper).
Qed.
End CurrentLipschitzHomotopyEndpointPushforward.

Section CurrentLipschitzDeformationChainPushforward.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables f g:R_n R n->R_n R nu.
Variable h:R_n R (1+n)%N->R_n R nu.
Hypothesis hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h.
Local Notation geometry:=hHomotopy.1.
Local Notation hU:=(current_homotopy_source_open geometry).
Local Notation hV:=(current_homotopy_target_open geometry).
Local Notation hA:=(current_homotopy_parameter_interval geometry).
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hA).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT U hAT hU).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_locally_flat_current R h2 n j U hU T.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j
  A U V f g h geometry T.
Local Notation time:=(@current_homotopy_time_segment R A hA h2).
Local Notation product:=(@CartesianCurrentProduct.value R h2 1%N n 1%N j
  AT U hAT hU time T).
Local Notation product_local:=(@locally_flat_current_time_cylinder R h2 n j
  A U hA hU T hT).
Local Notation product_proper:=(@current_homotopy_product_proper R h2 n nu j
  A U V f g h geometry T hProper).
Local Notation product_boundary:=(@current_boundary R h2 (1+n)%N j AU hAU product).
Local Notation image:=(current_homotopy_image geometry).
Local Notation chain:=(@CurrentLipschitzDeformationChain.value R h2 n nu j
  A U V f g h hHomotopy T hT hProper).

(** Source for [current_lipschitz_deformation_chain_pushforward]:
    the actual opaque chain equals the actual
    local image h#([0,1] times T), as
    defined in Federer 4.1.14, p. 371.
    Only the public independent image laws and
    uniqueness are used; no chosen witness is exposed. *)
Theorem current_lipschitz_deformation_chain_pushforward:
  chain=@CurrentLipschitzPushforward.value R h2 (1+n)%N nu (1+j)%N
    AU V hAU hV h image hHomotopy.2 product product_local product_proper.
Proof.
exact:(@current_lipschitz_image_unique R h2 (1+n)%N nu (1+j)%N
  AU V hAU hV h image hHomotopy.2 product product_local product_proper
  chain _
  (@CurrentLipschitzDeformationChain.laws R h2 n nu j
    A U V f g h hHomotopy T hT hProper)
  (@CurrentLipschitzPushforward.laws R h2 (1+n)%N nu (1+j)%N
    AU V hAU hV h image hHomotopy.2 product product_local product_proper)).
Qed.

(** Source for [current_lipschitz_deformation_chain_boundary_proper]:
    the product boundary has smaller support than
    the original cylinder, so the printed
    properness suffices, supporting Federer 4.1.14,
    p. 371, by 4.1.9, p. 363. *)
Theorem current_lipschitz_deformation_chain_boundary_proper:
  @is_current_proper_on_support R h2 (1+n)%N nu j AU hAU V
    product_boundary h image.
Proof.
exact:(@current_proper_smaller_support R h2 (1+n)%N nu AU hAU V h image
  (1+j)%N j product product_boundary
  (@current_boundary_support_subset R h2 (1+n)%N j AU hAU product) product_proper).
Qed.

(** Source for [current_lipschitz_deformation_chain_boundary]:
    boundary h#([0,1] times T) equals h#
    of its product boundary for every original
    locally flat T, supporting the homotopy
    identities in Federer 4.1.14, p. 371.
    This includes degree zero without a negative boundary. *)
Theorem current_lipschitz_deformation_chain_boundary:
  @current_boundary R h2 nu j V hV chain=
  @CurrentLipschitzPushforward.value R h2 (1+n)%N nu j
    AU V hAU hV h image hHomotopy.2 product_boundary
    (@locally_flat_current_boundary R h2 (1+n)%N j AU hAU product product_local)
    current_lipschitz_deformation_chain_boundary_proper.
Proof.
rewrite current_lipschitz_deformation_chain_pushforward.
exact:(@current_lipschitz_pushforward_boundary R h2 (1+n)%N nu j
  AU V hAU hV h image hHomotopy.2 product product_local product_proper
  current_lipschitz_deformation_chain_boundary_proper).
Qed.
End CurrentLipschitzDeformationChainPushforward.
