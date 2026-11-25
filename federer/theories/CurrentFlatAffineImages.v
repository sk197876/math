(** Federer (1969), 4.1.13, pp. 369–370: the original
    flat-seminorm estimate for two smooth images of a
    normal current. Only the affine segments over spt T
    must lie in V. The proof chooses the smaller source
    internally and transports the original variation integrals
    back to U. The zero-degree statement has its own formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormRegularityOperations NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockLinearMaps EuclideanHomOperator OperatorNormUP OperatorNormSealed
  CurrentDomain CurrentSpaces CurrentBoundary CurrentBoundarySupport CurrentMapDifferential
  CurrentIntegrationCriterion NormalisedCurrentSealed NormalCurrentsUP SmoothCompactSet
  CurrentOpenRestriction CurrentOpenRestrictionBoundary CurrentOpenRestrictionSupport
  CurrentOpenRestrictionNormal CurrentOpenRestrictionVariation CurrentVariationCongruence
  CurrentCompactPushforwardAlgebra CurrentNormalNeighbourhoodPushforward
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopySliceClass CurrentHomotopyCylinder
  CurrentHomotopyEndpointProper CurrentHomotopyBoundaryCylinder CurrentHomotopyCompactCylinder
  CurrentAffineHomotopyUP CurrentAffineHomotopySealed CurrentAffineHomotopyClass
  CurrentAffineHomotopyGeometry CurrentAffineHomotopyNeighbourhood CurrentAffineSegmentHull
  CurrentAffineHomotopyMaximumBound CurrentAffineHomotopyFlatBound
  CurrentAffineWeightRestrictionIntegral CurrentFlatNorm MeasureIntegralUP MeasureIntegralBounds SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_affine_image_compact]: package the exact
    original C of Federer 4.1.13, p. 369, as a compact
    index for the already specified flat seminorm. Its carrier
    is the original segment union, not an enlargement. *)
Definition current_affine_image_compact (R:realType) (h2:(1+1:R)!=0)
    n nu m (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (f g:R_n R n->R_n R nu)
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (hg:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U g)
    (T:@current_space R h2 n U hU m)
    (hNormal:@is_normal_current R h2 n U hU m T)
    (hC:@current_affine_segment_hull R h2 n nu m U hU f g T `<=` V):
  smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R nu)) V:=
  @Build_smooth_compact_set R (R_n R nu)
    (inner_norm (@euclidean_inner_productP R nu))
    (inner_norm_real_norm (@euclidean_inner_productP R nu)) V
    (@current_affine_segment_hull R h2 n nu m U hU f g T) hC
    (@current_affine_segment_hull_compact R h2 n nu m U hU f g T hf hg hNormal.2).

(** Source for [current_affine_image_compact_carrier]: the flat
    compact index has exactly the original displayed set C,
    Federer 4.1.13, p. 369. *)
Lemma current_affine_image_compact_carrier (R:realType) (h2:(1+1:R)!=0)
    n nu m (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (f g:R_n R n->R_n R nu)
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (hg:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U g)
    (T:@current_space R h2 n U hU m)
    (hNormal:@is_normal_current R h2 n U hU m T)
    (hC:@current_affine_segment_hull R h2 n nu m U hU f g T `<=` V):
  smooth_compact_carrier (@current_affine_image_compact R h2 n nu m
    U V hU f g hf hg T hNormal hC)=
  @current_affine_segment_hull R h2 n nu m U hU f g T.
Proof. by []. Qed.

Section CurrentFlatAffineImages.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu:nat.
Variable j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Op := (@euclidean_operator_norm R n nu).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall x,U x->V (g x).
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNX hNY U g.
Local Notation H := (@CurrentAffineHomotopy.value R n nu f g).
Local Notation UT := (current_domain R n U).
Local Notation displacement := (fun x:UT=>NY (g (set_val x)-f (set_val x))).
Local Notation rho := (fun x:UT=>Num.max
  (Op (@current_map_differential R n nu U f (set_val x)))
  (Op (@current_map_differential R n nu U g (set_val x)))).

(** Source for [affine_normal_support_neighbourhood]: the exact
    support-neighbourhood replacement in the proof of Federer
    4.1.13, pp. 369–370, instantiated with the original
    compact support of the normal current. *)
Local Lemma affine_normal_support_neighbourhood m
    (T:@current_space R h2 n U hU m)
    (hNormal:@is_normal_current R h2 n U hU m T)
    (hC:@current_affine_segment_hull R h2 n nu m U hU f g T `<=` V):
  exists (A:set R) (W:set X),
    @is_homotopy_parameter_interval R A /\@open XT W /\
    @current_support R h2 n U hU m T `<=` W /\W `<=` U /\
    forall t x,A t->W x->V ((1-t)*:f x+t*:g x).
Proof.
pose K:=@Build_smooth_compact_set R X NX hNX U
  (@current_support R h2 n U hU m T) (fun x hx=>hx.1) hNormal.2.
apply:(@current_affine_homotopy_neighbourhood R n nu U V hU hV f g hf hg K).
move=>t x ht hx;apply:hC.
by exists t,x;split=>//;split.
Qed.

Section PositiveDegree.
Variable T:@current_space R h2 n U hU j.+1.
Hypothesis hNormal:@is_normal_current R h2 n U hU j.+1 T.
Hypothesis hC:@current_affine_segment_hull R h2 n nu j.+1 U hU f g T `<=` V.
Local Notation C := (@current_affine_image_compact R h2 n nu j.+1
  U V hU f g hf hg T hNormal hC).
Local Notation F := (@current_compact_map_pushforward R h2 n nu U V hU hV
  f hFImage hf j.+1 T hNormal.2).
Local Notation G := (@current_compact_map_pushforward R h2 n nu U V hU hV
  g hGImage hg j.+1 T hNormal.2).
Local Notation B := (@current_boundary R h2 n j U hU T).
Local Notation mu := (@NormalisedCurrent.measure R h2 n j.+1 U hU T hNormal.1.1).
Local Notation muB := (@NormalisedCurrent.measure R h2 n j U hU B hNormal.1.2).

(** Source for [federer_4_1_13_positive_integrals]: both displayed
    original variation integrals in Federer 4.1.13, p. 369,
    are actual integral values. This follows from the affine
    integral laws at the end of 4.1.9, p. 364, applied
    in the ambient target. No target image premise is needed
    for these original-source scalar integral assertions. *)
Theorem federer_4_1_13_positive_integrals:
  is_measure_integral mu
    (real_total_integrand (fun x:UT=>(displacement x*(rho x)^+j.+1)%R))
    (measure_lower_integral mu
      (real_total_integrand (fun x:UT=>(displacement x*(rho x)^+j.+1)%R))) /\
  is_measure_integral muB
    (real_total_integrand (fun x:UT=>(displacement x*(rho x)^+j)%R))
    (measure_lower_integral muB
      (real_total_integrand (fun x:UT=>(displacement x*(rho x)^+j)%R))).
Proof.
clear hC.
have hAmbient:@is_smooth_current_homotopy R n nu (fun _:R=>True)
    U (fun _:Y=>True) f g H:=
  @current_affine_ambient_homotopy R n nu U hU f g hf hg.
have hSource:hU=@current_homotopy_source_open R n nu (fun _:R=>True)
    U (fun _:Y=>True) f g H hAmbient.1:=Prop_irrelevance _ _.
subst hU.
pose hU:=@current_homotopy_source_open R n nu (fun _:R=>True)
  U (fun _:Y=>True) f g H hAmbient.1.
pose hpT:=@current_homotopy_compact_support_proper R h2 n nu j.+1
  (fun _:R=>True) U (fun _:Y=>True) f g H hAmbient T hNormal.2.
pose hpB:=@current_homotopy_boundary_cylinder_proper R h2 n nu j
  (fun _:R=>True) U (fun _:Y=>True) f g H hAmbient.1 T hpT.
have hAffine:forall t x,True->U x->
    @current_homotopy_slice_map R n nu H t x=(1-t)*:f x+t*:g x.
  move=>t x _ _;exact:CurrentAffineHomotopy.laws.
split.
- exact:(@current_affine_homotopy_maximum_bound R h2 n nu j.+1
    (fun _:R=>True) U (fun _:Y=>True) f g H hAmbient T hNormal.1.1 hAffine hpT).1.
- exact:(@current_affine_homotopy_maximum_bound R h2 n nu j
    (fun _:R=>True) U (fun _:Y=>True) f g H hAmbient B hNormal.1.2 hAffine hpB).1.
Qed.

(** Source for [federer_4_1_13_positive]: the original positive-degree
    estimate of Federer 4.1.13, p. 369, proved on p. 370:
    F_C(g#T-f#T) is bounded by the original variation integrals
    of |g-f|rho^(j+1) against ||T|| and |g-f|rho^j against
    ||boundary T||. Only the printed segment-image assumption
    over spt T is imposed. *)
Theorem federer_4_1_13_positive:
  (@current_flat_norm R h2 nu j.+1 V hV C (G-F)<=
    measure_lower_integral mu
      (real_total_integrand (fun x:UT=>(displacement x*(rho x)^+j.+1)%R))+
    measure_lower_integral muB
      (real_total_integrand (fun x:UT=>(displacement x*(rho x)^+j)%R)))%E.
Proof.
have [A [W [hA [hOpenW [hTW [hWU hImageAW]]]]]]:=
  affine_normal_support_neighbourhood (T:=T) hNormal hC.
have hW:forall x,W x->norm_domain_interior NX W x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact:(open_nbhs_nbhs (conj hOpenW hx)).
pose hfW:=fun k=>@norm_class_open_restriction R X Y NX NY hNX hNY
  U W f k hWU hW (hf k).
pose hgW:=fun k=>@norm_class_open_restriction R X Y NX NY hNX hNY
  U W g k hWU hW (hg k).
have hH:@is_smooth_current_homotopy R n nu A W V f g H:=
  @current_affine_homotopy_in_target R n nu A hA W V hW hV f g
    hfW hgW hImageAW.
have hSource:hW=@current_homotopy_source_open R n nu A W V f g H
    hH.1:=Prop_irrelevance _ _.
have hTarget:hV=@current_homotopy_target_open R n nu A W V f g H
    hH.1:=Prop_irrelevance _ _.
subst hW hV.
pose hW:=@current_homotopy_source_open R n nu A W V f g H hH.1.
pose hV:=@current_homotopy_target_open R n nu A W V f g H hH.1.
pose S:=@current_open_restriction R h2 n j.+1 W U hW hU hWU T.
have hNS:=@current_normal_neighbourhood_restriction R h2 n W U hW hU hWU
  j.+1 T hNormal hTW.
pose hp:=@current_homotopy_compact_support_proper R h2 n nu j.+1
  A W V f g H hH S hNS.2.
have hAffine:forall t x,A t->W x->
    @current_homotopy_slice_map R n nu H t x=(1-t)*:f x+t*:g x.
  move=>t x _ _;exact:CurrentAffineHomotopy.laws.
have hImage:H @` (@current_homotopy_closed_cylinder R h2 n nu j.+1
    A W V f g H hH.1 S) `<=` smooth_compact_carrier C.
  move=>y [z [ht hx] <-].
  change (@current_affine_segment_hull R h2 n nu j.+1 U hU f g T (H z)).
  exists (@euclidean_one_project R (@euclidean_first_block_map R 1%N n z)),
    (@euclidean_last_block_map R 1%N n z);split;first exact:ht.
  split.
  - exact:(@current_open_restriction_support_subset R h2 n j.+1
      W U hW hU hWU T _ hx).
  - apply:esym;exact:current_affine_homotopy_coordinates.
pose endpoints:=@current_homotopy_endpoint_images R n nu A W V f g H hH.1.
pose classes:=@current_smooth_homotopy_endpoint_classes R n nu A W V f g H hH.
pose hpF:=@current_homotopy_start_proper R h2 n nu j.+1 A W V f g H hH.1 S hp.
pose hpG:=@current_homotopy_end_proper R h2 n nu j.+1 A W V f g H hH.1 S hp.
have hF:=@current_normal_neighbourhood_pushforward R h2 n nu j.+1 W U V
  hW hU hV hWU f hFImage hf endpoints.1 classes.1 T hNormal hTW hpF.
have hG:=@current_normal_neighbourhood_pushforward R h2 n nu j.+1 W U V
  hW hU hV hWU g hGImage hg endpoints.2 classes.2 T hNormal hTW hpG.
have hFlat:=@current_affine_homotopy_positive_flat_bound R h2 n nu
  A W V f g H hH hAffine C j S hNS.1 hp hImage.
rewrite -hG -hF in hFlat.
have hIntegral:=(@current_affine_homotopy_maximum_bound R h2 n nu j.+1
  A W V f g H hH S hNS.1.1 hAffine hp).1.
have hValue:=@current_affine_restricted_weight_lower_value R h2 n nu j.+1
  W U hW hU hWU f g hf hg T hNormal.1.1 hTW hNS.1.1 j.+1 _ hIntegral.
pose BS:=@current_boundary R h2 n j W hW S.
pose hpB:=@current_homotopy_boundary_cylinder_proper R h2 n nu j
  A W V f g H hH.1 S hp.
have hIntegralB:=(@current_affine_homotopy_maximum_bound R h2 n nu j
  A W V f g H hH BS hNS.1.2 hAffine hpB).1.
have hBW:@current_support R h2 n U hU j B `<=` W.
  move=>x hx;exact:hTW x (@current_boundary_support_subset R h2 n j U hU T x hx).
pose SB:=@current_open_restriction R h2 n j W U hW hU hWU B.
have hSB:=@current_neighbourhood_restriction_representable R h2 n j
  W U hW hU hWU B hNormal.1.2 hBW.
have hBoundary:SB=BS:=@current_open_restriction_boundary R h2 n j
  W U hW hU hWU T.
have hVariation:=@current_variation_current_congruence R h2 n j W hW
  SB BS hSB hNS.1.2 hBoundary.
rewrite -hVariation in hFlat hIntegralB.
have hValueB:=@current_affine_restricted_weight_lower_value R h2 n nu j
  W U hW hU hWU f g hf hg B hNormal.1.2 hBW hSB j _ hIntegralB.
by rewrite hValue hValueB in hFlat.
Qed.
End PositiveDegree.

Section DegreeZero.
Variable T:@current_space R h2 n U hU 0%N.
Hypothesis hNormal:@is_normal_current R h2 n U hU 0%N T.
Hypothesis hC:@current_affine_segment_hull R h2 n nu 0%N U hU f g T `<=` V.
Local Notation C := (@current_affine_image_compact R h2 n nu 0%N
  U V hU f g hf hg T hNormal hC).
Local Notation F := (@current_compact_map_pushforward R h2 n nu U V hU hV
  f hFImage hf 0%N T hNormal.2).
Local Notation G := (@current_compact_map_pushforward R h2 n nu U V hU hV
  g hGImage hg 0%N T hNormal.2).
Local Notation mu := (@NormalisedCurrent.measure R h2 n 0%N U hU T hNormal.1.1).

(** Source for [federer_4_1_13_zero_integral]: the degree-zero
    displacement integral displayed in Federer 4.1.13,
    p. 369, is an actual original-source variation integral,
    by the affine integral laws of 4.1.9, p. 364.
    The zeroth derivative power is exactly one. *)
Theorem federer_4_1_13_zero_integral:
  is_measure_integral mu (real_total_integrand displacement)
    (measure_lower_integral mu (real_total_integrand displacement)).
Proof.
clear hC.
have hAmbient:@is_smooth_current_homotopy R n nu (fun _:R=>True)
    U (fun _:Y=>True) f g H:=
  @current_affine_ambient_homotopy R n nu U hU f g hf hg.
have hSource:hU=@current_homotopy_source_open R n nu (fun _:R=>True)
    U (fun _:Y=>True) f g H hAmbient.1:=Prop_irrelevance _ _.
subst hU.
pose hU:=@current_homotopy_source_open R n nu (fun _:R=>True)
  U (fun _:Y=>True) f g H hAmbient.1.
pose hpT:=@current_homotopy_compact_support_proper R h2 n nu 0%N
  (fun _:R=>True) U (fun _:Y=>True) f g H hAmbient T hNormal.2.
have hAffine:forall t x,True->U x->
    @current_homotopy_slice_map R n nu H t x=(1-t)*:f x+t*:g x.
  move=>t x _ _;exact:CurrentAffineHomotopy.laws.
have hIntegral:=(@current_affine_homotopy_maximum_bound R h2 n nu 0%N
  (fun _:R=>True) U (fun _:Y=>True) f g H hAmbient T hNormal.1.1 hAffine hpT).1.
have hWeight:(fun x:UT=>(displacement x*(rho x)^+0%N)%R)=displacement.
  by apply:funext=>x;rewrite expr0 mulr1.
by rewrite hWeight in hIntegral.
Qed.

(** Source for [federer_4_1_13_zero]: the original degree-zero
    estimate in Federer 4.1.13, p. 369, proved on
    p. 370. F_C(g#T-f#T) is bounded by the original
    variation integral of |g-f|. No negative-degree boundary,
    derivative factor or nonzero-dimensional premise is added. *)
Theorem federer_4_1_13_zero:
  (@current_flat_norm R h2 nu 0%N V hV C (G-F)<=
    measure_lower_integral mu (real_total_integrand displacement))%E.
Proof.
have [A [W [hA [hOpenW [hTW [hWU hImageAW]]]]]]:=
  affine_normal_support_neighbourhood (T:=T) hNormal hC.
have hW:forall x,W x->norm_domain_interior NX W x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact:(open_nbhs_nbhs (conj hOpenW hx)).
pose hfW:=fun k=>@norm_class_open_restriction R X Y NX NY hNX hNY
  U W f k hWU hW (hf k).
pose hgW:=fun k=>@norm_class_open_restriction R X Y NX NY hNX hNY
  U W g k hWU hW (hg k).
have hH:@is_smooth_current_homotopy R n nu A W V f g H:=
  @current_affine_homotopy_in_target R n nu A hA W V hW hV f g
    hfW hgW hImageAW.
have hSource:hW=@current_homotopy_source_open R n nu A W V f g H
    hH.1:=Prop_irrelevance _ _.
have hTarget:hV=@current_homotopy_target_open R n nu A W V f g H
    hH.1:=Prop_irrelevance _ _.
subst hW hV.
pose hW:=@current_homotopy_source_open R n nu A W V f g H hH.1.
pose hV:=@current_homotopy_target_open R n nu A W V f g H hH.1.
pose S:=@current_open_restriction R h2 n 0%N W U hW hU hWU T.
have hNS:=@current_normal_neighbourhood_restriction R h2 n W U hW hU hWU
  0%N T hNormal hTW.
pose hp:=@current_homotopy_compact_support_proper R h2 n nu 0%N
  A W V f g H hH S hNS.2.
have hAffine:forall t x,A t->W x->
    @current_homotopy_slice_map R n nu H t x=(1-t)*:f x+t*:g x.
  move=>t x _ _;exact:CurrentAffineHomotopy.laws.
have hImage:H @` (@current_homotopy_closed_cylinder R h2 n nu 0%N
    A W V f g H hH.1 S) `<=` smooth_compact_carrier C.
  move=>y [z [ht hx] <-].
  change (@current_affine_segment_hull R h2 n nu 0%N U hU f g T (H z)).
  exists (@euclidean_one_project R (@euclidean_first_block_map R 1%N n z)),
    (@euclidean_last_block_map R 1%N n z);split;first exact:ht.
  split.
  - exact:(@current_open_restriction_support_subset R h2 n 0%N W U hW hU hWU T _ hx).
  - apply:esym;exact:current_affine_homotopy_coordinates.
pose endpoints:=@current_homotopy_endpoint_images R n nu A W V f g H hH.1.
pose classes:=@current_smooth_homotopy_endpoint_classes R n nu A W V f g H hH.
pose hpF:=@current_homotopy_start_proper R h2 n nu 0%N A W V f g H hH.1 S hp.
pose hpG:=@current_homotopy_end_proper R h2 n nu 0%N A W V f g H hH.1 S hp.
have hF:=@current_normal_neighbourhood_pushforward R h2 n nu 0%N W U V
  hW hU hV hWU f hFImage hf endpoints.1 classes.1 T hNormal hTW hpF.
have hG:=@current_normal_neighbourhood_pushforward R h2 n nu 0%N W U V
  hW hU hV hWU g hGImage hg endpoints.2 classes.2 T hNormal hTW hpG.
have hFlat:=@current_affine_homotopy_zero_flat_bound R h2 n nu
  A W V f g H hH hAffine C S hNS.1.1 hp hImage.
rewrite -hG -hF in hFlat.
have hIntegral:=(@current_affine_homotopy_maximum_bound R h2 n nu 0%N
  A W V f g H hH S hNS.1.1 hAffine hp).1.
have hValue:=@current_affine_restricted_weight_lower_value R h2 n nu 0%N
  W U hW hU hWU f g hf hg T hNormal.1.1 hTW hNS.1.1 0%N _ hIntegral.
have hWeightW:(fun x:current_domain R n W=>NY (g (set_val x)-f (set_val x))*
    (Num.max (Op (@current_map_differential R n nu W f (set_val x)))
      (Op (@current_map_differential R n nu W g (set_val x))))^+0%N)=
    (fun x:current_domain R n W=>NY (g (set_val x)-f (set_val x))).
  by apply:funext=>x;rewrite expr0 mulr1.
have hWeightU:(fun x:UT=>(displacement x*(rho x)^+0%N)%R)=displacement.
  by apply:funext=>x;rewrite expr0 mulr1.
rewrite hWeightW hWeightU in hValue.
by rewrite hValue in hFlat.
Qed.
End DegreeZero.
End CurrentFlatAffineImages.
