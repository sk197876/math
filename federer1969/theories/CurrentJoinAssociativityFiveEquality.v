(** Federer (1969), 4.1.11, p. 366: the
    literal two iterated maps have equal images of the
    original ordered five-factor current. Carry its
    common-source image through both maps, use the
    original H triangle argument and cancel the same sign. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDegreeTransport CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentCompactImageTransportEquation CurrentAmbientCartesianProduct CurrentJoinDomain CurrentJoinSourceCompact
  CurrentJoinAssociatorMapsSealed CurrentJoinTriangleMapsClass CurrentJoinAssociativityRegroup
  CurrentJoinAssociativityRegroupClass CurrentJoinAssociativitySquareSlot CurrentJoinAssociativityCommonMap
  CurrentJoinAssociativityCommonImage CurrentJoinAssociativityCommonEquality
  CurrentJoinAssociativityIteratedMaps CurrentJoinAssociativityCommonCompositions SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinAssociativityFiveEquality.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j k:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables (P:@current_space R h2 n (Full n) (hFull n) i)
  (S:@current_space R h2 n (Full n) (hFull n) j)
  (T:@current_space R h2 n (Full n) (hFull n) k).
Hypothesis hP:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) i P).
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) k T).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_segment_compact R h2).
Local Notation Square := (@current_ambient_cartesian_product R h2 1%N 1%N 1%N 1%N I I).
Local Notation hSquare := (@current_ambient_cartesian_product_compact R h2 1%N 1%N 1%N 1%N I I hI hI).
Local Notation SquareT := (@current_ambient_cartesian_product R h2 2%N n 2%N k Square T).
Local Notation hSquareT := (@current_ambient_cartesian_product_compact R h2 2%N n 2%N k Square T hSquare hT).
Local Notation InnerSource := (@current_ambient_cartesian_product R h2 n (2+n)%N j (2+k)%N S SquareT).
Local Notation hInnerSource := (@current_ambient_cartesian_product_compact R h2 n (2+n)%N j (2+k)%N S SquareT hS hSquareT).
Local Notation Common := (@current_ambient_cartesian_product R h2 n (n+(2+n))%N i (j+(2+k))%N P InnerSource).
Local Notation hCommon := (@current_ambient_cartesian_product_compact R h2 n (n+(2+n))%N i (j+(2+k))%N P InnerSource hP hInnerSource).
Local Notation IT := (@current_ambient_cartesian_product R h2 1%N n 1%N k I T).
Local Notation hIT := (@current_ambient_cartesian_product_compact R h2 1%N n 1%N k I T hI hT).
Local Notation SIT := (@current_ambient_cartesian_product R h2 n (1+n)%N j (1+k)%N S IT).
Local Notation hSIT := (@current_ambient_cartesian_product_compact R h2 n (1+n)%N j (1+k)%N S IT hS hIT).
Local Notation InnerTarget := (@current_ambient_cartesian_product R h2 1%N (n+(1+n))%N 1%N (j+(1+k))%N I SIT).
Local Notation hInnerTarget := (@current_ambient_cartesian_product_compact R h2 1%N (n+(1+n))%N 1%N (j+(1+k))%N I SIT hI hSIT).
Local Notation Five := (@current_ambient_cartesian_product R h2 n (1+(n+(1+n)))%N i (1+(j+(1+k)))%N P InnerTarget).
Local Notation eInner := (eq_trans (congr2 addn (erefl j) (esym (addnA 1%N 1%N k)))
  (addnCA j 1%N (1+k)%N)).
Local Notation hFive := (@current_ambient_cartesian_product_compact R h2 n (1+(n+(1+n)))%N
  i (1+(j+(1+k)))%N P InnerTarget hP hInnerTarget).
Local Notation dc := ((n+(n+(2+n)))%N).
Local Notation df := ((n+(1+(n+(1+n))))%N).
Local Notation dw := ((n+(n+(3+n)))%N).
Local Notation c := ((i+(j+(2+k)))%N).
Local Notation d := ((i+(1+(j+(1+k))))%N).
Local Notation e := (congr2 addn (erefl i) eInner).
Local Notation L := (@current_join_assoc_common_regroup R n).
Local Notation hL := (@current_join_assoc_common_regroup_smooth R n).
Local Notation Left := (@current_join_assoc_left_map R n).
Local Notation hLeft := (@current_join_assoc_left_map_smooth R n).
Local Notation Right := (@current_join_assoc_right_map R n).
Local Notation hRight := (@current_join_assoc_right_map_smooth R n).
Local Notation CImage := (fun (x:R_n R dc) (_:True)=>Logic.I).
Local Notation FImage := (fun (x:R_n R df) (_:True)=>Logic.I).
Local Notation WImage := (fun (x:R_n R dw) (_:True)=>Logic.I).
Local Notation H := (@current_join_assoc_weighted_map R n).
Local Notation hH := (@current_join_assoc_weighted_map_smooth R n).
Local Notation f := (@CurrentJoinAssociatorMaps.left_triangle R).
Local Notation g := (@CurrentJoinAssociatorMaps.right_triangle R).
Local Notation hf := (@current_join_left_triangle_smooth R).
Local Notation hg := (@current_join_right_triangle_smooth R).
Local Notation Slot := (@current_join_assoc_square_slot R n).
Local Notation hSlot := (fun (u:R_n R 2%N->R_n R 3%N)
  (hu:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R 2%N))
    (inner_norm_real_norm (@euclidean_inner_productP R 3%N)) (Full 2%N) u)=>
  @current_join_assoc_square_slot_smooth R n u hu).
Local Notation LeftImage := (@current_smooth_composite_image R dc df n
  (Full dc) (Full df) (Full n) L Left CImage FImage).
Local Notation LeftClass := (@current_smooth_composite_class R dc df n
  (Full dc) (Full df) L Left CImage hL hLeft).
Local Notation RightImage := (@current_smooth_composite_image R dc df n
  (Full dc) (Full df) (Full n) L Right CImage FImage).
Local Notation RightClass := (@current_smooth_composite_class R dc df n
  (Full dc) (Full df) L Right CImage hL hRight).
Local Notation KLImage := (@current_smooth_composite_image R dc dw n
  (Full dc) (Full dw) (Full n) (Slot f) H CImage WImage).
Local Notation KLClass := (@current_smooth_composite_class R dc dw n
  (Full dc) (Full dw) (Slot f) H CImage (hSlot f hf) hH).
Local Notation KRImage := (@current_smooth_composite_image R dc dw n
  (Full dc) (Full dw) (Full n) (Slot g) H CImage WImage).
Local Notation KRClass := (@current_smooth_composite_class R dc dw n
  (Full dc) (Full dw) (Slot g) H CImage (hSlot g hg) hH).

(** Source for [current_join_assoc_five_factor_equality]: the
    two literal iterated F maps have equal images of
    R times I times S times I times T, supporting
    the associative law in Federer 4.1.11, p. 366.
    The common sign (-1)^j is proved and cancelled;
    no representation hypothesis is used. *)
Lemma current_join_assoc_five_factor_equality:
  @current_compact_map_pushforward R h2 df n (Full df) (Full n) (hFull df) (hFull n)
    Left FImage hLeft d Five hFive=
  @current_compact_map_pushforward R h2 df n (Full df) (Full n) (hFull df) (hFull n)
    Right FImage hRight d Five hFive.
Proof.
have hSource:=@current_join_assoc_common_source_image R h2 n i j k P S T hP hS hT.
have hLeftSource:=@current_compact_image_transport_equation R h2 dc df n L Left hL hLeft
  c Common hCommon d e ((-1:R)^+j) Five hFive hSource.
have hRightSource:=@current_compact_image_transport_equation R h2 dc df n L Right hL hRight
  c Common hCommon d e ((-1:R)^+j) Five hFive hSource.
have hLeftCompare:=@current_compact_map_images_agree R h2 dc n
  (Full dc) (Full n) (hFull dc) (hFull n) (fun x=>Left (L x)) LeftImage LeftClass
  c Common hCommon (fun x=>H (Slot f x)) KLImage KLClass hCommon
  (fun x _=>@current_join_assoc_left_common_composition R n x).
have hRightCompare:=@current_compact_map_images_agree R h2 dc n
  (Full dc) (Full n) (hFull dc) (hFull n) (fun x=>Right (L x)) RightImage RightClass
  c Common hCommon (fun x=>H (Slot g x)) KRImage KRClass hCommon
  (fun x _=>@current_join_assoc_right_common_composition R n x).
have hCommonEquality:=@current_join_assoc_common_composite_equality R h2 n i j k P S T hP hS hT.
have hImages:=eq_trans hLeftCompare (eq_trans hCommonEquality (esym hRightCompare)).
pose Tr:=@current_degree_transport R h2 n (Full n) (hFull n) c d e.
have hSigned:=congr1 Tr hImages.
rewrite hLeftSource hRightSource in hSigned.
have hCancel:=congr1 (fun V:@current_space R h2 n (Full n) (hFull n) d=>(-1:R)^+j*:V) hSigned.
by rewrite !signrZK in hCancel.
Qed.
End CurrentJoinAssociativityFiveEquality.
