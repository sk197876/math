(** Federer (1969), 4.1.11, p. 366: the
    common original R times (S times (square times T))
    current becomes R times (I times (S times (I times T)))
    with the exact shared sign (-1)^j. All products
    and images are the preceding opaque operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  EuclideanCartesianLinear EuclideanDimensionCastLinear CurrentSpaces CurrentDegreeTransport
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages CurrentAmbientCartesianProduct
  CurrentAmbientProductImageEquation CurrentCartesianMapClass CurrentJoinSliceMapClass
  CurrentJoinDomain CurrentJoinSourceCompact CurrentFirstTwoBlockInterchange
  CurrentJoinAssociativityRegroup CurrentJoinAssociativityRegroupClass CurrentJoinAssociativityInnerImage
  SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAssociativityCommonImage.
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
Local Notation Id := (fun x:R_n R n=>x).
Local Notation IdClass := (@current_join_slice_identity_smooth R n).
Local Notation Assoc := (@euclidean_dimension_cast_map R ((1+1)+n)%N (1+(1+n))%N (esym (addnA 1%N 1%N n))).
Local Notation AssocClass := (@euclidean_dimension_cast_smooth R ((1+1)+n)%N (1+(1+n))%N
  (esym (addnA 1%N 1%N n)) (Full (2+n)%N) (hFull (2+n)%N)).
Local Notation A := (@euclidean_cartesian_map R n (2+n)%N n (1+(1+n))%N Id Assoc).
Local Notation AClass := (@current_cartesian_map_smooth R n (2+n)%N n (1+(1+n))%N Id Assoc IdClass AssocClass).
Local Notation B := (@current_first_two_block_interchange R n 1%N (1+n)%N).
Local Notation BClass := (@current_first_two_block_smooth R n 1%N (1+n)%N).
Local Notation AImage := (fun (x:R_n R (n+(2+n))%N) (_:True)=>Logic.I).
Local Notation BImage := (fun (x:R_n R (n+(1+(1+n)))%N) (_:True)=>Logic.I).
Local Notation OldImage := (@current_smooth_composite_image R (n+(2+n))%N (n+(1+(1+n)))%N (1+(n+(1+n)))%N
  (Full (n+(2+n))%N) (Full (n+(1+(1+n)))%N) (Full (1+(n+(1+n)))%N) A B AImage BImage).
Local Notation OldClass := (@current_smooth_composite_class R (n+(2+n))%N (n+(1+(1+n)))%N (1+(n+(1+n)))%N
  (Full (n+(2+n))%N) (Full (n+(1+(1+n)))%N) A B AImage AClass BClass).
Local Notation InnerMap := (@current_join_assoc_inner_regroup R n).
Local Notation InnerClass := (@current_join_assoc_inner_regroup_smooth R n).
Local Notation ProductMap := (@euclidean_cartesian_map R n (n+(2+n))%N n (1+(n+(1+n)))%N Id InnerMap).
Local Notation ProductClass := (@current_cartesian_map_smooth R n (n+(2+n))%N n (1+(n+(1+n)))%N
  Id InnerMap IdClass InnerClass).
Local Notation CommonMap := (@current_join_assoc_common_regroup R n).
Local Notation CommonClass := (@current_join_assoc_common_regroup_smooth R n).
Local Notation Image := (fun (x:R_n R (n+(n+(2+n)))%N) (_:True)=>Logic.I).

(** Source for [current_join_assoc_common_source_image]: the
    common current gives the original five-factor current
    with exact sign (-1)^j, supporting both sides
    of the associativity proof in Federer 4.1.11,
    p. 366. No measure representation, positivity,
    or finite-mass premise is added to any original current. *)
Lemma current_join_assoc_common_source_image:
  @current_degree_transport R h2 (n+(1+(n+(1+n))))%N (Full (n+(1+(n+(1+n))))%N)
    (hFull (n+(1+(n+(1+n))))%N) (i+(j+(2+k)))%N (i+(1+(j+(1+k))))%N
    (congr2 addn (erefl i) eInner)
    (@current_compact_map_pushforward R h2 (n+(n+(2+n)))%N (n+(1+(n+(1+n))))%N
      (Full (n+(n+(2+n)))%N) (Full (n+(1+(n+(1+n))))%N)
      (hFull (n+(n+(2+n)))%N) (hFull (n+(1+(n+(1+n))))%N)
      CommonMap Image CommonClass (i+(j+(2+k)))%N Common hCommon)=
  (-1:R)^+j*:Five.
Proof.
have hInner:=@current_join_assoc_inner_source_image R h2 n j k S T hS hT.
have hMap:forall x,B (A x)=InnerMap x.
  move=>x;by rewrite /current_join_assoc_inner_regroup hom_compE
    /current_join_assoc_inner_association euclidean_cartesian_linearE.
have hCompareInner:=@current_compact_map_images_agree R h2 (n+(2+n))%N (1+(n+(1+n)))%N
  (Full (n+(2+n))%N) (Full (1+(n+(1+n)))%N) (hFull (n+(2+n))%N) (hFull (1+(n+(1+n)))%N)
  (fun x=>B (A x)) OldImage OldClass (j+(2+k))%N InnerSource hInnerSource
  InnerMap AImage InnerClass hInnerSource (fun x _=>hMap x).
rewrite hCompareInner in hInner.
have hLift:=@current_ambient_product_second_image_equation R h2 n (n+(2+n))%N (1+(n+(1+n)))%N
  InnerMap InnerClass i (j+(2+k))%N P InnerSource hP hInnerSource
  (1+(j+(1+k)))%N eInner ((-1:R)^+j) InnerTarget hInnerTarget hInner.
have hCommonMap:forall x,ProductMap x=CommonMap x.
  move=>x;by rewrite /current_join_assoc_common_regroup euclidean_cartesian_linearE.
have hCompareCommon:=@current_compact_map_images_agree R h2
  (n+(n+(2+n)))%N (n+(1+(n+(1+n))))%N
  (Full (n+(n+(2+n)))%N) (Full (n+(1+(n+(1+n))))%N)
  (hFull (n+(n+(2+n)))%N) (hFull (n+(1+(n+(1+n))))%N)
  ProductMap Image ProductClass (i+(j+(2+k)))%N Common hCommon
  CommonMap Image CommonClass hCommon (fun x _=>hCommonMap x).
by rewrite hCompareCommon in hLift.
Qed.
End CurrentJoinAssociativityCommonImage.
