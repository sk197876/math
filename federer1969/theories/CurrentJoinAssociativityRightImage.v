(** Federer (1969), 4.1.11, p. 366: expand
    the literal right iterated join as the image of
    the original ordered five-factor current. Reuse
    the actual raw join image, product naturality and
    proper composition, retaining every degree equality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportComposition CurrentCompactPushforwardAlgebra
  CurrentCompactPushforwardImages CurrentCompactImageTransportEquation CurrentAmbientCartesianProduct
  CurrentAmbientProductImageEquation CurrentCartesianMapClass CurrentJoinSliceMapClass CurrentJoinDomain
  CurrentJoinSourceCompact CurrentJoinSealed CurrentJoinLaws CurrentJoinMapSealed CurrentJoinMapClass
  CurrentJoinAmbientSource CurrentJoinAmbientImage CurrentJoinAssociativityIteratedMaps
  SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_join_assoc_right_degree]: the original
    five-factor degree and right iterated-join degree
    coincide, supporting Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_right_degree i j k:
  (i+(1+(j+(1+k))))%N=(i+1+(j+1+k))%N.
Proof. by rewrite !addnA. Qed.

Section CurrentJoinAssociativityRightImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j k:nat.
Local Notation dj := ((n+(1+n))%N).
Local Notation df := ((n+(1+dj))%N).
Local Notation q := ((j+(1+k))%N).
Local Notation r := ((j+1+k)%N).
Local Notation d := ((i+(1+q))%N).
Local Notation Full := (fun a:nat=>fun _:R_n R a=>True).
Local Notation hFull := (fun (a:nat) (x:R_n R a) (_:True)=>
  @norm_full_domain_interior R (R_n R a) (inner_norm (@euclidean_inner_productP R a)) x).
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
Local Notation IT := (@current_ambient_cartesian_product R h2 1%N n 1%N k I T).
Local Notation hIT := (@current_ambient_cartesian_product_compact R h2 1%N n 1%N k I T hI hT).
Local Notation SourceST := (@current_ambient_cartesian_product R h2 n (1+n)%N j (1+k)%N S IT).
Local Notation hSourceST := (@current_ambient_cartesian_product_compact R h2 n (1+n)%N j (1+k)%N S IT hS hIT).
Local Notation hPublicST := (@current_join_ambient_source_compact R h2 n j k S T hS hT).
Local Notation ISourceST := (@current_ambient_cartesian_product R h2 1%N dj 1%N q I SourceST).
Local Notation hISourceST := (@current_ambient_cartesian_product_compact R h2 1%N dj 1%N q I SourceST hI hSourceST).
Local Notation Five := (@current_ambient_cartesian_product R h2 n (1+dj)%N i (1+q)%N P ISourceST).
Local Notation hFive := (@current_ambient_cartesian_product_compact R h2 n (1+dj)%N i (1+q)%N P ISourceST hP hISourceST).
Local Notation J := (@CurrentJoin.value R h2 n j k S T hS hT).
Local Notation hJ := (@current_join_compact R h2 n j k S T hS hT).
Local Notation IJ := (@current_ambient_cartesian_product R h2 1%N n 1%N r I J).
Local Notation hIJ := (@current_ambient_cartesian_product_compact R h2 1%N n 1%N r I J hI hJ).
Local Notation OuterSource := (@current_ambient_cartesian_product R h2 n (1+n)%N i (1+r)%N P IJ).
Local Notation hOuterSource := (@current_ambient_cartesian_product_compact R h2 n (1+n)%N i (1+r)%N P IJ hP hIJ).
Local Notation hPublicOuter := (@current_join_ambient_source_compact R h2 n i r P J hP hJ).
Local Notation RightJoin := (@CurrentJoin.value R h2 n i r P J hP hJ).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation hF := (@current_join_map_smooth R n (Full dj) (hFull dj)).
Local Notation Id := (fun a:nat=>fun x:R_n R a=>x).
Local Notation hId := (@current_join_slice_identity_smooth R).
Local Notation Inner := (@euclidean_cartesian_map R 1%N dj 1%N n (Id 1%N) F).
Local Notation InnerClass := (@current_cartesian_map_smooth R 1%N dj 1%N n (Id 1%N) F (hId 1%N) hF).
Local Notation Middle := (@euclidean_cartesian_map R n (1+dj)%N n (1+n)%N (Id n) Inner).
Local Notation MiddleClass := (@current_cartesian_map_smooth R n (1+dj)%N n (1+n)%N
  (Id n) Inner (hId n) InnerClass).
Local Notation FImage := (fun (x:R_n R dj) (_:True)=>Logic.I).
Local Notation FiveImage := (fun (x:R_n R df) (_:True)=>Logic.I).
Local Notation CompositeImage := (@current_smooth_composite_image R df dj n
  (Full df) (Full dj) (Full n) Middle F FiveImage FImage).
Local Notation CompositeClass := (@current_smooth_composite_class R df dj n
  (Full df) (Full dj) Middle F FiveImage MiddleClass hF).
Local Notation eST := (addnA j 1%N k).
Local Notation eFirst := (congr2 addn (erefl 1%N) eST).
Local Notation eSecond := (congr2 addn (erefl i) eFirst).
Local Notation eOuter := (addnA i 1%N r).

(** Source for [current_join_assoc_right_image]: the literal
    R join (S join T) is the image of the original
    R times I times S times I times T under
    F(x,a,F(y,b,z)), with only its equal degree
    identified, Federer 4.1.11, p. 366. All three
    currents remain arbitrary and compactly supported. *)
Lemma current_join_assoc_right_image:
  RightJoin=@current_degree_transport R h2 n (Full n) (hFull n) d (i+1+r)%N
    (current_join_assoc_right_degree i j k)
    (@current_compact_map_pushforward R h2 df n (Full df) (Full n) (hFull df) (hFull n)
      (@current_join_assoc_right_map R n) FiveImage (@current_join_assoc_right_map_smooth R n)
      d Five hFive).
Proof.
have hST:=@current_join_ambient_image R h2 n j k S T hS hT.
have hCompareST:=@current_compact_map_pushforward_congruence R h2 dj n
  (Full dj) (Full n) (hFull dj) (hFull n) F FImage hF q SourceST SourceST
  hPublicST hSourceST (erefl SourceST).
rewrite hCompareST in hST.
have hSTCoefficient:=eq_trans (esym hST) (esym (scale1r J)).
have hFirst:=@current_ambient_product_second_image_equation R h2 1%N dj n F hF
  1%N q I SourceST hI hSourceST r eST (1:R) J hJ hSTCoefficient.
have hSecond:=@current_ambient_product_second_image_equation R h2 n (1+dj)%N (1+n)%N
  Inner InnerClass i (1+q)%N P ISourceST hP hISourceST (1+r)%N eFirst
  (1:R) IJ hIJ hFirst.
have hTransport:=@current_compact_image_transport_equation R h2 df dj n Middle F MiddleClass hF
  d Five hFive (i+(1+r))%N eSecond (1:R) OuterSource hOuterSource hSecond.
rewrite scale1r in hTransport.
have hOuter:=@current_join_ambient_image R h2 n i r P J hP hJ.
have hCompareOuter:=@current_compact_map_pushforward_congruence R h2 dj n
  (Full dj) (Full n) (hFull dj) (hFull n) F FImage hF (i+(1+r))%N OuterSource OuterSource
  hPublicOuter hOuterSource (erefl OuterSource).
rewrite hCompareOuter in hOuter.
pose Tr:=@current_degree_transport R h2 n (Full n) (hFull n) (i+(1+r))%N (i+1+r)%N eOuter.
have hTotal:=congr1 Tr hTransport.
rewrite current_degree_transport_composition -hOuter in hTotal.
have hDegree:(eq_trans eSecond eOuter)=current_join_assoc_right_degree i j k:=Prop_irrelevance _ _.
have hMaps:forall x,F (Middle x)=@current_join_assoc_right_map R n x.
  move=>x;by rewrite /current_join_assoc_right_map.
have hCompare:=@current_compact_map_images_agree R h2 df n
  (Full df) (Full n) (hFull df) (hFull n) (fun x=>F (Middle x)) CompositeImage CompositeClass
  d Five hFive (@current_join_assoc_right_map R n) FiveImage (@current_join_assoc_right_map_smooth R n)
  hFive (fun x _=>hMaps x).
rewrite hDegree hCompare in hTotal.
exact:esym hTotal.
Qed.
End CurrentJoinAssociativityRightImage.
