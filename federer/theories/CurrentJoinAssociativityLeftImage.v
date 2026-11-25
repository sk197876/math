(** Federer (1969), 4.1.11, p. 366: expand
    the literal left iterated join on the original five
    factors. Use the actual raw join, first-factor
    naturality and the preceding source association. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportComposition CurrentCompactPushforwardAlgebra
  CurrentCompactPushforwardImages CurrentCompactImageTransportEquation CurrentAmbientCartesianProduct
  CurrentAmbientFirstImageEquation CurrentCartesianMapClass CurrentJoinSliceMapClass CurrentJoinDomain
  CurrentJoinSourceCompact CurrentJoinSealed CurrentJoinLaws CurrentJoinMapSealed CurrentJoinMapClass
  CurrentJoinAmbientSource CurrentJoinAmbientImage CurrentJoinAssociativityIteratedMaps
  CurrentJoinAssociativityLeftSourceMaps CurrentJoinAssociativityLeftSourceImage SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_join_assoc_left_degree]: the original
    five-factor and left iterated-join degrees agree,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_left_degree i j k:
  (i+(1+(j+(1+k))))%N=((i+1+j)+1+k)%N.
Proof. by rewrite !addnA. Qed.

Section CurrentJoinAssociativityLeftImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j k:nat.
Local Notation dj := ((n+(1+n))%N).
Local Notation dl := ((dj+(1+n))%N).
Local Notation dm := ((n+((1+n)+(1+n)))%N).
Local Notation df := ((n+(1+dj))%N).
Local Notation d := ((i+(1+(j+(1+k))))%N).
Local Notation a := ((i+(1+j))%N).
Local Notation b := ((a+(1+k))%N).
Local Notation c := ((i+((1+j)+(1+k)))%N).
Local Notation Full := (fun l:nat=>fun _:R_n R l=>True).
Local Notation hFull := (fun (l:nat) (x:R_n R l) (_:True)=>
  @norm_full_domain_interior R (R_n R l) (inner_norm (@euclidean_inner_productP R l)) x).
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
Local Notation IS := (@current_ambient_cartesian_product R h2 1%N n 1%N j I S).
Local Notation hIS := (@current_ambient_cartesian_product_compact R h2 1%N n 1%N j I S hI hS).
Local Notation IT := (@current_ambient_cartesian_product R h2 1%N n 1%N k I T).
Local Notation hIT := (@current_ambient_cartesian_product_compact R h2 1%N n 1%N k I T hI hT).
Local Notation PS := (@current_ambient_cartesian_product R h2 n (1+n)%N i (1+j)%N P IS).
Local Notation hPS := (@current_ambient_cartesian_product_compact R h2 n (1+n)%N i (1+j)%N P IS hP hIS).
Local Notation Left := (@current_ambient_cartesian_product R h2 dj (1+n)%N a (1+k)%N PS IT).
Local Notation hLeft := (@current_ambient_cartesian_product_compact R h2 dj (1+n)%N a (1+k)%N PS IT hPS hIT).
Local Notation Two := (@current_ambient_cartesian_product R h2 (1+n)%N (1+n)%N (1+j)%N (1+k)%N IS IT).
Local Notation hTwo := (@current_ambient_cartesian_product_compact R h2 (1+n)%N (1+n)%N (1+j)%N (1+k)%N IS IT hIS hIT).
Local Notation Middle := (@current_ambient_cartesian_product R h2 n ((1+n)+(1+n))%N i ((1+j)+(1+k))%N P Two).
Local Notation hMiddle := (@current_ambient_cartesian_product_compact R h2 n ((1+n)+(1+n))%N i ((1+j)+(1+k))%N P Two hP hTwo).
Local Notation SIT := (@current_ambient_cartesian_product R h2 n (1+n)%N j (1+k)%N S IT).
Local Notation hSIT := (@current_ambient_cartesian_product_compact R h2 n (1+n)%N j (1+k)%N S IT hS hIT).
Local Notation ISIT := (@current_ambient_cartesian_product R h2 1%N dj 1%N (j+(1+k))%N I SIT).
Local Notation hISIT := (@current_ambient_cartesian_product_compact R h2 1%N dj 1%N (j+(1+k))%N I SIT hI hSIT).
Local Notation Five := (@current_ambient_cartesian_product R h2 n (1+dj)%N i (1+(j+(1+k)))%N P ISIT).
Local Notation hFive := (@current_ambient_cartesian_product_compact R h2 n (1+dj)%N i (1+(j+(1+k)))%N P ISIT hP hISIT).
Local Notation r := ((i+1+j)%N).
Local Notation J := (@CurrentJoin.value R h2 n i j P S hP hS).
Local Notation hJ := (@current_join_compact R h2 n i j P S hP hS).
Local Notation Outer := (@current_ambient_cartesian_product R h2 n (1+n)%N r (1+k)%N J IT).
Local Notation hOuter := (@current_ambient_cartesian_product_compact R h2 n (1+n)%N r (1+k)%N J IT hJ hIT).
Local Notation hPublicPS := (@current_join_ambient_source_compact R h2 n i j P S hP hS).
Local Notation hPublicOuter := (@current_join_ambient_source_compact R h2 n r k J T hJ hT).
Local Notation LeftJoin := (@CurrentJoin.value R h2 n r k J T hJ hT).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation hF := (@current_join_map_smooth R n (Full dj) (hFull dj)).
Local Notation Id := (fun x:R_n R (1+n)%N=>x).
Local Notation hId := (@current_join_slice_identity_smooth R (1+n)%N).
Local Notation MiddleMap := (@euclidean_cartesian_map R dj (1+n)%N n (1+n)%N F Id).
Local Notation MiddleClass := (@current_cartesian_map_smooth R dj (1+n)%N n (1+n)%N F Id hF hId).
Local Notation G := (fun x=>F (MiddleMap x)).
Local Notation hG := (@current_smooth_composite_class R dl dj n (Full dl) (Full dj)
  MiddleMap F (fun _ _=>Logic.I) MiddleClass hF).
Local Notation BackMap := (@current_join_assoc_left_regroup R n).
Local Notation BackClass := (@current_join_assoc_left_regroup_smooth R n).
Local Notation FImage := (fun (x:R_n R dj) (_:True)=>Logic.I).
Local Notation LeftImage := (fun (x:R_n R dl) (_:True)=>Logic.I).
Local Notation FiveImage := (fun (x:R_n R df) (_:True)=>Logic.I).
Local Notation RawImage := (@current_smooth_composite_image R dl dj n
  (Full dl) (Full dj) (Full n) MiddleMap F LeftImage FImage).
Local Notation CompositeImage := (@current_smooth_composite_image R df dl n
  (Full df) (Full dl) (Full n) BackMap G FiveImage LeftImage).
Local Notation CompositeClass := (@current_smooth_composite_class R df dl n
  (Full df) (Full dl) BackMap G FiveImage BackClass hG).
Local Notation ePS := (addnA i 1%N j).
Local Notation eProduct := (congr2 addn ePS (erefl (1+k)%N)).
Local Notation eOuter := (addnA r 1%N k).
Local Notation eRaw := (eq_trans eProduct eOuter).
Local Notation eBack := (current_join_assoc_left_source_degree i j k).

(** Source for [current_join_assoc_left_image]: the literal
    (R join S) join T is the image of the original
    R times I times S times I times T under
    F(F(x,a,y),b,z), with only its equal degree
    identified, Federer 4.1.11, p. 366. All three
    currents remain arbitrary and compactly supported. *)
Lemma current_join_assoc_left_image:
  LeftJoin=@current_degree_transport R h2 n (Full n) (hFull n) d (r+1+k)%N
    (current_join_assoc_left_degree i j k)
    (@current_compact_map_pushforward R h2 df n (Full df) (Full n) (hFull df) (hFull n)
      (@current_join_assoc_left_map R n) FiveImage (@current_join_assoc_left_map_smooth R n)
      d Five hFive).
Proof.
have hPSImage:=@current_join_ambient_image R h2 n i j P S hP hS.
have hComparePS:=@current_compact_map_pushforward_congruence R h2 dj n
  (Full dj) (Full n) (hFull dj) (hFull n) F FImage hF a PS PS
  hPublicPS hPS (erefl PS).
rewrite hComparePS in hPSImage.
have hPSCoefficient:=eq_trans (esym hPSImage) (esym (scale1r J)).
have hProduct:=@current_ambient_product_first_image_equation R h2 dj n (1+n)%N F hF
  a (1+k)%N PS IT hPS hIT r ePS (1:R) J hJ hPSCoefficient.
have hTransport:=@current_compact_image_transport_equation R h2 dl dj n MiddleMap F MiddleClass hF
  b Left hLeft (r+(1+k))%N eProduct (1:R) Outer hOuter hProduct.
rewrite scale1r in hTransport.
have hOuterImage:=@current_join_ambient_image R h2 n r k J T hJ hT.
have hCompareOuter:=@current_compact_map_pushforward_congruence R h2 dj n
  (Full dj) (Full n) (hFull dj) (hFull n) F FImage hF (r+(1+k))%N Outer Outer
  hPublicOuter hOuter (erefl Outer).
rewrite hCompareOuter in hOuterImage.
pose TrOuter:=@current_degree_transport R h2 n (Full n) (hFull n) (r+(1+k))%N (r+1+k)%N eOuter.
have hRaw:=congr1 TrOuter hTransport.
rewrite current_degree_transport_composition -hOuterImage in hRaw.
have hBack:=@current_join_assoc_left_source_image R h2 n i j k P S T hP hS hT.
have hBackCoefficient:=eq_trans hBack (esym (scale1r Left)).
have hTransfer:=@current_compact_image_transport_equation R h2 df dl n BackMap G BackClass hG
  d Five hFive b eBack (1:R) Left hLeft hBackCoefficient.
rewrite scale1r in hTransfer.
have hRawImage:RawImage=LeftImage:=Prop_irrelevance _ _.
rewrite hRawImage in hRaw.
pose TrRaw:=@current_degree_transport R h2 n (Full n) (hFull n) b (r+1+k)%N eRaw.
have hTotal:=congr1 TrRaw hTransfer.
rewrite current_degree_transport_composition hRaw in hTotal.
have hDegree:(eq_trans eBack eRaw)=current_join_assoc_left_degree i j k:=Prop_irrelevance _ _.
have hMaps:forall x,G (BackMap x)=@current_join_assoc_left_map R n x.
  move=>x;by rewrite /current_join_assoc_left_map.
have hCompare:=@current_compact_map_images_agree R h2 df n
  (Full df) (Full n) (hFull df) (hFull n) (fun x=>G (BackMap x)) CompositeImage CompositeClass
  d Five hFive (@current_join_assoc_left_map R n) FiveImage (@current_join_assoc_left_map_smooth R n)
  hFive (fun x _=>hMaps x).
rewrite hDegree hCompare in hTotal.
exact:esym hTotal.
Qed.
End CurrentJoinAssociativityLeftImage.
