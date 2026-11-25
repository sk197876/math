(** Federer (1969), 4.1.11, p. 366: naturally
    group the original five factors into the source of
    the left iterated join. The preceding Cartesian
    associativity theorem and its inverse suffice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  EuclideanDimensionCastLinear CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportComposition
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages CurrentCompactImageTransportEquation
  CurrentCompactInverseImageEquation CurrentAmbientCartesianProduct CurrentAmbientProductAssociation
  CurrentAmbientProductImageEquation CurrentCartesianMapClass CurrentJoinSliceMapClass
  CurrentJoinDomain CurrentJoinSourceCompact CurrentJoinAssociativityIteratedMaps
  CurrentJoinAssociativityLeftSourceMaps SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_join_assoc_left_source_degree]: natural
    association preserves the original total degree,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_left_source_degree i j k:
  (i+(1+(j+(1+k))))%N=((i+(1+j))+(1+k))%N.
Proof. by rewrite !addnA. Qed.

Section CurrentJoinAssociativityLeftSourceImage.
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
Local Notation First := (@euclidean_dimension_cast_map R dl dm (esym (addnA n (1+n)%N (1+n)%N))).
Local Notation FirstClass := (@euclidean_dimension_cast_smooth R dl dm
  (esym (addnA n (1+n)%N (1+n)%N)) (Full dl) (hFull dl)).
Local Notation Inner := (@euclidean_dimension_cast_map R ((1+n)+(1+n))%N (1+dj)%N
  (esym (addnA 1%N n (1+n)%N))).
Local Notation InnerClass := (@euclidean_dimension_cast_smooth R ((1+n)+(1+n))%N (1+dj)%N
  (esym (addnA 1%N n (1+n)%N)) (Full ((1+n)+(1+n))%N) (hFull ((1+n)+(1+n))%N)).
Local Notation Id := (fun x:R_n R n=>x).
Local Notation Second := (@euclidean_cartesian_map R n ((1+n)+(1+n))%N n (1+dj)%N Id Inner).
Local Notation SecondClass := (@current_cartesian_map_smooth R n ((1+n)+(1+n))%N n (1+dj)%N
  Id Inner (@current_join_slice_identity_smooth R n) InnerClass).
Local Notation Forward := (@current_join_assoc_forward_source R n).
Local Notation ForwardClass := (@current_join_assoc_forward_source_smooth R n).
Local Notation BackMap := (@current_join_assoc_left_regroup R n).
Local Notation BackClass := (@current_join_assoc_left_regroup_smooth R n).
Local Notation LeftImage := (fun (x:R_n R dl) (_:True)=>Logic.I).
Local Notation FiveImage := (fun (x:R_n R df) (_:True)=>Logic.I).
Local Notation CompositeImage := (@current_smooth_composite_image R dl dm df
  (Full dl) (Full dm) (Full df) First Second LeftImage (fun _ _=>Logic.I)).
Local Notation CompositeClass := (@current_smooth_composite_class R dl dm df
  (Full dl) (Full dm) First Second LeftImage FirstClass SecondClass).
Local Notation eFirst := (esym (addnA i (1+j)%N (1+k)%N)).
Local Notation eInner := (esym (addnA 1%N j (1+k)%N)).
Local Notation eSecond := (congr2 addn (erefl i) eInner).
Local Notation eTotal := (eq_trans eFirst eSecond).

(** Source for [current_join_assoc_left_source_image]: the
    original five-factor current has precisely the left
    join's original raw source under reverse association,
    Federer 4.1.11, p. 366. Only equal degrees are
    identified, and all three currents remain arbitrary. *)
Lemma current_join_assoc_left_source_image:
  @current_degree_transport R h2 dl (Full dl) (hFull dl) d b
    (current_join_assoc_left_source_degree i j k)
    (@current_compact_map_pushforward R h2 df dl (Full df) (Full dl) (hFull df) (hFull dl)
      BackMap FiveImage BackClass d Five hFive)=Left.
Proof.
have hFirst:=@current_ambient_product_association R h2 n (1+n)%N (1+n)%N
  i (1+j)%N (1+k)%N P IS IT hP hIS hIT.
have hInner:=@current_ambient_product_association R h2 1%N n (1+n)%N
  1%N j (1+k)%N I S IT hI hS hIT.
have hInnerCoefficient:=eq_trans hInner (esym (scale1r ISIT)).
have hSecond:=@current_ambient_product_second_image_equation R h2 n ((1+n)+(1+n))%N (1+dj)%N
  Inner InnerClass i ((1+j)+(1+k))%N P Two hP hTwo (1+(j+(1+k)))%N eInner
  (1:R) ISIT hISIT hInnerCoefficient.
have hFirstCoefficient:=eq_trans hFirst (esym (scale1r Middle)).
have hTransport:=@current_compact_image_transport_equation R h2 dl dm df First Second FirstClass SecondClass
  b Left hLeft c eFirst (1:R) Middle hMiddle hFirstCoefficient.
rewrite scale1r in hTransport.
pose Tr:=@current_degree_transport R h2 df (Full df) (hFull df) c d eSecond.
have hForward:=congr1 Tr hTransport.
rewrite current_degree_transport_composition hSecond scale1r in hForward.
have hMaps:forall x,Second (First x)=Forward x.
  move=>x;by rewrite /current_join_assoc_forward_source.
have hCompare:=@current_compact_map_images_agree R h2 dl df
  (Full dl) (Full df) (hFull dl) (hFull df) (fun x=>Second (First x)) CompositeImage CompositeClass
  b Left hLeft Forward LeftImage ForwardClass hLeft (fun x _=>hMaps x).
rewrite hCompare in hForward.
have hReverse:=@current_compact_inverse_image_equation R h2 dl df Forward BackMap ForwardClass BackClass
  (@current_join_assoc_forward_source_inverse R n) b Left hLeft d eTotal Five hFive hForward.
have hDegree:esym eTotal=current_join_assoc_left_source_degree i j k:=Prop_irrelevance _ _.
by rewrite hDegree in hReverse.
Qed.
End CurrentJoinAssociativityLeftSourceImage.
