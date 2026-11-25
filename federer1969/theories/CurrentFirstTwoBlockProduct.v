(** Federer (1969), 4.1.11, p. 366: the
    original adjacent time-space interchange has sign
    (-1)^(ij). Derive it from the preceding outer
    interchange, natural association and remaining inner
    interchange, retaining arbitrary compact current factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  EuclideanCartesianSwapLinear EuclideanDimensionCastLinear EuclideanCartesianLinear
  CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportComposition CurrentCompactPushforwardAlgebra
  CurrentCompactPushforwardImages CurrentCompactImageTransportEquation CurrentAmbientCartesianProduct
  CurrentAmbientProductSwap CurrentAmbientProductImageEquation CurrentCartesianMapClass
  CurrentJoinSliceMapClass CurrentFirstTwoBlockInterchange CurrentFirstTwoBlockSourceImage
  SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_first_two_block_sign]: the two
    original interchange exponents reduce to ij because
    their two ik contributions cancel, supporting the
    product reordering in Federer 4.1.11, p. 366. *)
Lemma current_first_two_block_sign (R:realType) i j k:
  (-1:R)^+(i*(j+k))*(-1:R)^+(k*i)=(-1:R)^+(i*j).
Proof. by rewrite mulnDr exprD [(k*i)%N]mulnC -mulrA -expr2 sqrr_sign mulr1. Qed.

Section CurrentFirstTwoBlockProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n v i j k:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables (S:@current_space R h2 m (Full m) (hFull m) i)
  (T:@current_space R h2 n (Full n) (hFull n) j)
  (U:@current_space R h2 v (Full v) (hFull v) k).
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) i S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j T).
Hypothesis hU:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R v)))
  (@current_support R h2 v (Full v) (hFull v) k U).
Local Notation TU := (@current_ambient_cartesian_product R h2 n v j k T U).
Local Notation US := (@current_ambient_cartesian_product R h2 v m k i U S).
Local Notation SU := (@current_ambient_cartesian_product R h2 m v i k S U).
Local Notation hTU := (@current_ambient_cartesian_product_compact R h2 n v j k T U hT hU).
Local Notation hUS := (@current_ambient_cartesian_product_compact R h2 v m k i U S hU hS).
Local Notation hSU := (@current_ambient_cartesian_product_compact R h2 m v i k S U hS hU).
Local Notation Source := (@current_ambient_cartesian_product R h2 m (n+v)%N i (j+k)%N S TU).
Local Notation hSource := (@current_ambient_cartesian_product_compact R h2 m (n+v)%N i (j+k)%N S TU hS hTU).
Local Notation MiddleCurrent := (@current_ambient_cartesian_product R h2 n (v+m)%N j (k+i)%N T US).
Local Notation hMiddleCurrent := (@current_ambient_cartesian_product_compact R h2 n (v+m)%N j (k+i)%N T US hT hUS).
Local Notation Target := (@current_ambient_cartesian_product R h2 n (m+v)%N j (i+k)%N T SU).
Local Notation Outer := (@euclidean_cartesian_swap_map R m (n+v)%N).
Local Notation OuterClass := (@euclidean_cartesian_swap_smooth R m (n+v)%N
  (Full (m+(n+v))%N) (hFull (m+(n+v))%N)).
Local Notation Assoc := (@euclidean_dimension_cast_map R ((n+v)+m)%N (n+(v+m))%N (esym (addnA n v m))).
Local Notation AssocClass := (@euclidean_dimension_cast_smooth R ((n+v)+m)%N (n+(v+m))%N
  (esym (addnA n v m)) (Full ((n+v)+m)%N) (hFull ((n+v)+m)%N)).
Local Notation OImage := (fun (x:R_n R (m+(n+v))%N) (_:True)=>Logic.I).
Local Notation AImage := (fun (x:R_n R ((n+v)+m)%N) (_:True)=>Logic.I).
Local Notation Middle := (fun x=>Assoc (Outer x)).
Local Notation MiddleClass := (@current_smooth_composite_class R (m+(n+v))%N ((n+v)+m)%N (n+(v+m))%N
  (Full (m+(n+v))%N) (Full ((n+v)+m)%N) Outer Assoc OImage OuterClass AssocClass).
Local Notation Inner := (@euclidean_cartesian_swap_map R v m).
Local Notation InnerClass := (@euclidean_cartesian_swap_smooth R v m (Full (v+m)%N) (hFull (v+m)%N)).
Local Notation Id := (fun x:R_n R n=>x).
Local Notation IdClass := (@current_join_slice_identity_smooth R n).
Local Notation Tail := (@euclidean_cartesian_map R n (v+m)%N n (m+v)%N Id Inner).
Local Notation TailClass := (@current_cartesian_map_smooth R n (v+m)%N n (m+v)%N Id Inner IdClass InnerClass).
Local Notation TailImage := (fun (x:R_n R (n+(v+m))%N) (_:True)=>Logic.I).
Local Notation CompositeImage := (@current_smooth_composite_image R (m+(n+v))%N (n+(v+m))%N (n+(m+v))%N
  (Full (m+(n+v))%N) (Full (n+(v+m))%N) (Full (n+(m+v))%N) Middle Tail OImage TailImage).
Local Notation CompositeClass := (@current_smooth_composite_class R (m+(n+v))%N (n+(v+m))%N (n+(m+v))%N
  (Full (m+(n+v))%N) (Full (n+(v+m))%N) Middle Tail OImage MiddleClass TailClass).
Local Notation e12 := (eq_trans (addnC i (j+k)%N) (esym (addnA j k i))).
Local Notation e3 := (congr2 addn (erefl j) (addnC k i)).

(** Source for [current_first_two_block_tail_image]: the
    last original interchange fixes T and swaps U,S,
    with exact sign (-1)^(ki), supporting Federer
    4.1.11, p. 366. *)
Lemma current_first_two_block_tail_image:
  @current_degree_transport R h2 (n+(m+v))%N (Full (n+(m+v))%N) (hFull (n+(m+v))%N)
    (j+(k+i))%N (j+(i+k))%N e3
    (@current_compact_map_pushforward R h2 (n+(v+m))%N (n+(m+v))%N
      (Full (n+(v+m))%N) (Full (n+(m+v))%N) (hFull (n+(v+m))%N) (hFull (n+(m+v))%N)
      Tail TailImage TailClass (j+(k+i))%N MiddleCurrent hMiddleCurrent)=
  (-1:R)^+(k*i)*:Target.
Proof.
have hInner:=@current_ambient_product_swap R h2 v m k i U S hU hS.
exact:(@current_ambient_product_second_image_equation R h2 n (v+m)%N (m+v)%N
  Inner InnerClass j (k+i)%N T US hT hUS (i+k)%N (addnC k i) ((-1:R)^+(k*i)) SU hSU hInner).
Qed.

(** Source for [current_first_two_block_product]: the original
    (x,y,z) to (y,x,z) map sends S times (T times U)
    to (-1)^(ij) T times (S times U), supporting
    the exact time-factor reordering in Federer
    4.1.11, p. 366. The inputs retain arbitrary
    compact supports, all degrees and all Euclidean dimensions. *)
Lemma current_first_two_block_product:
  @current_degree_transport R h2 (n+(m+v))%N (Full (n+(m+v))%N) (hFull (n+(m+v))%N)
    (i+(j+k))%N (j+(i+k))%N (addnCA i j k)
    (@current_compact_map_pushforward R h2 (m+(n+v))%N (n+(m+v))%N
      (Full (m+(n+v))%N) (Full (n+(m+v))%N) (hFull (m+(n+v))%N) (hFull (n+(m+v))%N)
      (@current_first_two_block_interchange R m n v) OImage
      (@current_first_two_block_smooth R m n v) (i+(j+k))%N Source hSource)=
  (-1:R)^+(i*j)*:Target.
Proof.
have hFirst:=@current_first_two_block_source_image R h2 m n v i j k S T U hS hT hU.
have hFirstImage:(@current_smooth_composite_image R (m+(n+v))%N ((n+v)+m)%N (n+(v+m))%N
  (Full (m+(n+v))%N) (Full ((n+v)+m)%N) (Full (n+(v+m))%N) Outer Assoc OImage AImage)=OImage:=Prop_irrelevance _ _.
rewrite hFirstImage in hFirst.
have hTransport:=@current_compact_image_transport_equation R h2
  (m+(n+v))%N (n+(v+m))%N (n+(m+v))%N Middle Tail MiddleClass TailClass
  (i+(j+k))%N Source hSource (j+(k+i))%N e12 ((-1:R)^+(i*(j+k)))
  MiddleCurrent hMiddleCurrent hFirst.
pose Tr:=@current_degree_transport R h2 (n+(m+v))%N (Full (n+(m+v))%N) (hFull (n+(m+v))%N)
  (j+(k+i))%N (j+(i+k))%N e3.
have hTotal:=congr1 Tr hTransport.
rewrite current_degree_transport_composition (linZ (hom_linear Tr))
  current_first_two_block_tail_image scalerA current_first_two_block_sign in hTotal.
have hDegree:(eq_trans e12 e3)=addnCA i j k:=Prop_irrelevance _ _.
have hMaps:forall x,Tail (Middle x)=@current_first_two_block_interchange R m n v x.
  move=>x;by rewrite /current_first_two_block_interchange !hom_compE euclidean_cartesian_linearE.
have hCompare:=@current_compact_map_images_agree R h2 (m+(n+v))%N (n+(m+v))%N
  (Full (m+(n+v))%N) (Full (n+(m+v))%N) (hFull (m+(n+v))%N) (hFull (n+(m+v))%N)
  (fun x=>Tail (Middle x)) CompositeImage CompositeClass (i+(j+k))%N Source hSource
  (@current_first_two_block_interchange R m n v) OImage (@current_first_two_block_smooth R m n v)
  hSource (fun x _=>hMaps x).
by rewrite hDegree hCompare in hTotal.
Qed.
End CurrentFirstTwoBlockProduct.
