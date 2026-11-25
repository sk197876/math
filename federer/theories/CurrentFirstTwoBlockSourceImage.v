(** Federer (1969), 4.1.11, p. 366: the
    first two original product reorderings move S past
    T times U and then naturally associate the factors.
    Retain the exact original sign and all degrees. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  EuclideanCartesianSwapLinear EuclideanDimensionCastLinear CurrentSpaces CurrentDegreeTransport
  CurrentDegreeTransportComposition CurrentAmbientCartesianProduct CurrentAmbientProductSwap
  CurrentAmbientProductAssociation CurrentCompactPushforwardAlgebra CurrentCompactImageTransportEquation
  SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFirstTwoBlockSourceImage.
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
Local Notation hTU := (@current_ambient_cartesian_product_compact R h2 n v j k T U hT hU).
Local Notation hUS := (@current_ambient_cartesian_product_compact R h2 v m k i U S hU hS).
Local Notation Source := (@current_ambient_cartesian_product R h2 m (n+v)%N i (j+k)%N S TU).
Local Notation hSource := (@current_ambient_cartesian_product_compact R h2 m (n+v)%N i (j+k)%N S TU hS hTU).
Local Notation Swapped := (@current_ambient_cartesian_product R h2 (n+v)%N m (j+k)%N i TU S).
Local Notation hSwapped := (@current_ambient_cartesian_product_compact R h2 (n+v)%N m (j+k)%N i TU S hTU hS).
Local Notation Target := (@current_ambient_cartesian_product R h2 n (v+m)%N j (k+i)%N T US).
Local Notation Outer := (@euclidean_cartesian_swap_map R m (n+v)%N).
Local Notation OuterClass := (@euclidean_cartesian_swap_smooth R m (n+v)%N
  (Full (m+(n+v))%N) (hFull (m+(n+v))%N)).
Local Notation Assoc := (@euclidean_dimension_cast_map R ((n+v)+m)%N (n+(v+m))%N (esym (addnA n v m))).
Local Notation AssocClass := (@euclidean_dimension_cast_smooth R ((n+v)+m)%N (n+(v+m))%N
  (esym (addnA n v m)) (Full ((n+v)+m)%N) (hFull ((n+v)+m)%N)).
Local Notation OImage := (fun (x:R_n R (m+(n+v))%N) (_:True)=>Logic.I).
Local Notation AImage := (fun (x:R_n R ((n+v)+m)%N) (_:True)=>Logic.I).
Local Notation CompositeImage := (@current_smooth_composite_image R (m+(n+v))%N ((n+v)+m)%N (n+(v+m))%N
  (Full (m+(n+v))%N) (Full ((n+v)+m)%N) (Full (n+(v+m))%N) Outer Assoc OImage AImage).
Local Notation CompositeClass := (@current_smooth_composite_class R (m+(n+v))%N ((n+v)+m)%N (n+(v+m))%N
  (Full (m+(n+v))%N) (Full ((n+v)+m)%N) Outer Assoc OImage OuterClass AssocClass).
Local Notation e1 := (addnC i (j+k)%N).
Local Notation e2 := (esym (addnA j k i)).

(** Source for [current_first_two_block_source_image]: the
    first two original reorderings send S times (T times U)
    to (-1)^(i(j+k)) T times (U times S),
    supporting the time-factor argument in Federer
    4.1.11, p. 366. Only the corresponding natural
    degree equalities are composed. *)
Lemma current_first_two_block_source_image:
  @current_degree_transport R h2 (n+(v+m))%N (Full (n+(v+m))%N) (hFull (n+(v+m))%N)
    (i+(j+k))%N (j+(k+i))%N (eq_trans e1 e2)
    (@current_compact_map_pushforward R h2 (m+(n+v))%N (n+(v+m))%N
      (Full (m+(n+v))%N) (Full (n+(v+m))%N) (hFull (m+(n+v))%N) (hFull (n+(v+m))%N)
      (fun x=>Assoc (Outer x)) CompositeImage CompositeClass (i+(j+k))%N Source hSource)=
  (-1:R)^+(i*(j+k))*:Target.
Proof.
have hSwap:=@current_ambient_product_swap R h2 m (n+v)%N i (j+k)%N S TU hS hTU.
have hTransport:=@current_compact_image_transport_equation R h2
  (m+(n+v))%N ((n+v)+m)%N (n+(v+m))%N Outer Assoc OuterClass AssocClass
  (i+(j+k))%N Source hSource ((j+k)+i)%N e1 ((-1:R)^+(i*(j+k))) Swapped hSwapped hSwap.
have hAssoc:=@current_ambient_product_association R h2 n v m j k i T U S hT hU hS.
pose Tr:=@current_degree_transport R h2 (n+(v+m))%N (Full (n+(v+m))%N) (hFull (n+(v+m))%N)
  ((j+k)+i)%N (j+(k+i))%N e2.
have hTotal:=congr1 Tr hTransport.
rewrite current_degree_transport_composition (linZ (hom_linear Tr)) hAssoc in hTotal.
exact:hTotal.
Qed.
End CurrentFirstTwoBlockSourceImage.
