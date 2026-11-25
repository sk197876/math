(** Federer (1969), 4.1.11, p. 366: the
    common square and spatial factors give the original
    inner time-space order with sign (-1)^j. Reuse
    the preceding Cartesian association and adjacent
    interchange; the currents remain arbitrary and compact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  EuclideanDimensionCastLinear CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportComposition
  CurrentCompactPushforwardAlgebra CurrentCompactImageTransportEquation CurrentAmbientCartesianProduct
  CurrentAmbientProductAssociation CurrentAmbientProductImageEquation CurrentCartesianMapClass
  CurrentJoinSliceMapClass CurrentJoinDomain CurrentJoinSourceCompact CurrentFirstTwoBlockInterchange
  CurrentFirstTwoBlockProduct SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinAssociativityInnerImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j k:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables (S:@current_space R h2 n (Full n) (hFull n) j)
  (T:@current_space R h2 n (Full n) (hFull n) k).
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) k T).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_segment_compact R h2).
Local Notation Square := (@current_ambient_cartesian_product R h2 1%N 1%N 1%N 1%N I I).
Local Notation hSquare := (@current_ambient_cartesian_product_compact R h2 1%N 1%N 1%N 1%N I I hI hI).
Local Notation IT := (@current_ambient_cartesian_product R h2 1%N n 1%N k I T).
Local Notation hIT := (@current_ambient_cartesian_product_compact R h2 1%N n 1%N k I T hI hT).
Local Notation IIT := (@current_ambient_cartesian_product R h2 1%N (1+n)%N 1%N (1+k)%N I IT).
Local Notation hIIT := (@current_ambient_cartesian_product_compact R h2 1%N (1+n)%N 1%N (1+k)%N I IT hI hIT).
Local Notation SquareT := (@current_ambient_cartesian_product R h2 2%N n 2%N k Square T).
Local Notation hSquareT := (@current_ambient_cartesian_product_compact R h2 2%N n 2%N k Square T hSquare hT).
Local Notation Source := (@current_ambient_cartesian_product R h2 n (2+n)%N j (2+k)%N S SquareT).
Local Notation hSource := (@current_ambient_cartesian_product_compact R h2 n (2+n)%N j (2+k)%N S SquareT hS hSquareT).
Local Notation Associated := (@current_ambient_cartesian_product R h2 n (1+(1+n))%N j (1+(1+k))%N S IIT).
Local Notation hAssociated := (@current_ambient_cartesian_product_compact R h2 n (1+(1+n))%N j (1+(1+k))%N S IIT hS hIIT).
Local Notation SIT := (@current_ambient_cartesian_product R h2 n (1+n)%N j (1+k)%N S IT).
Local Notation Target := (@current_ambient_cartesian_product R h2 1%N (n+(1+n))%N 1%N (j+(1+k))%N I SIT).
Local Notation Assoc := (@euclidean_dimension_cast_map R ((1+1)+n)%N (1+(1+n))%N (esym (addnA 1%N 1%N n))).
Local Notation AssocClass := (@euclidean_dimension_cast_smooth R ((1+1)+n)%N (1+(1+n))%N
  (esym (addnA 1%N 1%N n)) (Full (2+n)%N) (hFull (2+n)%N)).
Local Notation Id := (fun x:R_n R n=>x).
Local Notation IdClass := (@current_join_slice_identity_smooth R n).
Local Notation A := (@euclidean_cartesian_map R n (2+n)%N n (1+(1+n))%N Id Assoc).
Local Notation AClass := (@current_cartesian_map_smooth R n (2+n)%N n (1+(1+n))%N Id Assoc IdClass AssocClass).
Local Notation B := (@current_first_two_block_interchange R n 1%N (1+n)%N).
Local Notation BClass := (@current_first_two_block_smooth R n 1%N (1+n)%N).
Local Notation AImage := (fun (x:R_n R (n+(2+n))%N) (_:True)=>Logic.I).
Local Notation BImage := (fun (x:R_n R (n+(1+(1+n)))%N) (_:True)=>Logic.I).
Local Notation CompositeImage := (@current_smooth_composite_image R (n+(2+n))%N (n+(1+(1+n)))%N (1+(n+(1+n)))%N
  (Full (n+(2+n))%N) (Full (n+(1+(1+n)))%N) (Full (1+(n+(1+n)))%N) A B AImage BImage).
Local Notation CompositeClass := (@current_smooth_composite_class R (n+(2+n))%N (n+(1+(1+n)))%N (1+(n+(1+n)))%N
  (Full (n+(2+n))%N) (Full (n+(1+(1+n)))%N) A B AImage AClass BClass).
Local Notation eA := (congr2 addn (erefl j) (esym (addnA 1%N 1%N k))).
Local Notation eB := (addnCA j 1%N (1+k)%N).

(** Source for [current_join_assoc_inner_source_image]: the
    common S times (square times T) current gives
    (-1)^j I times (S times (I times T)),
    supporting both original compositions in Federer
    4.1.11, p. 366. All original compact currents,
    degrees and zero-dimensional spatial spaces remain allowed. *)
Lemma current_join_assoc_inner_source_image:
  @current_degree_transport R h2 (1+(n+(1+n)))%N (Full (1+(n+(1+n)))%N) (hFull (1+(n+(1+n)))%N)
    (j+(2+k))%N (1+(j+(1+k)))%N (eq_trans eA eB)
    (@current_compact_map_pushforward R h2 (n+(2+n))%N (1+(n+(1+n)))%N
      (Full (n+(2+n))%N) (Full (1+(n+(1+n)))%N) (hFull (n+(2+n))%N) (hFull (1+(n+(1+n)))%N)
      (fun x=>B (A x)) CompositeImage CompositeClass (j+(2+k))%N Source hSource)=
  (-1:R)^+j*:Target.
Proof.
have hAssoc:=@current_ambient_product_association R h2 1%N 1%N n 1%N 1%N k I I T hI hI hT.
have hAssocCoefficient:=eq_trans hAssoc (esym (scale1r IIT)).
have hFirst:=@current_ambient_product_second_image_equation R h2 n (2+n)%N (1+(1+n))%N
  Assoc AssocClass j (2+k)%N S SquareT hS hSquareT (1+(1+k))%N
  (esym (addnA 1%N 1%N k)) (1:R) IIT hIIT hAssocCoefficient.
have hInterchange:=@current_first_two_block_product R h2 n 1%N (1+n)%N
  j 1%N (1+k)%N S I IT hS hI hIT.
rewrite muln1 in hInterchange.
have hTransport:=@current_compact_image_transport_equation R h2
  (n+(2+n))%N (n+(1+(1+n)))%N (1+(n+(1+n)))%N A B AClass BClass
  (j+(2+k))%N Source hSource (j+(1+(1+k)))%N eA (1:R) Associated hAssociated hFirst.
rewrite scale1r in hTransport.
pose Tr:=@current_degree_transport R h2 (1+(n+(1+n)))%N (Full (1+(n+(1+n)))%N)
  (hFull (1+(n+(1+n)))%N) (j+(1+(1+k)))%N (1+(j+(1+k)))%N eB.
have hTotal:=congr1 Tr hTransport.
rewrite current_degree_transport_composition hInterchange in hTotal.
exact:hTotal.
Qed.
End CurrentJoinAssociativityInnerImage.
