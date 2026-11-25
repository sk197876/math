(** Federer (1969), 4.1.11, p. 365: when S has degree
    zero, take the boundary of S times ([0,1] times T).
    Reuse the original zero-first-degree Cartesian rule,
    segment boundary and the proved insertion current identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric
  NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanCartesianMap CurrentSpaces CurrentBoundary CurrentDirac
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianProductBilinear
  CurrentCartesianBoundarySecondZero CurrentDegreeTransport CurrentDegreeTransportIdentity
  CurrentSegmentMapUP OrientedSegmentCurrentSealed OrientedSegmentProductBoundary
  CurrentJoinDomain CurrentJoinSourceChain CurrentJoinBoundaryDegree CurrentJoinSliceProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinSourceBoundaryFirstZero.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n j : nat.
Local Notation X := (R_n R n).
Local Notation Source := (R_n R (n+n)%N).
Local Notation Target := (R_n R (n+(1+n))%N).
Local Notation Full := (fun _ : X => True).
Local Notation Time := (fun _ : R_n R 1%N => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation hTime := (fun (x : R_n R 1%N) (_ : True) =>
  @norm_full_domain_interior R (R_n R 1%N) NT x).
Local Notation AB := (@euclidean_cartesian_set R n n Full Full).
Local Notation hAB :=
  (@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace :=
  (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Local Notation C := (fun k=>@current_space R h2 n Full hFull k).
Local Notation Compact := (fun k (T:C k)=>@compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull k T)).
Local Notation P := (fun a b=>@CartesianCurrentProduct.value R h2 n (1+n)%N
  a b Full TimeSpace hFull hTimeSpace).
Local Notation Q := (fun a b=>@CartesianCurrentProduct.value R h2 1%N n
  a b Time Full hTime hFull).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation e0 := (@euclidean_one_embed R 0).
Local Notation e1 := (@euclidean_one_embed R 1).
Local Notation hSegment := (@current_join_time_segment_domain R).

(** Source for [current_join_source_boundary_first_zero_positive]:
    for i=0<j the source boundary has the two inserted endpoint
    products minus S times [0,1] times boundary T. This is the
    original source calculation behind the third boundary formula
    of Federer 4.1.11, p. 365. *)
Theorem current_join_source_boundary_first_zero_positive
    (S:C 0%N) (T:C j.+1) (hS:Compact 0%N S) (hT:Compact j.+1 T):
  @current_boundary R h2 (n+(1+n))%N j.+1 Domain hDomain
    (@current_join_successor_source R h2 n 0%N j.+1 S T)=
  @current_join_slice_current R h2 n 0%N j.+1 S T hS hT 1-
  @current_join_slice_current R h2 n 0%N j.+1 S T hS hT 0-
  @current_join_source_chain R h2 n 0%N j S
    (@current_boundary R h2 n j Full hFull T).
Proof.
have hInner:=@oriented_segment_product_boundary_positive R h2 1%N n
  Time Full hTime hFull e0 e1 hSegment j T.
have hOuter:=@current_cartesian_boundary_second_zero R h2 n (1+n)%N
  Full TimeSpace hFull hTimeSpace j.+1 S (Q 1%N j.+1 Segment T).
rewrite current_degree_transport_identity hInner
  !(bilBr (@current_cartesian_product_bilinear R h2 n (1+n)%N
    0%N j.+1 Full TimeSpace hFull hTimeSpace)) in hOuter.
rewrite /current_join_successor_source current_degree_transport_identity.
rewrite -(@current_join_slice_product R h2 n 0%N j.+1 S T hS hT 1)
  -(@current_join_slice_product R h2 n 0%N j.+1 S T hS hT 0).
rewrite /current_join_source_chain current_degree_transport_identity.
exact:hOuter.
Qed.

(** Source for [current_join_source_boundary_both_zero]:
    for i=j=0 the source boundary consists of its two inserted
    endpoint products, supporting the fourth boundary formula of
    Federer 4.1.11, p. 365. Neither zero current is differentiated. *)
Theorem current_join_source_boundary_both_zero
    (S:C 0%N) (T:C 0%N) (hS:Compact 0%N S) (hT:Compact 0%N T):
  @current_boundary R h2 (n+(1+n))%N 0%N Domain hDomain
    (@current_join_successor_source R h2 n 0%N 0%N S T)=
  @current_join_slice_current R h2 n 0%N 0%N S T hS hT 1-
  @current_join_slice_current R h2 n 0%N 0%N S T hS hT 0.
Proof.
have hInner:=@oriented_segment_product_boundary_zero R h2 1%N n
  Time Full hTime hFull e0 e1 hSegment T.
have hOuter:=@current_cartesian_boundary_second_zero R h2 n (1+n)%N
  Full TimeSpace hFull hTimeSpace 0%N S (Q 1%N 0%N Segment T).
rewrite current_degree_transport_identity hInner
  (bilBr (@current_cartesian_product_bilinear R h2 n (1+n)%N
    0%N 0%N Full TimeSpace hFull hTimeSpace)) in hOuter.
rewrite /current_join_successor_source current_degree_transport_identity.
rewrite -(@current_join_slice_product R h2 n 0%N 0%N S T hS hT 1)
  -(@current_join_slice_product R h2 n 0%N 0%N S T hS hT 0).
exact:hOuter.
Qed.
End CurrentJoinSourceBoundaryFirstZero.
