(** Federer (1969), 4.1.11, pp. 364–365: the join has
    positive degree i+j+1. Identify the equal natural degrees
    explicitly before taking its original current boundary.
    Every operation is an existing opaque product, join or
    proper pushforward; no new boundary is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentBoundary
  CurrentDegreeTransport CurrentDegreeTransportComposition
  CurrentProperSupport CurrentCompactMapProper CurrentPushforwardSealed
  CurrentPushforwardDegreeTransport CurrentPushforwardCongruence
  CurrentPushforwardBoundary CurrentJoinMapSealed CurrentJoinMapClass
  CurrentJoinDomain CurrentJoinSourceChain CurrentJoinSourceCompact
  CurrentJoinSealed CurrentJoinLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_join_degree_successor]: the printed
    join degree i+1+j equals the successor of i+j. This is only
    natural-number bookkeeping for Federer 4.1.11, pp. 364–365. *)
Lemma current_join_degree_successor i j:(i+1+j)%N=(i+j).+1.
Proof. by rewrite addn1 addSn. Qed.

Section CurrentJoinBoundaryDegree.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n i j : nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _ : X => True).
Local Notation Time := (fun _ : R_n R 1%N => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation hTime := (fun (t : R_n R 1%N) (_ : True) =>
  @norm_full_domain_interior R (R_n R 1%N) NT t).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace :=
  (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Variable S : @current_space R h2 n Full hFull i.
Variable T : @current_space R h2 n Full hFull j.
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation Inner :=
  (@CartesianCurrentProduct.value R h2 1%N n 1%N j
    Time Full hTime hFull Segment T).
Local Notation Chain := (@current_join_source_chain R h2 n i j S T).
Hypothesis hS : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull i S).
Hypothesis hT : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull j T).

Local Notation Raw := (@CartesianCurrentProduct.value R h2 n (1+n)%N
  i (1+j)%N Full TimeSpace hFull hTimeSpace S Inner).
Local Notation SourceTr := (fun a b (e:a=b)=>
  @current_degree_transport R h2 (n+(1+n))%N Domain hDomain a b e).
Local Notation TargetTr := (fun a b (e:a=b)=>
  @current_degree_transport R h2 n Full hFull a b e).
Local Notation eJoin := (current_join_degree_successor i j).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation Image := (@current_join_map_image R n).
Local Notation Smooth := (@current_join_map_smooth R n Domain hDomain).
Local Notation Proper := (@current_join_source_proper R h2 n i j S T hS hT).

(** Source for [current_join_successor_source]: the actual
    original source S times ([0,1] times T), identified with
    degree (i+j)+1 to take the boundary in Federer 4.1.11, p. 365. *)
Definition current_join_successor_source:=SourceTr _ _ (addnS i j) Raw.

(** Source for [current_join_successor_source_identification]:
    both associations of the original positive source degree
    give the same current, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_successor_source_identification:
  SourceTr _ _ eJoin Chain=current_join_successor_source.
Proof.
rewrite /current_join_source_chain current_degree_transport_composition.
have hProof:eq_trans (addnA i 1%N j) eJoin=addnS i j:=Prop_irrelevance _ _.
by rewrite hProof.
Qed.

(** Source for [current_join_successor_source_proper]: F is
    proper on the same actual source support after this degree
    identification, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_successor_source_proper:
  @is_current_proper_on_support R h2 (n+(1+n))%N n (i+j).+1
    Domain hDomain Full current_join_successor_source F Image.
Proof.
have h:=@current_degree_transport_proper R h2 (n+(1+n))%N n Domain Full hDomain
  F Image (i+1+j)%N (i+j).+1 eJoin Chain Proper.
by rewrite current_join_successor_source_identification in h.
Qed.

(** Source for [current_join_successor]: the original join,
    with its positive degree written (i+j)+1, supporting the four
    boundary formulas of Federer 4.1.11, p. 365. *)
Definition current_join_successor:=
  TargetTr _ _ eJoin (@CurrentJoin.value R h2 n i j S T hS hT).

(** Source for [current_join_successor_pushforward]: the original
    join remains F#(S times [0,1] times T) at the equal successor
    degree, supporting Federer 4.1.11, pp. 364–365. *)
Theorem current_join_successor_pushforward:
  current_join_successor=
  @CurrentPushforward.value R h2 (n+(1+n))%N n (i+j).+1
    Domain Full hDomain hFull current_join_successor_source
    F Image Smooth current_join_successor_source_proper.
Proof.
rewrite /current_join_successor current_join_pushforward.
pose hp:=@current_degree_transport_proper R h2 (n+(1+n))%N n Domain Full hDomain
  F Image (i+1+j)%N (i+j).+1 eJoin Chain Proper.
have hTransport:=@current_pushforward_degree_transport R h2 (n+(1+n))%N n
  Domain Full hDomain hFull F Image Smooth (i+1+j)%N (i+j).+1 eJoin Chain Proper hp.
have hCompare:=@current_pushforward_current_congruence R h2 (n+(1+n))%N n (i+j).+1
  Domain Full hDomain hFull F Image Smooth
  (SourceTr _ _ eJoin Chain) current_join_successor_source hp
  current_join_successor_source_proper current_join_successor_source_identification.
exact:(eq_trans hTransport hCompare).
Qed.

(** Source for [current_join_boundary]: the actual boundary
    of the original join, Federer 4.1.11, p. 365. Only equal
    positive degrees are identified; no degree-zero boundary is used. *)
Definition current_join_boundary:=
  @current_boundary R h2 n (i+j)%N Full hFull current_join_successor.

(** Source for [current_join_boundary_pushforward]: the join
    boundary is the original F pushforward of the source boundary,
    supporting all four formulas of Federer 4.1.11, p. 365. Reuse
    the preceding proper-pushforward boundary theorem. *)
Theorem current_join_boundary_pushforward:
  current_join_boundary=
  @CurrentPushforward.value R h2 (n+(1+n))%N n (i+j)%N
    Domain Full hDomain hFull
    (@current_boundary R h2 (n+(1+n))%N (i+j)%N Domain hDomain current_join_successor_source)
    F Image Smooth
    (@current_pushforward_boundary_proper R h2 (n+(1+n))%N n (i+j)%N
      Domain Full hDomain current_join_successor_source F Image
      current_join_successor_source_proper).
Proof.
rewrite /current_join_boundary current_join_successor_pushforward.
exact:current_pushforward_boundary.
Qed.
End CurrentJoinBoundaryDegree.
