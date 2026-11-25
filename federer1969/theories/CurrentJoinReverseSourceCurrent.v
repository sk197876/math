(** Federer (1969), 4.1.11, p. 365: write the original
    p pushforward in the printed source-chain degrees i+1+j
    and j+1+i. The complete raw reversing identity supplies
    the current equation; only equal-degree bookkeeping remains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianCompactCurrents
  CurrentDegreeTransport CurrentDegreeTransportComposition CurrentCompactPushforwardAlgebra
  CurrentJoinDomain CurrentJoinSourceChain CurrentJoinSourceCompact CurrentJoinBoundaryDegree
  CurrentJoinReverseMapSealed CurrentJoinReverseMapLaws CurrentJoinReverseMapClass
  CurrentJoinReverseRawCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_join_swap_degree]: the original two
    join degrees coincide after exchanging i and j, supporting
    the anticommutativity formula of Federer 4.1.11, p. 365.
    Reuse the preceding successor-degree identifications. *)
Lemma current_join_swap_degree i j:(i+1+j)%N=(j+1+i)%N.
Proof.
exact:(eq_trans (current_join_degree_successor i j)
  (eq_trans (congr1 (fun k:nat=>k.+1) (addnC i j))
    (esym (current_join_degree_successor j i)))).
Qed.

(** Source for [current_join_raw_swap_degree]: identify the
    two original raw triple product degrees, supporting the
    reversing calculation of Federer 4.1.11, p. 365. *)
Lemma current_join_raw_swap_degree i j:(i+(1+j))%N=(j+(1+i))%N.
Proof. by rewrite !add1n !addnS addnC. Qed.

Section CurrentJoinReverseSourceCurrent.
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

Local Notation Raw := (@CartesianCurrentProduct.value R h2 n (1+n)%N i (1+j)%N
  Full TimeSpace hFull hTimeSpace S Inner).
Local Notation hRaw := (@current_cartesian_compact_currents R h2 n (1+n)%N i (1+j)%N
  Full TimeSpace hFull hTimeSpace S Inner hS
  (@current_cartesian_compact_currents R h2 1%N n 1%N j Time Full hTime hFull
    Segment T (@current_join_time_segment_compact R h2) hT)).
Local Notation hChain := (@current_join_source_compact R h2 n i j S T hS hT).
Local Notation p := (@CurrentJoinReverseMap.value R n).
Local Notation Image := (@current_join_reverse_domain_image R n).
Local Notation Smooth := (@current_join_reverse_open_smooth R n Domain hDomain).
Local Notation RawPush := (@current_compact_map_pushforward R h2 (n+(1+n))%N (n+(1+n))%N
  Domain Domain hDomain hDomain p Image Smooth (i+(1+j))%N Raw hRaw).
Local Notation ChainPush := (@current_compact_map_pushforward R h2 (n+(1+n))%N (n+(1+n))%N
  Domain Domain hDomain hDomain p Image Smooth (i+1+j)%N Chain hChain).
Local Notation RawTarget := (@CartesianCurrentProduct.value R h2 n (1+n)%N j (1+i)%N
  Full TimeSpace hFull hTimeSpace T (@CartesianCurrentProduct.value R h2 1%N n 1%N i
    Time Full hTime hFull Segment S)).
Local Notation ChainTarget := (@current_join_source_chain R h2 n j i T S).
Local Notation Tr := (fun a b (e:a=b)=>@current_degree_transport R h2 (n+(1+n))%N
  Domain hDomain a b e).
Local Notation eRaw := (current_join_raw_swap_degree i j).
Local Notation eSwap := (current_join_swap_degree i j).
Local Notation signJoin := ((-1:R)^+((i+1)*(j+1))).

(** Source for [current_join_reverse_source_current]: the
    original p image of S times [0,1] times T is the signed
    reversed chain, supporting Federer 4.1.11, p. 365. This
    writes the equivalent reversing identity in the forward
    p-image direction, retaining every original compact current. *)
Theorem current_join_reverse_source_current:
  Tr _ _ eSwap ChainPush=signJoin*:ChainTarget.
Proof.
have hSame (f g:(i+(1+j))%N=(j+(1+i))%N):
    Tr _ _ f RawPush=Tr _ _ g RawPush.
  have ->:f=g:=Prop_irrelevance _ _;reflexivity.
have hRawIdentity:Tr _ _ eRaw RawPush=signJoin*:RawTarget.
  exact:(eq_trans (hSame eRaw _) (@current_join_reverse_raw_current R h2 n i j S T hS hT)).
have hNormal:=congr1 (Tr _ _ (addnA j 1%N i)) hRawIdentity.
rewrite current_degree_transport_composition (linZ (hom_linear (Tr _ _ (addnA j 1%N i)))) in hNormal.
have hDegree:=@current_compact_map_pushforward_degree R h2 (n+(1+n))%N (n+(1+n))%N
  Domain Domain hDomain hDomain p Image Smooth (i+(1+j))%N (i+1+j)%N
  (addnA i 1%N j) Raw hRaw hChain.
have hLeft:=congr1 (Tr _ _ eSwap) (esym hDegree).
have hProof:eq_trans (addnA i 1%N j) eSwap=eq_trans eRaw (addnA j 1%N i):=
  Prop_irrelevance _ _.
rewrite current_degree_transport_composition hProof in hLeft.
exact:(eq_trans hLeft hNormal).
Qed.

(** Source for [current_join_reverse_source_printed]: T times
    [0,1] times S equals (-1)^((i+1)(j+1)) p#(S times [0,1]
    times T), the original reversing pushforward of Federer
    4.1.11, p. 365. The graded sign is its own inverse. *)
Theorem current_join_reverse_source_printed:
  ChainTarget=signJoin*:Tr _ _ eSwap ChainPush.
Proof.
have h:=congr1 (fun U:@current_space R h2 (n+(1+n))%N Domain hDomain (j+1+i)%N=>
  signJoin*:U) current_join_reverse_source_current.
rewrite scalerA -exprMn mulrNN mul1r expr1n scale1r in h.
exact:esym h.
Qed.
End CurrentJoinReverseSourceCurrent.
