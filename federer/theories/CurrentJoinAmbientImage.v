(** Federer (1969), 4.1.11, pp. 364, 366:
    express the original join as F# of its original
    ordered product on the whole Euclidean source.
    This is domain and degree equality bookkeeping,
    using the preceding exact raw-image theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed CurrentDegreeTransport
  CurrentDomainTransport CurrentDomainTransportIdentity CurrentCompactMapDomainTransport
  CurrentCompactPushforwardAlgebra CurrentJoinDomain CurrentJoinMapSealed CurrentJoinMapClass
  CurrentJoinSealed CurrentJoinRawMass CurrentJoinAmbientSource.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAmbientImage.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation d := ((n+(1+n))%N).
Local Notation Full := (fun k:nat=>fun _:R_n R k=>True).
Local Notation hFull := (fun (k:nat) (x:R_n R k) (_:True)=>
  @norm_full_domain_interior R (R_n R k) (inner_norm (@euclidean_inner_productP R k)) x).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n (Full 1%N) (Full n)).
Local Notation hTimeSpace := (@current_cartesian_domain_open R 1%N n
  (Full 1%N) (Full n) (hFull 1%N) (hFull n)).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Variables (S:@current_space R h2 n (Full n) (hFull n) i)
  (T:@current_space R h2 n (Full n) (hFull n) j).
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) i S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j T).
Local Notation I := (@current_join_time_segment R h2).
Local Notation Inner := (@CartesianCurrentProduct.value R h2 1%N n 1%N j
  (Full 1%N) (Full n) (hFull 1%N) (hFull n) I T).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 n (1+n)%N i (1+j)%N
  (Full n) TimeSpace (hFull n) hTimeSpace S Inner).
Local Notation hRaw := (@current_join_raw_compact R h2 n i j S T hS hT).
Local Notation Source := (@current_join_ambient_source R h2 n i j S T).
Local Notation hSource := (@current_join_ambient_source_compact R h2 n i j S T hS hT).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation OldImage := (@current_join_map_image R n).
Local Notation Image := (fun (x:R_n R d) (_:True)=>Logic.I).
Local Notation OldClass := (@current_join_map_smooth R n Domain hDomain).
Local Notation FullClass := (@current_join_map_smooth R n (Full d) (hFull d)).
Local Notation TrSource := (@current_domain_transport R h2 d Domain hDomain (Full d)
  (@current_join_domain_full R n) (hFull d) (i+(1+j))%N Raw).

(** Source for [current_join_ambient_image]: the original
    join is exactly the image of S times [0,1]
    times T under F on its equal full Euclidean
    presentation, supporting the associativity calculation
    in Federer 4.1.11, p. 366. Both current factors
    remain arbitrary and compact. *)
Lemma current_join_ambient_image:
  @CurrentJoin.value R h2 n i j S T hS hT=
  @current_degree_transport R h2 n (Full n) (hFull n)
    (i+(1+j))%N (i+1+j)%N (addnA i 1%N j)
    (@current_compact_map_pushforward R h2 d n (Full d) (Full n) (hFull d) (hFull n)
      F Image FullClass (i+(1+j))%N Source hSource).
Proof.
have hTrSource:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (@current_support R h2 d (Full d) (hFull d) (i+(1+j))%N TrSource).
  rewrite current_domain_transport_support;exact:hRaw.
have hTransfer:=@current_compact_map_domain_transport R h2 d n
  Domain (Full d) (Full n) (Full n) hDomain (hFull d) (hFull n) (hFull n)
  (@current_join_domain_full R n) (erefl (Full n)) F OldImage Image OldClass FullClass
  (i+(1+j))%N Raw hRaw hTrSource.
rewrite current_domain_transport_identity in hTransfer.
have hReplace:=@current_compact_map_pushforward_congruence R h2 d n
  (Full d) (Full n) (hFull d) (hFull n) F Image FullClass (i+(1+j))%N
  TrSource Source hTrSource hSource (@current_join_raw_ambient R h2 n i j S T).
have hOld:=@current_join_raw_image R h2 n i j S T hS hT.
change (@CurrentJoin.value R h2 n i j S T hS hT=
  @current_degree_transport R h2 n (Full n) (hFull n) (i+(1+j))%N (i+1+j)%N
    (addnA i 1%N j) (@current_compact_map_pushforward R h2 d n Domain (Full n) hDomain (hFull n)
      F OldImage OldClass (i+(1+j))%N Raw hRaw)) in hOld.
rewrite -hTransfer hReplace in hOld.
exact:hOld.
Qed.
End CurrentJoinAmbientImage.
