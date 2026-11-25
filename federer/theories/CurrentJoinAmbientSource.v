(** Federer (1969), 4.1.11, pp. 364, 366:
    the original S times [0,1] times T source on
    its equal whole-space Euclidean presentation. Keep
    the original opaque Cartesian products. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianCompactCurrents
  CurrentDomainTransport CurrentDomainTransportIdentity CurrentAmbientCartesianProduct
  CurrentAmbientProductDomainTransport CurrentJoinDomain CurrentJoinSourceCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_join_domain_full]: the original
    R^n times R times R^n source is the full
    Euclidean space under its original block identification,
    supporting Federer 4.1.11, pp. 364, 366. *)
Lemma current_join_domain_full (R:realType) n:
  @current_join_domain R n=(fun _:R_n R (n+(1+n))%N=>True).
Proof.
apply:funext=>z;apply:propext;split=>_;first exact:Logic.I.
exact:(conj Logic.I (conj Logic.I Logic.I)).
Qed.

Section CurrentJoinAmbientSource.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n (Full 1%N) (Full n)).
Local Notation hTimeSpace := (@current_cartesian_domain_open R 1%N n
  (Full 1%N) (Full n) (hFull 1%N) (hFull n)).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Variable S:@current_space R h2 n (Full n) (hFull n) i.
Variable T:@current_space R h2 n (Full n) (hFull n) j.
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_segment_compact R h2).
Local Notation Inner := (@CartesianCurrentProduct.value R h2 1%N n 1%N j
  (Full 1%N) (Full n) (hFull 1%N) (hFull n) I T).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 n (1+n)%N i (1+j)%N
  (Full n) TimeSpace (hFull n) hTimeSpace S Inner).

(** Source for [current_join_ambient_source]: the actual
    original ordered source product, supporting the
    associativity calculation in Federer 4.1.11, p. 366.
    This alias constructs no new Cartesian product. *)
Definition current_join_ambient_source:
    @current_space R h2 (n+(1+n))%N (Full (n+(1+n))%N) (hFull (n+(1+n))%N) (i+(1+j))%N:=
  @current_ambient_cartesian_product R h2 n (1+n)%N i (1+j)%N S
    (@current_ambient_cartesian_product R h2 1%N n 1%N j I T).

(** Source for [current_join_raw_ambient]: the original
    source equals its full-space presentation after domain
    equality alone, supporting Federer 4.1.11, p. 366. *)
Lemma current_join_raw_ambient:
  @current_domain_transport R h2 (n+(1+n))%N Domain hDomain (Full (n+(1+n))%N)
    (@current_join_domain_full R n) (hFull (n+(1+n))%N) (i+(1+j))%N Raw=
    current_join_ambient_source.
Proof.
rewrite (@current_ambient_product_domain_transport R h2 n (1+n)%N
  (Full n) TimeSpace (hFull n) hTimeSpace (erefl (Full n))
  (@current_cartesian_full_domain R 1%N n) (@current_join_domain_full R n) i (1+j)%N).
rewrite (@current_ambient_product_domain_transport R h2 1%N n
  (Full 1%N) (Full n) (hFull 1%N) (hFull n) (erefl (Full 1%N))
  (erefl (Full n)) (@current_cartesian_full_domain R 1%N n) 1%N j).
by rewrite !current_domain_transport_identity.
Qed.

(** Source for [current_join_ambient_source_compact]: compact
    original factors give a compact ordered source,
    supporting Federer 4.1.11, p. 366. Arbitrary
    compact currents retain their original degrees. *)
Lemma current_join_ambient_source_compact:
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n (Full n) (hFull n) i S)->
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n (Full n) (hFull n) j T)->
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)))
    (@current_support R h2 (n+(1+n))%N (Full (n+(1+n))%N) (hFull (n+(1+n))%N)
      (i+(1+j))%N current_join_ambient_source).
Proof.
move=>hS hT.
apply:(@current_ambient_cartesian_product_compact R h2 n (1+n)%N i (1+j)%N
  S (@current_ambient_cartesian_product R h2 1%N n 1%N j I T) hS).
exact:(@current_ambient_cartesian_product_compact R h2 1%N n 1%N j I T hI hT).
Qed.
End CurrentJoinAmbientSource.
