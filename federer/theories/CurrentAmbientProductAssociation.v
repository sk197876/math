(** Federer (1969), 4.1.11, p. 366: retain
    the preceding Cartesian associativity law on equal
    whole-space domains. Both dimension and current-degree
    identifications are the original natural equalities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  EuclideanDimensionCastLinear CurrentSpaces CurrentCartesianDomain CurrentCartesianReassociationDomain
  CurrentCartesianProductSealed CurrentCartesianCompactCurrents CurrentCartesianCompactIdentities
  CurrentCompactPushforwardAlgebra CurrentCompactMapDomainTransport CurrentDomainTransport
  CurrentDomainTransportIdentity CurrentDomainTransportDegree CurrentDegreeTransport
  CurrentAmbientCartesianProduct CurrentAmbientProductDomainTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentAmbientProductAssociation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n v:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation AB := (@euclidean_cartesian_set R m n (Full m) (Full n)).
Local Notation BC := (@euclidean_cartesian_set R n v (Full n) (Full v)).
Local Notation hAB := (@current_cartesian_domain_open R m n (Full m) (Full n) (hFull m) (hFull n)).
Local Notation hBC := (@current_cartesian_domain_open R n v (Full n) (Full v) (hFull n) (hFull v)).
Local Notation Left := (@euclidean_cartesian_set R (m+n)%N v AB (Full v)).
Local Notation Right := (@euclidean_cartesian_set R m (n+v)%N (Full m) BC).
Local Notation hLeft := (@current_cartesian_domain_open R (m+n)%N v AB (Full v) hAB (hFull v)).
Local Notation hRight := (@current_cartesian_domain_open R m (n+v)%N (Full m) BC (hFull m) hBC).

(** Source for [current_cartesian_left_full]: the original
    left-associated three full factors have the whole
    domain, supporting Federer 4.1.11, p. 366. *)
Lemma current_cartesian_left_full:Left=Full ((m+n)+v)%N.
Proof.
apply:funext=>z;apply:propext;split=>_;first exact:Logic.I.
exact:(conj (conj Logic.I Logic.I) Logic.I).
Qed.

(** Source for [current_cartesian_right_full]: the original
    right-associated three full factors have the same
    whole domain, supporting Federer 4.1.11, p. 366. *)
Lemma current_cartesian_right_full:Right=Full (m+(n+v))%N.
Proof.
apply:funext=>z;apply:propext;split=>_;first exact:Logic.I.
exact:(conj Logic.I (conj Logic.I Logic.I)).
Qed.

Variables i j k:nat.
Variables (S:@current_space R h2 m (Full m) (hFull m) i)
  (T:@current_space R h2 n (Full n) (hFull n) j)
  (U:@current_space R h2 v (Full v) (hFull v) k).
Local Notation PairLeft := (@CartesianCurrentProduct.value R h2 m n i j
  (Full m) (Full n) (hFull m) (hFull n) S T).
Local Notation PairRight := (@CartesianCurrentProduct.value R h2 n v j k
  (Full n) (Full v) (hFull n) (hFull v) T U).
Local Notation RawLeft := (@CartesianCurrentProduct.value R h2 (m+n)%N v (i+j)%N k
  AB (Full v) hAB (hFull v) PairLeft U).
Local Notation RawRight := (@CartesianCurrentProduct.value R h2 m (n+v)%N i (j+k)%N
  (Full m) BC (hFull m) hBC S PairRight).
Local Notation AmbientLeft := (@current_ambient_cartesian_product R h2 (m+n)%N v (i+j)%N k
  (@current_ambient_cartesian_product R h2 m n i j S T) U).
Local Notation AmbientRight := (@current_ambient_cartesian_product R h2 m (n+v)%N i (j+k)%N
  S (@current_ambient_cartesian_product R h2 n v j k T U)).
Local Notation TrLeft := (fun d=>@current_domain_transport R h2 ((m+n)+v)%N Left hLeft
  (Full ((m+n)+v)%N) current_cartesian_left_full (hFull ((m+n)+v)%N) d).
Local Notation TrRight := (fun d=>@current_domain_transport R h2 (m+(n+v))%N Right hRight
  (Full (m+(n+v))%N) current_cartesian_right_full (hFull (m+(n+v))%N) d).

(** Source for [current_ambient_product_left_source]: equal-domain
    transport gives the actual left-associated full-space
    product, supporting Federer 4.1.11, p. 366. *)
Lemma current_ambient_product_left_source:TrLeft ((i+j)+k)%N RawLeft=AmbientLeft.
Proof.
rewrite (@current_ambient_product_domain_transport R h2 (m+n)%N v AB (Full v) hAB (hFull v)
  (@current_cartesian_full_domain R m n) (erefl (Full v)) current_cartesian_left_full (i+j)%N k).
rewrite (@current_ambient_product_domain_transport R h2 m n (Full m) (Full n) (hFull m) (hFull n)
  (erefl (Full m)) (erefl (Full n)) (@current_cartesian_full_domain R m n) i j).
by rewrite !current_domain_transport_identity.
Qed.

(** Source for [current_ambient_product_right_source]: equal-domain
    transport gives the actual right-associated full-space
    product, supporting Federer 4.1.11, p. 366. *)
Lemma current_ambient_product_right_source:TrRight (i+(j+k))%N RawRight=AmbientRight.
Proof.
rewrite (@current_ambient_product_domain_transport R h2 m (n+v)%N (Full m) BC (hFull m) hBC
  (erefl (Full m)) (@current_cartesian_full_domain R n v) current_cartesian_right_full i (j+k)%N).
rewrite (@current_ambient_product_domain_transport R h2 n v (Full n) (Full v) (hFull n) (hFull v)
  (erefl (Full n)) (erefl (Full v)) (@current_cartesian_full_domain R n v) j k).
by rewrite !current_domain_transport_identity.
Qed.

Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) i S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j T).
Hypothesis hU:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R v)))
  (@current_support R h2 v (Full v) (hFull v) k U).
Local Notation hPairLeft := (@current_cartesian_compact_currents R h2 m n i j
  (Full m) (Full n) (hFull m) (hFull n) S T hS hT).
Local Notation hRawLeft := (@current_cartesian_compact_currents R h2 (m+n)%N v (i+j)%N k
  AB (Full v) hAB (hFull v) PairLeft U hPairLeft hU).
Local Notation hAmbientPair := (@current_ambient_cartesian_product_compact R h2 m n i j S T hS hT).
Local Notation hAmbientLeft := (@current_ambient_cartesian_product_compact R h2 (m+n)%N v (i+j)%N k
  (@current_ambient_cartesian_product R h2 m n i j S T) U hAmbientPair hU).
Local Notation A := (@euclidean_dimension_cast_map R ((m+n)+v)%N (m+(n+v))%N (esym (addnA m n v))).
Local Notation OldImage := (fun z hz=>@current_cartesian_reassociation_image R m n v
  (Full m) (Full n) (Full v) z hz).
Local Notation Image := (fun (z:R_n R ((m+n)+v)%N) (_:True)=>Logic.I).
Local Notation OldClass := (@euclidean_dimension_cast_smooth R ((m+n)+v)%N (m+(n+v))%N
  (esym (addnA m n v)) Left hLeft).
Local Notation AClass := (@euclidean_dimension_cast_smooth R ((m+n)+v)%N (m+(n+v))%N
  (esym (addnA m n v)) (Full ((m+n)+v)%N) (hFull ((m+n)+v)%N)).

(** Source for [current_ambient_product_association]: the
    original associativity image holds on equal whole-space
    domains, supporting Federer 4.1.11, p. 366. All
    degrees and Euclidean dimensions retain the preceding
    general Cartesian associativity theorem. *)
Lemma current_ambient_product_association:
  @current_degree_transport R h2 (m+(n+v))%N (Full (m+(n+v))%N) (hFull (m+(n+v))%N)
    ((i+j)+k)%N (i+(j+k))%N (esym (addnA i j k))
    (@current_compact_map_pushforward R h2 ((m+n)+v)%N (m+(n+v))%N
      (Full ((m+n)+v)%N) (Full (m+(n+v))%N) (hFull ((m+n)+v)%N) (hFull (m+(n+v))%N)
      A Image AClass ((i+j)+k)%N AmbientLeft hAmbientLeft)=AmbientRight.
Proof.
have hTrCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R ((m+n)+v)%N)))
    (@current_support R h2 ((m+n)+v)%N (Full ((m+n)+v)%N) (hFull ((m+n)+v)%N)
      ((i+j)+k)%N (TrLeft ((i+j)+k)%N RawLeft)).
  rewrite current_domain_transport_support;exact:hRawLeft.
have hOld:=@current_cartesian_compact_association R h2 m n v
  (Full m) (Full n) (Full v) (hFull m) (hFull n) (hFull v)
  i j k S T U hRawLeft OldImage OldClass.
have hDomains:=@current_compact_map_domain_transport R h2 ((m+n)+v)%N (m+(n+v))%N
  Left (Full ((m+n)+v)%N) Right (Full (m+(n+v))%N) hLeft (hFull ((m+n)+v)%N)
  hRight (hFull (m+(n+v))%N) current_cartesian_left_full current_cartesian_right_full
  A OldImage Image OldClass AClass ((i+j)+k)%N RawLeft hRawLeft hTrCompact.
have hReplace:=@current_compact_map_pushforward_congruence R h2 ((m+n)+v)%N (m+(n+v))%N
  (Full ((m+n)+v)%N) (Full (m+(n+v))%N) (hFull ((m+n)+v)%N) (hFull (m+(n+v))%N)
  A Image AClass ((i+j)+k)%N (TrLeft ((i+j)+k)%N RawLeft) AmbientLeft hTrCompact hAmbientLeft
  current_ambient_product_left_source.
have hTransport:=congr1 (TrRight (i+(j+k))%N) hOld.
rewrite current_domain_transport_degree -hDomains hReplace current_ambient_product_right_source in hTransport.
exact:hTransport.
Qed.
End CurrentAmbientProductAssociation.
