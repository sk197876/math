(** Federer (1969), 4.1.11, pp. 365–366:
    the original point join is the original cone image
    of the time-space product on its equal whole-space
    presentation. Reuse the preceding point-cone theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentDirac CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianCompactCurrents
  CurrentCompactElementaryPushforwards CurrentCompactPushforwardAlgebra CurrentDomainTransport
  CurrentDomainTransportIdentity CurrentCompactMapDomainTransport CurrentAmbientCartesianProduct
  CurrentConeHomotopySealed CurrentConeHomotopyClass CurrentJoinDomain CurrentJoinSourceCompact
  CurrentJoinSealed CurrentJoinPointCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinPointAmbientCone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variable u:R_n R n.
Local Notation H := (@CurrentConeHomotopy.value R n u).
Local Notation Domain := (@euclidean_cartesian_set R 1%N n (Full 1%N) (Full n)).
Local Notation hDomain := (@current_cartesian_domain_open R 1%N n
  (Full 1%N) (Full n) (hFull 1%N) (hFull n)).

(** Source for [current_cone_homotopy_full_smooth]: the
    original contraction is smooth on the whole product
    Euclidean space, supporting the triangle maps in
    Federer 4.1.11, p. 366, by 4.1.10, p. 364. *)
Lemma current_cone_homotopy_full_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (Full (1+n)%N) H.
Proof.
have h:=@current_cone_homotopy_smooth R n u (Full n) (hFull n).
change (norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) Domain H) in h.
by rewrite current_cartesian_full_domain in h.
Qed.

Variable T:@current_space R h2 n (Full n) (hFull n) j.
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j T).
Local Notation Point := (@dirac_current R h2 n (Full n) (hFull n) u).
Local Notation hPoint := (@current_compact_dirac_support R h2 n (Full n) (hFull n) u Logic.I).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_segment_compact R h2).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 1%N n 1%N j
  (Full 1%N) (Full n) (hFull 1%N) (hFull n) I T).
Local Notation hRaw := (@current_cartesian_compact_currents R h2 1%N n 1%N j
  (Full 1%N) (Full n) (hFull 1%N) (hFull n) I T hI hT).
Local Notation Product := (@current_ambient_cartesian_product R h2 1%N n 1%N j I T).
Local Notation hProduct := (@current_ambient_cartesian_product_compact R h2 1%N n 1%N j I T hI hT).
Local Notation OldImage := (fun (x:R_n R (1+n)%N) (_:Domain x)=>Logic.I).
Local Notation Image := (fun (x:R_n R (1+n)%N) (_:True)=>Logic.I).
Local Notation OldClass := (@current_cone_homotopy_smooth R n u (Full n) (hFull n)).

(** Source for [current_join_point_ambient_cone]: delta_u
    join T is h#([0,1] times T), with the original
    whole Euclidean product presentation, supporting
    the triangle argument of Federer 4.1.11, p. 366.
    T is any compact current; no integral representation
    or finite-mass condition is imposed. *)
Lemma current_join_point_ambient_cone:
  @CurrentJoin.value R h2 n 0%N j Point T hPoint hT=
  @current_compact_map_pushforward R h2 (1+n)%N n (Full (1+n)%N) (Full n)
    (hFull (1+n)%N) (hFull n) H Image current_cone_homotopy_full_smooth (1+j)%N Product hProduct.
Proof.
have hOld:=@current_join_point_is_cone R h2 n j u T hT.
have hDomains:=@current_compact_map_domain_transport R h2 (1+n)%N n
  Domain (Full (1+n)%N) (Full n) (Full n) hDomain (hFull (1+n)%N) (hFull n) (hFull n)
  (@current_cartesian_full_domain R 1%N n) (erefl (Full n)) H OldImage Image
  OldClass current_cone_homotopy_full_smooth (1+j)%N Raw hRaw hProduct.
rewrite current_domain_transport_identity in hDomains.
exact:(eq_trans hOld (esym hDomains)).
Qed.
End CurrentJoinPointAmbientCone.
