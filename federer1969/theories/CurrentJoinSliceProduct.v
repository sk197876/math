(** Federer (1969), 4.1.11, p. 365, opening paragraph:
    S times delta_t times T equals G_t#(S times T).
    Reuse the proved product pushforward, original point product
    and compact identity pushforward. All currents are arbitrary
    under the original compact-support hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianCompactCurrents CurrentCartesianPointInclusion
  CurrentCartesianPointInclusionProper CurrentCartesianPointProduct
  CurrentCartesianMapClass CurrentCartesianMapPullback
  CurrentCartesianProductPushforward CurrentDirac CurrentProperSupport
  CurrentCompactMapProper CurrentPushforwardUP CurrentPushforwardSealed
  CurrentPushforwardMapAgreement CurrentPushforwardNormality
  CurrentElementaryPushforwards CurrentJoinDomain
  CurrentJoinSliceMapSealed CurrentJoinSliceMapClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentJoinSliceProduct.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n i j : nat.
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
Variable S : @current_space R h2 n Full hFull i.
Variable T : @current_space R h2 n Full hFull j.
Hypothesis hS : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull i S).
Hypothesis hT : @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull j T).
Variable t : R.
Local Notation Product :=
  (@CartesianCurrentProduct.value R h2 n n i j Full Full hFull hFull S T).
Local Notation hProductCompact :=
  (@current_cartesian_compact_currents R h2 n n i j
    Full Full hFull hFull S T hS hT).
Local Notation G := (@CurrentJoinSliceMap.value R n t).
Local Notation GImage := (fun z hz =>
  @current_join_slice_map_domain_image R n t z hz).
Local Notation GClass := (@current_join_slice_map_open_smooth R n t).
Local Notation GProper := (@current_compact_map_proper R h2
  (n+n)%N (n+(1+n))%N (i+j)%N AB Domain hAB Product G GImage
  (norm_class_continuous (GClass 0%N)) hProductCompact).

(** Source for [current_join_slice_current]: the original
    G_t#(S times T), Federer 4.1.11, p. 365. This alias uses
    only the already opaque product and proper pushforward. *)
Definition current_join_slice_current :
    @current_space R h2 (n+(1+n))%N Domain hDomain (i+j)%N :=
  @CurrentPushforward.value R h2 (n+n)%N (n+(1+n))%N (i+j)%N
    AB Domain hAB hDomain Product G GImage GClass GProper.

(** Source for [current_join_slice_current_laws]: the original
    insertion pushforward has every actual compact-replacement
    action, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_slice_current_laws :
  @is_current_pushforward R h2 (n+n)%N (n+(1+n))%N (i+j)%N
    AB Domain hAB hDomain Product G GImage GClass current_join_slice_current.
Proof. exact: CurrentPushforward.laws. Qed.

(** Source for [current_join_slice_current_compact]: the
    original insertion image is compactly supported, supporting
    the join boundary calculation in Federer 4.1.11, p. 365. *)
Lemma current_join_slice_current_compact :
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(1+n))%N)))
    (@current_support R h2 (n+(1+n))%N Domain hDomain
      (i+j)%N current_join_slice_current).
Proof.
exact: (@current_pushforward_compact_support R h2 (n+n)%N (n+(1+n))%N
  AB Domain hAB hDomain G GImage GClass (i+j)%N
  Product GProper hProductCompact).
Qed.

Local Notation idMap := (fun x : X => x).
Local Notation insert :=
  (@current_cartesian_point_inclusion R 1%N n (@euclidean_one_embed R t)).
Local Notation IdImage := (fun (x : X) (_ : True) => Logic.I).
Local Notation InsertImage :=
  (fun (x : X) (_ : True) => conj Logic.I Logic.I).
Local Notation IdGlobal := (@current_join_slice_identity_smooth R n).
Local Notation InsertGlobal :=
  (@current_cartesian_point_inclusion_smooth R 1%N n Full hFull
    (@euclidean_one_embed R t)).
Local Notation IdClass :=
  (@current_cartesian_factor_open_class R n n Full hFull idMap IdGlobal).
Local Notation InsertClass :=
  (@current_cartesian_factor_open_class R n (1+n)%N Full hFull insert InsertGlobal).
Local Notation IdProper := (@current_compact_map_proper R h2 n n i
  Full Full hFull S idMap IdImage (norm_class_continuous (IdClass 0%N)) hS).
Local Notation InsertProper := (@current_compact_map_proper R h2 n (1+n)%N j
  Full TimeSpace hFull T insert InsertImage
  (norm_class_continuous (InsertClass 0%N)) hT).
Local Notation IdPush :=
  (@CurrentPushforward.value R h2 n n i Full Full hFull hFull
    S idMap IdImage IdClass IdProper).
Local Notation InsertPush :=
  (@CurrentPushforward.value R h2 n (1+n)%N j Full TimeSpace hFull hTimeSpace
    T insert InsertImage InsertClass InsertProper).
Local Notation ProductMap :=
  (@euclidean_cartesian_map R n n n (1+n)%N idMap insert).
Local Notation ProductImage := (fun (z : Source) (hz : AB z) =>
  @current_cartesian_map_domain_image R n n n (1+n)%N
    Full Full Full TimeSpace idMap insert IdImage InsertImage z hz).
Local Notation ProductClass :=
  (@current_cartesian_map_on_open_product_smooth R n n n (1+n)%N
    idMap insert IdGlobal InsertGlobal Full Full hFull hFull).
Local Notation ProductProper := (@current_compact_map_proper R h2
  (n+n)%N (n+(1+n))%N (i+j)%N AB Domain hAB Product
  ProductMap ProductImage (norm_class_continuous (ProductClass 0%N))
  hProductCompact).
Local Notation OldInsertImage := (fun y hy =>
  @current_cartesian_point_inclusion_image R 1%N n Time Full
    (@euclidean_one_embed R t) Logic.I y hy).
Local Notation OldInsertProper :=
  (@current_cartesian_point_inclusion_proper R h2 1%N n j
    Time Full hTime hFull (@euclidean_one_embed R t) Logic.I T).
Local Notation delta :=
  (@dirac_current R h2 1%N Time hTime (@euclidean_one_embed R t)).
Local Notation Inner :=
  (@CartesianCurrentProduct.value R h2 1%N n 0%N j
    Time Full hTime hFull delta T).

(** Source for [current_join_slice_product]: the original
    S times delta_t times T equals G_t#(S times T), Federer
    4.1.11, p. 365, opening sentence. The proof reuses the original
    identity image, point product and complete product-map theorem. *)
Theorem current_join_slice_product :
  @CartesianCurrentProduct.value R h2 n (1+n)%N i j
    Full TimeSpace hFull hTimeSpace S Inner = current_join_slice_current.
Proof.
have hIdentity : IdPush=S := @current_compact_identity_pushforward R h2
  n Full hFull i S hS IdImage IdClass IdProper.
have hInsertComparison := @current_pushforward_map_agreement R h2 n (1+n)%N j
  Full TimeSpace hFull hTimeSpace insert insert InsertImage OldInsertImage
  InsertClass InsertGlobal T InsertProper OldInsertProper (fun _ _ => erefl).
have hInsert : InsertPush=Inner := eq_trans hInsertComparison
  (esym (@current_cartesian_point_product R h2 1%N n j
    Time Full hTime hFull (@euclidean_one_embed R t) Logic.I T)).
have hNatural := @current_cartesian_product_pushforward R h2 n n n (1+n)%N
  Full Full Full TimeSpace hFull hFull hFull hTimeSpace
  idMap insert IdGlobal InsertGlobal IdImage InsertImage i j S T hS hT.
rewrite hIdentity hInsert in hNatural.
have hMapComparison := @current_pushforward_map_agreement R h2
  (n+n)%N (n+(1+n))%N (i+j)%N AB Domain hAB hDomain
  G ProductMap GImage ProductImage GClass ProductClass
  Product GProper ProductProper
  (fun z _ => congr1 (fun H : Source -> Target => H z)
    (@current_join_slice_map_as_product R n t)).
exact: esym (eq_trans hMapComparison hNatural).
Qed.
End CurrentJoinSliceProduct.
