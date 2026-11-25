(** Federer (1969), 4.1.11, p. 365, opening paragraph:
    F composed with G_0 and G_1 gives the two standard
    projections. Evaluate their actual pushforwards using the
    preceding compact-cutoff projection results. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianCompactCurrents CurrentProperSupport
  CurrentCompactMapProper CurrentPushforwardSealed CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentCartesianProjections
  CurrentCartesianProjectionProper CurrentCartesianSecondProjection
  CurrentCartesianFirstProjection CurrentJoinDomain
  CurrentJoinSliceMapClass CurrentJoinSlicePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinEndpointProjections.
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
Local Notation Product :=
  (@CartesianCurrentProduct.value R h2 n n i j Full Full hFull hFull S T).
Local Notation ProductCompact := (@current_cartesian_compact_currents R h2 n n i j
  Full Full hFull hFull S T hS hT).
Local Notation ATr := (fun a b (e:a=b)=>@current_degree_transport R h2 n Full hFull a b e).
Local Notation p := (@euclidean_first_block_map R n n).
Local Notation q := (@euclidean_last_block_map R n n).
Local Notation PImage := (fun z (hz:AB z)=>hz.1).
Local Notation QImage := (fun z (hz:AB z)=>hz.2).
Local Notation PClass := (@current_cartesian_first_projection_smooth R n n Full Full hFull hFull).
Local Notation QClass := (@current_cartesian_last_projection_smooth R n n Full Full hFull hFull).
Local Notation PProper := (@current_compact_map_proper R h2 (n+n)%N n (i+j)%N
  AB Full hAB Product p PImage (norm_class_continuous (PClass 0%N)) ProductCompact).
Local Notation QProper := (@current_cartesian_projection_proper_on_support R h2 n n i j
  Full Full hFull hFull S T hS).
Local Notation SlicePush := (fun t=>@current_join_slice_pushforward R h2 n i j S T hS hT t).

(** Source for [current_join_start_projection_pushforward]:
    the original F#(G_0#(S times T)) is the first projection
    of S times T. This is the first endpoint used in all four
    boundary formulas of Federer 4.1.11, p. 365. *)
Theorem current_join_start_projection_pushforward k (e:(i+j)%N=k):
  ATr _ _ e (SlicePush 0)=
  @current_cartesian_compact_first_projection R h2 n n Full Full hFull hFull
    i j S T hS hT k e.
Proof.
rewrite /current_cartesian_compact_first_projection.
apply:congr1.
exact:(@current_join_slice_pushforward_map R h2 n i j S T hS hT 0
  p PImage PClass PProper (fun z _=>@current_join_start_projection R n z)).
Qed.

(** Source for [current_join_end_projection_pushforward]:
    the original F#(G_1#(S times T)) is the second projection
    of S times T, as used for the second endpoint in Federer
    4.1.11, p. 365. Reuse the original proper projection. *)
Theorem current_join_end_projection_pushforward:
  SlicePush 1=@current_cartesian_second_projection R h2 n n Full Full hFull hFull
    i j S T hS.
Proof.
exact:(@current_join_slice_pushforward_map R h2 n i j S T hS hT 1
  q QImage QClass QProper (fun z _=>@current_join_end_projection R n z)).
Qed.

(** Source for [current_join_start_positive]: the first
    endpoint contribution vanishes for j>0, supporting the first
    and third boundary cases in Federer 4.1.11, p. 365. *)
Theorem current_join_start_positive:(0<j)%N->SlicePush 0=0.
Proof.
move=>hj.
have hStart:=current_join_start_projection_pushforward (erefl (i+j)%N).
rewrite current_degree_transport_identity
  (@current_cartesian_first_projection_positive R h2 n n Full Full hFull hFull
    i j S T hS hT hj) in hStart.
exact:hStart.
Qed.

(** Source for [current_join_end_positive]: the second
    endpoint contribution vanishes for i>0, supporting the first
    and second boundary cases in Federer 4.1.11, p. 365. *)
Theorem current_join_end_positive:(0<i)%N->SlicePush 1=0.
Proof.
move=>hi.
exact:(eq_trans current_join_end_projection_pushforward
  (@current_cartesian_projection_positive R h2 n n Full Full hFull hFull
    i j S T hS hi)).
Qed.
End CurrentJoinEndpointProjections.
