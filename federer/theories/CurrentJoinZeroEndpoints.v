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
  CurrentCartesianFirstProjection CurrentCartesianFirstProjectionZero CurrentCompactSmoothValue CurrentJoinDomain
  CurrentJoinSliceMapClass CurrentJoinSlicePushforward CurrentJoinEndpointProjections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinZeroEndpoints.
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
Local Notation C := (fun k=>@current_space R h2 n Full hFull k).
Local Notation Compact := (fun k (P:C k)=>
  @compact (real_norm_metric_space hNX) (@current_support R h2 n Full hFull k P)).
Local Notation Tr := (fun a b (e:a=b)=>@current_degree_transport R h2 n Full hFull a b e).

(** Source for [current_join_start_zero]: when j=0, the
    first endpoint is T(1)S, giving the second and fourth boundary
    cases of Federer 4.1.11, p. 365. The actual smooth-dual total
    is used, including zero currents and dimension zero. *)
Theorem current_join_start_zero (S:C i) (T:C 0%N)
    (hS:Compact i S) (hT:Compact 0%N T):
  Tr _ _ (addn0 i) (@current_join_slice_pushforward R h2 n i 0%N S T hS hT 0)=
    (@current_compact_total R h2 n Full hFull T hT)*:S.
Proof.
exact:(eq_trans (@current_join_start_projection_pushforward R h2 n i 0%N S T hS hT
  i (addn0 i))
  (@current_cartesian_first_projection_zero R h2 n n Full Full hFull hFull
    i S T hS hT)).
Qed.

(** Source for [current_join_end_zero]: when i=0, the
    second endpoint is S(1)T, giving the third and fourth boundary
    cases of Federer 4.1.11, p. 365. Both original compact current
    factors are retained without a representation premise. *)
Theorem current_join_end_zero (S:C 0%N) (T:C j)
    (hS:Compact 0%N S) (hT:Compact j T):
  @current_join_slice_pushforward R h2 n 0%N j S T hS hT 1=
    (@current_compact_total R h2 n Full hFull S hS)*:T.
Proof.
exact:(eq_trans (@current_join_end_projection_pushforward R h2 n 0%N j S T hS hT)
  (@current_cartesian_projection_zero R h2 n n Full Full hFull hFull
    j S T hS)).
Qed.
End CurrentJoinZeroEndpoints.
