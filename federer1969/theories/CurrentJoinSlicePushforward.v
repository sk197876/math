(** Federer (1969), 4.1.11, p. 365, opening paragraph:
    compose the original insertion pushforward with F. The
    preceding composition law gives the first and second
    projections at the endpoints. Both input currents remain
    arbitrary under their original compact-support hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormClassOneUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianCompactCurrents CurrentProperSupport
  CurrentCompactMapProper SmoothFormPullbackComposition CurrentCompositeProperness
  CurrentPushforwardSealed CurrentPushforwardCompositionParameters
  CurrentPushforwardMapAgreement CurrentJoinDomain
  CurrentJoinMapSealed CurrentJoinMapClass CurrentJoinSliceMapSealed
  CurrentJoinSliceMapClass CurrentJoinSliceProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinSlicePushforward.
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

Local Notation Slice := (@current_join_slice_current R h2 n i j S T hS hT t).
Local Notation F := (@CurrentJoinMap.value R n).
Local Notation FImage := (@current_join_map_image R n).
Local Notation FClass := (@current_join_map_smooth R n Domain hDomain).
Local Notation FProper := (@current_compact_map_proper R h2
  (n+(1+n))%N n (i+j)%N Domain Full hDomain Slice F FImage
  (norm_class_continuous (FClass 0%N))
  (@current_join_slice_current_compact R h2 n i j S T hS hT t)).

(** Source for [current_join_slice_pushforward]: the actual
    F#(G_t#(S times T)), supporting Federer 4.1.11, p. 365.
    This is an alias of the original opaque proper pushforward. *)
Definition current_join_slice_pushforward :
    @current_space R h2 n Full hFull (i+j)%N :=
  @CurrentPushforward.value R h2 (n+(1+n))%N n (i+j)%N
    Domain Full hDomain hFull Slice F FImage FClass FProper.

(** Source for [current_join_slice_pushforward_map]: if f is
    the actual F composed with G_t on the source, its image of
    S times T equals F#(G_t#(S times T)). This supporting form
    of composition gives the two projections in Federer 4.1.11,
    p. 365. No condition beyond smoothness and properness is added. *)
Theorem current_join_slice_pushforward_map
    (f:Source->X)
    (hImage:forall z,AB z->Full (f z))
    (hf:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R (n+n)%N)) hNX AB f)
    (hp:@is_current_proper_on_support R h2 (n+n)%N n (i+j)%N
      AB hAB Full Product f hImage):
  (forall z,AB z->F (G z)=f z)->
  current_join_slice_pushforward=
    @CurrentPushforward.value R h2 (n+n)%N n (i+j)%N
      AB Full hAB hFull Product f hImage hf hp.
Proof.
move=>hMap.
pose gfImage:=@current_smooth_composite_image R (n+n)%N (n+(1+n))%N n
  AB Domain Full G F GImage FImage.
pose gfClass:=@current_smooth_composite_class R (n+n)%N (n+(1+n))%N n
  AB Domain G F GImage GClass FClass.
have gfProper:@is_current_proper_on_support R h2 (n+n)%N n (i+j)%N
    AB hAB Full Product (fun z=>F (G z)) gfImage.
  exact:(@current_compact_map_proper R h2 (n+n)%N n (i+j)%N
    AB Full hAB Product (fun z=>F (G z)) gfImage
    (norm_class_continuous (gfClass 0%N)) hProductCompact).
have hComposition:=@current_pushforward_composition_parameters R h2
  (n+n)%N (n+(1+n))%N n (i+j)%N AB Domain Full hAB hDomain hFull
  G F GImage FImage GClass FClass Product gfProper GProper FProper.
have hComparison:=@current_pushforward_map_agreement R h2 (n+n)%N n (i+j)%N
  AB Full hAB hFull (fun z=>F (G z)) f gfImage hImage gfClass hf
  Product gfProper hp hMap.
exact:(eq_trans (esym hComposition) hComparison).
Qed.
End CurrentJoinSlicePushforward.
