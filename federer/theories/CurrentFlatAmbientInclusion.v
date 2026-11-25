(** Federer (1969), 4.1.18, pp. 375–376:
    reduce the original open-U representation to all of
    R^n by the already proved compact identity inclusion.
    The same K and its exact flat norm are preserved;
    compactness is derived from flat membership. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations NormClassOneUP NormClassOneLocalLipschitz
  NormLocalLipschitzScalarProduct LipschitzUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet SmoothCompactSetExtensionality
  CurrentOpenIdentitySmooth CurrentLipschitzCompactImage
  CurrentCompactLipschitzPushforwardSealed CurrentCompactLipschitzPushforwardSmooth
  CurrentCompactPushforwardAlgebra CurrentCompactMapProper CurrentProperSupport
  CurrentCompactInclusionRestriction CurrentOpenRestriction CurrentFlatOpenRestrictionNorm
  CurrentFlatNorm FlatCurrentsUP FlatCurrentFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_flat_ambient_inclusion]: the original
    flat current on U has an ambient flat representative
    in exactly K, whose restriction is T and whose F_K
    value is unchanged, supporting Federer 4.1.18,
    pp. 375–376. There is no finite-mass premise. *)
Theorem current_flat_ambient_inclusion (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current_supported_in R h2 n m U hU K T):
  let Full:=fun _:R_n R n=>True in
  let hFull:=fun (x:R_n R n) (_:True)=>norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) x in
  let KF:=@current_compact_index_in_open R n U Full K (fun _ _=>Logic.I) in
  exists Q:@current_space R h2 n Full hFull m,
    @is_flat_current_supported_in R h2 n m Full hFull KF Q /\
    @current_open_restriction R h2 n m U Full hU hFull (fun _ _=>Logic.I) Q=T /\
    @current_flat_norm R h2 n m Full hFull KF Q=
      @current_flat_norm R h2 n m U hU K T.
Proof.
move=>Full hFull KF.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose image:=fun (x:X) (_:U x)=>Logic.I.
pose hId:=@current_open_identity_smooth R n U hU.
have hLocal:@is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNX) U (fun x=>x).
  apply:(@norm_class_one_locally_metric_lipschitz R X X NX NX hNX hNX U (fun x=>x)).
  apply:((@norm_class_firstP R X X NX NX hNX hNX U (fun x=>x)).1).
  exact:hId 1.
pose fK:=@current_lipschitz_compact_image R n n U Full hU (fun x:X=>x) image hLocal K.
have hIndex:fK=KF.
  apply:smooth_compact_set_extensionality.
  rewrite current_lipschitz_compact_image_carrier.
  apply/seteqP;split.
  - by move=>x [y hy <-].
  - move=>x hx;by exists x.
pose Q:=@CurrentCompactLipschitzPushforward.value R h2 n n m U Full hU hFull
  (fun x:X=>x) image hLocal K T hFlat.
have hQFlat:@is_flat_current_supported_in R h2 n m Full hFull KF Q.
  have h:@is_flat_current_supported_in R h2 n m Full hFull fK Q:=
    (@CurrentCompactLipschitzPushforward.laws R h2 n n m U Full hU hFull
    (fun x:X=>x) image hLocal K T hFlat).1.
  by rewrite hIndex in h.
pose hCompact:=@flat_supported_current_compact R h2 n m U hU K T hFlat.
pose hProper:=@current_compact_map_proper R h2 n n m U Full hU T
  (fun x:X=>x) image (norm_class_continuous (hId 0%N)) hCompact.
have hRecovery:@current_open_restriction R h2 n m U Full hU hFull image Q=T.
  rewrite /Q (@current_compact_lipschitz_pushforward_smooth R h2 n n m
    U Full hU hFull (fun x:X=>x) image hLocal K T hFlat hId).
  exact:(@current_compact_inclusion_restriction R h2 n U Full hU hFull image
    m T hCompact hId hProper).
have hSupport:=@flat_current_supported_support R h2 n m Full hFull KF Q hQFlat.
have hKBack:@current_compact_index_in_open R n Full U KF
    (smooth_compact_in_domain K)=K by apply:smooth_compact_set_extensionality.
have hNorm:=@current_open_restriction_flat_norm R h2 n m Full U hFull hU image
  KF (smooth_compact_in_domain K) Q hSupport.
rewrite hKBack hRecovery in hNorm.
exists Q;split;first exact:hQFlat.
split;[exact:hRecovery|exact:esym hNorm].
Qed.
