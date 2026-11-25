(** Federer (1969), 4.1.15, p. 373: a Lipschitz
    retraction of K onto C identifies the flat currents
    indexed by C with the K-indexed flat currents supported
    in C. Extend the original K-map by 2.10.43,
    restrict to a derived source mapping into U, and
    apply support-only coincidence to the actual restriction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology NormClassOneUP NormRegularity NormClassHigherRestriction
  NormOpenPreimage NormLocalLipschitzScalarProduct InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP LipschitzBasic
  EuclideanLipschitzClassZero KirszbraunExtensionUP KirszbraunExtension RetractionUP
  SmoothCompactSet CurrentSpaces CurrentSupportGeometry FlatCurrentsUP FlatCurrentFinite
  CurrentFlatCompactMonotone CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentFlatOpenRestriction CurrentLipschitzCompactImage CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentOpenIdentitySmooth CurrentFlatSmoothPushforward
  CurrentFlatLipschitzPushforwardSealed CurrentApproximationOpenRestriction
  CurrentFlatLipschitzSupportAgreement CurrentCompactRetractionExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentFlatLipschitzRetraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation MX:=(real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variables K C:smooth_compact_set hNX U.
Variable r:X->X.
Hypothesis hRetraction:@is_metric_retraction R MX
  (smooth_compact_carrier K) (smooth_compact_carrier C) r.
Hypothesis hLip:@is_metric_lipschitz R MX MX (smooth_compact_carrier K) r.
Variable T:@current_space R h2 n U hU m.

(** Source for [current_flat_retraction_localisation]:
    F_(m,K)(U) intersect {T:sptT contained in C}
    equals F_(m,C)(U), Federer 4.1.15, p. 373.
    The retraction is given only on K; its original
    extension into U is derived on a neighbourhood.
    Empty K and C are included. *)
Theorem current_flat_retraction_localisation:
  (@is_flat_current_supported_in R h2 n m U hU K T /\
    @current_support R h2 n U hU m T `<=` smooth_compact_carrier C) <->
  @is_flat_current_supported_in R h2 n m U hU C T.
Proof.
pose hCK:=@metric_retraction_subset R MX
  (smooth_compact_carrier K) (smooth_compact_carrier C) r hRetraction.
split.
- move=>[hTK hTC].
  have[F [Z [hZ [hKZ [hZU [hFImage [hFLip [hAgreement [hFixedC hContinuous]]]]]]]]]:=
    @current_compact_retraction_extension_exists R n U hU K
      (smooth_compact_carrier C) r hRetraction hLip.
  pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
  pose S:=@current_open_restriction R h2 n m Z U hZ hU hZU T.
  pose hS:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hTK.
  have hSGlobal:@is_flat_current R h2 n m Z hZ S by exists KZ.
  pose hSCompact:=@flat_supported_current_compact R h2 n m Z hZ KZ S hS.
  have hSC:@current_support R h2 n Z hZ m S `<=` smooth_compact_carrier C.
    move=>x hx;apply:(@hTC x).
    exact:(@current_open_restriction_support_subset R h2 n m Z U hZ hU hZU T x hx).
  pose hFLocal:=@metric_lipschitz_is_local R MX MX Z F hFLip.
  pose hIdClass:=@current_open_identity_smooth R n Z hZ.
  pose hIdLocal:=@norm_class_one_locally_metric_lipschitz R X X NX NX hNX hNX
    Z (fun x:X=>x)
    ((@norm_class_firstP R X X NX NX hNX hNX Z (fun x:X=>x)).1 (hIdClass 1%N)).
  have hFixed:forall x,@current_support R h2 n Z hZ m S x->F x=x.
    move=>x hx.
    exact:(@hFixedC x (@hSC x hx)).
  have hSame:=@current_flat_lipschitz_support_agreement R h2 n n m Z U hZ hU
    F (fun x:X=>x) hFImage hZU hFLocal hIdLocal S hSGlobal hFixed.
  pose Q:=@CurrentFlatLipschitzPushforward.value R h2 n n m Z U hZ hU
    F hFImage hFLocal S hSGlobal.
  pose hIdProper:=@current_compact_map_proper R h2 n n m Z U hZ S
    (fun x:X=>x) hZU (norm_class_continuous (hIdClass 0%N)) hSCompact.
  have hIdSmooth:=@current_flat_lipschitz_pushforward_smooth R h2 n n m Z U hZ hU
    (fun x:X=>x) hZU hIdLocal S hSGlobal hIdClass hIdProper.
  have hRecover:=@flat_current_neighbourhood_inclusion_recovery R h2 n m
    U Z hU hZ hZU K hKZ T hTK hSCompact.
  have hQT:Q=T:=eq_trans hSame (eq_trans hIdSmooth hRecover).
  pose FK:=@current_lipschitz_compact_image R n n Z U hZ F hFImage hFLocal KZ.
  have hFKC:smooth_compact_carrier FK `<=` smooth_compact_carrier C.
    move=>y [x hx <-].
    rewrite (@hAgreement x hx).
    exact:(@metric_retraction_range R MX (smooth_compact_carrier K)
      (smooth_compact_carrier C) r hRetraction x hx).
  have hQFK:=((@CurrentFlatLipschitzPushforward.laws R h2 n n m
    Z U hZ hU F hFImage hFLocal S hSGlobal).2 KZ hS).1.
  have hQC:=@flat_current_compact_monotone R h2 n m U hU FK C hFKC Q hQFK.
  by rewrite -hQT.
- move=>hC;split.
  + exact:(@flat_current_compact_monotone R h2 n m U hU C K hCK T hC).
  + exact:(@flat_current_supported_support R h2 n m U hU C T hC).
Qed.
End CurrentFlatLipschitzRetraction.

Arguments current_flat_retraction_localisation : clear implicits.
