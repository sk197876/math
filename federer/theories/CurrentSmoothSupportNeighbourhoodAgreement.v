(** Federer (1969), 4.1.15, p. 372: the two
    smooth image currents agree because the smoothed maps
    agree on an open neighbourhood of the actual support.
    Restrict to that neighbourhood and apply the original
    smooth map-agreement and source-recovery laws. This
    supporting statement holds for every compact current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormClassOneUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentSupportGeometry CurrentProperSupport CurrentCompactMapProper
  CurrentPushforwardSealed CurrentCompactPushforwardAlgebra
  CurrentPushforwardNeighbourhoodParameters CurrentPushforwardMapAgreement
  CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentOpenIdentitySmooth SmoothClassOpenRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentSmoothSupportNeighbourhoodAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall x,U x->V (g x).
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNX hNY U g.
Variable T:@current_space R h2 n U hU m.
Hypothesis hCompact:@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU m T).
Variable W:set X.
Hypothesis hW:forall x,W x->norm_domain_interior NX W x.
Hypothesis hWU:forall x,W x->U x.
Hypothesis hSupport:@current_support R h2 n U hU m T `<=` W.
Hypothesis hAgreement:forall x,W x->f x=g x.

(** Source for [current_smooth_support_neighbourhood_agreement]:
    the equality of the two smooth images preceding the
    support-coincidence theorem in Federer 4.1.15, p. 372.
    The neighbourhood may depend on the approximation index;
    no equality on the whole original compact index is used. *)
Theorem current_smooth_support_neighbourhood_agreement:
  @current_compact_map_pushforward R h2 n nu U V hU hV
    f hFImage hf m T hCompact=
  @current_compact_map_pushforward R h2 n nu U V hU hV
    g hGImage hg m T hCompact.
Proof.
pose S:=@current_open_restriction R h2 n m W U hW hU hWU T.
have hSupportEqual:@current_support R h2 n W hW m S=
    @current_support R h2 n U hU m T.
  rewrite (@current_open_restriction_support R h2 n m W U hW hU hWU T).
  apply:funext=>x;apply:propext;split.
  - exact:proj2.
  - move=>hx;exact:conj (@hSupport x hx) hx.
have hSCompact:@compact (real_norm_metric_space hNX)
    (@current_support R h2 n W hW m S).
  by rewrite hSupportEqual.
pose hId:=@current_open_identity_smooth R n W hW.
pose hIProper:=@current_compact_map_proper R h2 n n m W U hW S
  (fun x:X=>x) hWU (norm_class_continuous (hId 0%N)) hSCompact.
pose hFImageW:=fun x (hx:W x)=>@hFImage x (@hWU x hx).
pose hGImageW:=fun x (hx:W x)=>@hGImage x (@hWU x hx).
pose hfW:=@smooth_class_open_restriction R X Y NX NY hNX hNY
  U W f hWU hW hf.
pose hgW:=@smooth_class_open_restriction R X Y NX NY hNX hNY
  U W g hWU hW hg.
pose hFProperU:=@current_compact_map_proper R h2 n nu m U V hU T f hFImage
  (norm_class_continuous (hf 0%N)) hCompact.
pose hGProperU:=@current_compact_map_proper R h2 n nu m U V hU T g hGImage
  (norm_class_continuous (hg 0%N)) hCompact.
pose hFProperW:=@current_compact_map_proper R h2 n nu m W V hW S f hFImageW
  (norm_class_continuous (hfW 0%N)) hSCompact.
pose hGProperW:=@current_compact_map_proper R h2 n nu m W V hW S g hGImageW
  (norm_class_continuous (hgW 0%N)) hSCompact.
have hFSource:=@current_pushforward_neighbourhood_parameters R h2 n nu m
  W U V hW hU hV hWU hId f hFImage hf hFImageW hfW T hSupport
  hIProper hFProperW hFProperU.
have hGSource:=@current_pushforward_neighbourhood_parameters R h2 n nu m
  W U V hW hU hV hWU hId g hGImage hg hGImageW hgW T hSupport
  hIProper hGProperW hGProperU.
have hSame:=@current_pushforward_map_agreement R h2 n nu m W V hW hV
  f g hFImageW hGImageW hfW hgW S hFProperW hGProperW hAgreement.
exact:(eq_trans hFSource (eq_trans hSame (esym hGSource))).
Qed.
End CurrentSmoothSupportNeighbourhoodAgreement.
