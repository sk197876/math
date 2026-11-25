(** Federer (1969), 4.1.15, p. 373: the actual
    flat image under a constant map vanishes in positive
    degree and is T(1) delta_u in degree zero.
    These are the original smooth constant-image laws of
    4.1.10, p. 364, applied through 4.1.14. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP
  CurrentSpaces CurrentProperSupport CurrentCompactMapProper
  CurrentCompactSmoothValue CurrentDirac CurrentElementaryPushforwards
  CurrentLipschitzCompactImage FlatCurrentsUP
  CurrentFlatLipschitzPushforwardSealed CurrentFlatSmoothPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentFlatConstantPushforward.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables U V:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall x,V x->norm_domain_interior NX V x.
Variable u:X.
Hypothesis hImage:forall x,U x->V u.
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNX) U (fun _:X=>u).
Local Notation hSmooth:=(fun k=>@norm_class_constant R X X NX NX hNX hNX U u k hU).

(** Source for [current_flat_constant_positive_pushforward]: the
    retraction onto a point sends a positive-degree flat
    current to zero, Federer 4.1.15, p. 373,
    by the original 4.1.10 formula on p. 364.
    Flat membership supplies compact support; finite mass
    and normality are not assumed. *)
Theorem current_flat_constant_positive_pushforward j
    (T:@current_space R h2 n U hU j.+1)
    (hFlat:@is_flat_current R h2 n j.+1 U hU T):
  @CurrentFlatLipschitzPushforward.value R h2 n n j.+1 U V hU hV
    (fun _:X=>u) hImage hLocal T hFlat=0.
Proof.
have[K hK]:=hFlat.
pose hCompact:=@flat_supported_current_compact R h2 n j.+1 U hU K T hK.
pose hProper:=@current_compact_map_proper R h2 n n j.+1 U V hU T
  (fun _:X=>u) hImage (norm_class_continuous (hSmooth 0%N)) hCompact.
rewrite (@current_flat_lipschitz_pushforward_smooth R h2 n n j.+1
  U V hU hV (fun _:X=>u) hImage hLocal T hFlat hSmooth hProper).
exact:(@current_compact_constant_positive_pushforward R h2 n U hU
  j V hV u T hCompact hImage hSmooth hProper).
Qed.

(** Source for [current_flat_constant_zero_pushforward]: the
    original degree-zero constant image is T(1) delta_u,
    used for the point formula in Federer 4.1.15,
    p. 373. Every compactness witness of the same
    current is accepted, and no measure representation is
    a premise. *)
Theorem current_flat_constant_zero_pushforward
    (T:@current_space R h2 n U hU 0%N)
    (hFlat:@is_flat_current R h2 n 0%N U hU T)
    (hCompact:@compact (real_norm_metric_space hNX)
      (@current_support R h2 n U hU 0%N T)):
  @CurrentFlatLipschitzPushforward.value R h2 n n 0%N U V hU hV
    (fun _:X=>u) hImage hLocal T hFlat=
  @current_compact_total R h2 n U hU T hCompact*:
    @dirac_current R h2 n V hV u.
Proof.
pose hProper:=@current_compact_map_proper R h2 n n 0%N U V hU T
  (fun _:X=>u) hImage (norm_class_continuous (hSmooth 0%N)) hCompact.
rewrite (@current_flat_lipschitz_pushforward_smooth R h2 n n 0%N
  U V hU hV (fun _:X=>u) hImage hLocal T hFlat hSmooth hProper).
exact:(@current_compact_constant_zero_pushforward R h2 n U hU
  V hV u T hCompact hImage hSmooth hProper).
Qed.
End CurrentFlatConstantPushforward.
