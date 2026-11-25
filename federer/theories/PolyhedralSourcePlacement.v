(** Federer (1969), 4.1.24, p. 380: restricting
    an original polyhedral source near its compact and
    placing it by an affine inclusion preserves its
    original image under the glued source map. Use
    only actual open restriction, affine polyhedral images,
    flat pushforward composition and domain agreement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic MetricLocalLipschitzComposition SmoothCompactSet
  CurrentSpaces CurrentOpenRestriction CurrentLipschitzCompactImage
  CurrentApproximationOpenRestriction CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic CurrentFlatLipschitzComposition
  CurrentFlatLipschitzSourceNeighbourhood CurrentLipschitzPushforwardExtensional
  FlatCurrentsUP PolyhedralCurrentAlgebra PolyhedralCurrentFlat PolyhedralNormal
  PolyhedralOpenRestriction PolyhedralFlatAffinePushforward RectifiableCurrentApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralSourcePlacement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables d e n m:nat.
Local Notation X:=(R_n R d).
Local Notation Y:=(R_n R e).
Local Notation V:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R d)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R e)).
Local Notation hNV:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (Z A:set X) (W:set Y) (U:set V).
Hypothesis hZ:forall x,Z x->norm_domain_interior (inner_norm (@euclidean_inner_productP R d)) Z x.
Hypothesis hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R d)) A x.
Hypothesis hW:forall x,W x->norm_domain_interior (inner_norm (@euclidean_inner_productP R e)) W x.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Hypothesis hAZ:forall x,A x->Z x.
Variable C:smooth_compact_set hNX Z.
Hypothesis hCA:smooth_compact_carrier C `<=` A.
Variable L:smooth_compact_set hNY W.
Variables (f:X->V) (E:X->Y) (F:Y->V).
Hypothesis hFImage:forall x,Z x->U (f x).
Hypothesis hFLip:@is_metric_lipschitz R (real_norm_metric_space hNX)
  (real_norm_metric_space hNV) Z f.
Hypothesis hAffine:is_affine_map E.
Hypothesis hEImage:forall x,A x->W (E x).
Hypothesis hELip:@is_metric_lipschitz R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) A E.
Hypothesis hImage:forall x,W x->U (F x).
Hypothesis hLip:@is_metric_lipschitz R (real_norm_metric_space hNY)
  (real_norm_metric_space hNV) W F.
Hypothesis hCL:forall x,smooth_compact_carrier C x->smooth_compact_carrier L (E x).
Hypothesis hValues:forall x,A x->F (E x)=f x.
Variable P:@current_space R h2 d Z hZ m.
Hypothesis hP:@integral_polyhedral_current_class R h2 d m Z hZ C P.

(** Source for [polyhedral_source_placement_exists]: each original
    polyhedral source can be placed in the common
    source without altering its current image, the
    source-placement step behind addition in 4.1.24,
    p. 380. The output uses the original exact
    compact L and accepts every flat-membership witness. *)
Theorem polyhedral_source_placement_exists:
  exists Q:@current_space R h2 e W hW m,
    @integral_polyhedral_current_class R h2 e m W hW L Q /\
    forall hQ:@is_flat_current R h2 e m W hW Q,
      @CurrentFlatLipschitzPushforward.value R h2 e n m W U hW hU F hImage
        (metric_lipschitz_is_local hLip) Q hQ=
      @polyhedral_lipschitz_image R h2 d n m Z U hZ hU C f hFImage hFLip P hP.
Proof.
pose CA:=@current_compact_index_in_open R d Z A C hCA.
pose S:=@current_open_restriction R h2 d m A Z hA hZ hAZ P.
pose hSPoly:=@integral_polyhedral_current_open_restriction
  R h2 d m Z A hZ hA hAZ C hCA P hP.
pose hSFlat:@is_flat_current R h2 d m A hA S:=ex_intro _ CA
  (@integral_polyhedral_current_flat_supported R h2 d m A hA CA S hSPoly).
pose hE:=metric_lipschitz_is_local hELip.
pose hF:=metric_lipschitz_is_local hLip.
pose Q:=@CurrentFlatLipschitzPushforward.value R h2 d e m A W hA hW
  E hEImage hE S hSFlat.
pose hQ:=(@CurrentFlatLipschitzPushforward.laws R h2 d e m A W hA hW
  E hEImage hE S hSFlat).1.
have hQPoly:@integral_polyhedral_current_class R h2 e m W hW L Q.
  exact:(@integral_polyhedral_current_flat_affine_pushforward R h2 d e m A W hA hW
    E hAffine hEImage hE CA L hCL S hSPoly hSFlat).
exists Q;split;first exact:hQPoly.
move=>hQOther.
have hProof:=@current_flat_lipschitz_pushforward_proof_independent
  R h2 e n m W U hW hU F hImage hF Q hQOther hQ.
have hComposition:=@current_flat_lipschitz_pushforward_composition
  R h2 d e n m A W U hA hW hU E F hEImage hImage hE hF S hSFlat.
pose H:=fun x:X=>F (E x).
pose hHImage:=fun x (hx:A x)=>@hImage (E x) (@hEImage x hx).
pose hHLocal:=@metric_local_lipschitz_composition R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) (real_norm_metric_space hNV)
  A W E F hEImage hE hF.
pose hOriginalLocal:=metric_lipschitz_is_local hFLip.
pose hOriginalImageA:=fun x (hx:A x)=>@hFImage x (@hAZ x hx).
pose hOriginalLocalA:=@metric_local_lipschitz_domain_restriction
  R (real_norm_metric_space hNX) (real_norm_metric_space hNV) Z A f hAZ hOriginalLocal.
have hAgreement:=@current_flat_lipschitz_pushforward_domain_agreement
  R h2 d n m A U hA hU H f hHImage hOriginalImageA hHLocal hOriginalLocalA
  hValues S hSFlat.
pose hPFlat:@is_flat_current R h2 d m Z hZ P:=ex_intro _ C
  (@integral_polyhedral_current_flat_supported R h2 d m Z hZ C P hP).
have hSupport:@current_support R h2 d Z hZ m P `<=` A.
  move=>x hx;apply:(hCA).
  exact:(@integral_polyhedral_current_normal_support R h2 d m Z hZ C P hP).2 x hx.
have hRestriction:=@current_flat_lipschitz_pushforward_open_restriction
  R h2 d n m Z A U hZ hA hU hAZ f hFImage hOriginalLocal P hPFlat hSupport hSFlat.
unfold polyhedral_lipschitz_image.
exact:(eq_trans hProof (eq_trans (esym hComposition)
  (eq_trans hAgreement (esym hRestriction)))).
Qed.
End PolyhedralSourcePlacement.
