(** Federer (1969), 4.1.24, p. 380: an original
    defining image witness remains such a witness under
    a locally Lipschitz target map. Restrict the source
    over a Lipschitz neighbourhood of K, preserve the
    same polyhedral compact, and use the registered actual
    pushforward composition and source-neighbourhood laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic MetricLocalLipschitzComposition
  SmoothCompactSet CurrentSpaces CurrentOpenRestriction CurrentSupportGeometry
  CurrentLipschitzCompactImage CurrentApproximationOpenRestriction
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentFlatLipschitzProofIndependence CurrentFlatLipschitzComposition
  CurrentFlatLipschitzSourceNeighbourhood FlatCurrentsUP
  PolyhedralCurrentAlgebra PolyhedralCurrentFlat PolyhedralNormal PolyhedralOpenRestriction
  RectifiableCurrentApproximationUP LocalLipschitzCompactNeighbourhood
  LipschitzSourceCompactRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableImageComposition.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R nu)) V y.
Variable g:X->Y.
Hypothesis hImage:forall x,U x->V (g x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g.
Variable K:smooth_compact_set hNX U.
Local Notation gK:=(@current_lipschitz_compact_image R n nu U V hU g hImage hLocal K).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Push:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV g hImage hLocal).

(** Source for [rectifiable_image_approximant_pushforward]: composition
    preserves the complete original image-witness class in
    4.1.24, p. 380, under the original locally
    Lipschitz g. The compact target index is exactly
    g(K). All extra neighbourhood and global-bound data
    are derived internally, including for empty compacts. *)
Theorem rectifiable_image_approximant_pushforward (Q:C)
    (hQ:@is_flat_current R h2 n m U hU Q):
  @is_rectifiable_image_approximant R h2 n m U hU K Q->
  @is_rectifiable_image_approximant R h2 nu m V hV gK (Push Q hQ).
Proof.
move=>[d [Z [hZ [A [f [hFImage [hFLip [P [hP [hAK hValue]]]]]]]]]].
have[W [hW [hKW [hWU hGLip]]]]:=@local_lipschitz_compact_neighbourhood
  R n nu U hU K g hLocal.
have hAW:forall x,smooth_compact_carrier A x->W (f x).
  move=>x hx;exact:hKW (f x) (hAK x hx).
have[B [hB [hAB [hBZ [hFW hCompositeLip]]]]]:=
  @lipschitz_source_compact_neighbourhood_restriction
    R d n nu Z hZ A W hW f g hFLip hGLip hAW.
pose AB:=@current_compact_index_in_open R d Z B A hAB.
pose P':=@current_open_restriction R h2 d m B Z hB hZ hBZ P.
pose hP':=@integral_polyhedral_current_open_restriction
  R h2 d m Z B hZ hB hBZ A hAB P hP.
pose H:=fun x:R_n R d=>g (f x).
pose hHImage:=fun x (hx:Z x)=>@hImage (f x) (@hFImage x hx).
pose hHBImage:=fun x (hx:B x)=>@hHImage x (@hBZ x hx).
exists d,B,hB,AB,H,hHBImage,hCompositeLip,P',hP';split.
- move=>x hx;change ((g @` smooth_compact_carrier K) (g (f x))).
  exists (f x);first exact:hAK x hx.
  by [].
- pose hFLocal:=metric_lipschitz_is_local hFLip.
  pose hHLocal:=@metric_local_lipschitz_composition R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (real_norm_metric_space hNX) (real_norm_metric_space hNY)
    Z U f g hFImage hFLocal hLocal.
  pose hHBLocal:=@metric_local_lipschitz_domain_restriction R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (real_norm_metric_space hNY) Z B H hBZ hHLocal.
  pose hPFlat:@is_flat_current R h2 d m Z hZ P:=ex_intro _ A
    (@integral_polyhedral_current_flat_supported R h2 d m Z hZ A P hP).
  pose hP'Flat:@is_flat_current R h2 d m B hB P':=ex_intro _ AB
    (@integral_polyhedral_current_flat_supported R h2 d m B hB AB P' hP').
  pose Q0:=@CurrentFlatLipschitzPushforward.value R h2 d n m Z U hZ hU
    f hFImage hFLocal P hPFlat.
  pose hQ0:=(@CurrentFlatLipschitzPushforward.laws R h2 d n m Z U hZ hU
    f hFImage hFLocal P hPFlat).1.
  have hQ0Value:Q0=Q by exact:hValue.
  have hComposition:=@current_flat_lipschitz_pushforward_composition
    R h2 d n nu m Z U V hZ hU hV f g hFImage hImage hFLocal hLocal P hPFlat.
  have hQImage:=@current_flat_lipschitz_pushforward_congruence
    R h2 n nu m U V hU hV g hImage hLocal Q0 Q hQ0 hQ hQ0Value.
  have hOriginal:@CurrentFlatLipschitzPushforward.value
      R h2 d nu m Z V hZ hV H hHImage hHLocal P hPFlat = Push Q hQ.
    exact:eq_trans hComposition hQImage.
  have hSupport:@current_support R h2 d Z hZ m P `<=` B.
    move=>x hx;apply:(hAB).
    exact:(@integral_polyhedral_current_normal_support R h2 d m Z hZ A P hP).2 x hx.
  have hRestrict:=@current_flat_lipschitz_pushforward_open_restriction
    R h2 d nu m Z B V hZ hB hV hBZ H hHImage hHLocal
    P hPFlat hSupport hP'Flat.
  apply:(eq_trans _ (eq_trans (esym hRestrict) hOriginal)).
  unfold polyhedral_lipschitz_image.
  exact:current_flat_lipschitz_pushforward_data_independent.
Qed.
End RectifiableImageComposition.
