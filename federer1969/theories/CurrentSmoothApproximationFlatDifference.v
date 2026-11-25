(** Federer (1969), 4.1.14, p. 371: control the
    difference of two smooth images by the original
    source flat error and the common derivative cap
    only on K. This supplies the third term in the
    printed extension argument; neither input need be
    normal or have finite mass. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormClassOneUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct SmoothCompactSet CurrentSpaces CurrentSupportGeometry
  CurrentCompactPushforwardAlgebra CurrentSmoothApproximationUP
  CurrentSmoothApproximationCompactImage CurrentSmoothPushforwardFlatBound
  CurrentFlatNorm CurrentLipschitzFlatCoefficient CurrentMapDifferential EuclideanHomOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSmoothApproximationFlatDifference.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (Z:set X) (V:set Y).
Hypothesis hZ:forall x,Z x->norm_domain_interior NX Z x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable K:smooth_compact_set hNX Z.
Variable f:X->Y.
Variable g:nat->X->Y.
Hypothesis hG:@is_current_smooth_approximation R n nu Z V K f g.
Hypothesis hImage:forall x,Z x->V (f x).
Hypothesis hf:norm_class_zero NX NY Z f.
Variable E:smooth_compact_set hNY V.
Hypothesis hInterior:forall x,smooth_compact_carrier K x->
  norm_domain_interior NY (smooth_compact_carrier E) (f x).
Variable c:R.
Hypothesis hc:0<=c.
Hypothesis hCap:forall i x,smooth_compact_carrier K x->
  @euclidean_operator_norm R n nu (@current_map_differential R n nu Z (g i) x)<=c.
Local Notation C:=(@current_space R h2 n Z hZ m).
Local Notation support:=(@current_support R h2 n Z hZ m).
Local Notation compactSupport:=(fun T:C=>@compact (real_norm_metric_space hNX) (support T)).
Local Notation Push:=(fun i (T:C) (hT:compactSupport T)=>
  @current_compact_map_pushforward R h2 n nu Z V hZ hV
    (g i) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) m T hT).

(** Source for [current_smooth_approximation_flat_difference_bound]:
    the original smooth images of the source error have
    uniformly bounded F_E, Federer 4.1.14, p. 371.
    Only finiteness of the source flat difference is used;
    no finite mass or flat-closure premise is added. *)
Theorem current_smooth_approximation_flat_difference_bound
    (S A:C) (hS:compactSupport S) (hA:compactSupport A):
  support S `<=` smooth_compact_carrier K ->
  support A `<=` smooth_compact_carrier K ->
  (@current_flat_norm R h2 n m Z hZ K (S-A) < +oo)%E ->
  exists N:nat,forall i,(N<=i)%N->
    (@current_flat_norm R h2 nu m V hV E (Push i S hS-Push i A hA)<=
      (current_lipschitz_flat_coefficient m c)%:E*
        @current_flat_norm R h2 n m Z hZ K (S-A))%E.
Proof.
move=>hSK hAK hFinite.
have hDifference:support (S-A) `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m Z hZ K (-1) A S hAK hSK.
  by rewrite scaleN1r addrC in h.
pose hCompact:=@current_support_compact_bound R h2 n m Z hZ K (S-A) hDifference.
have[N hN]:=@current_smooth_approximation_eventual_compact_image R n nu Z V K f g
  hG hImage hf E hInterior.
exists N=>i hNi.
have hBound:=@current_smooth_pushforward_flat_bound R h2 n nu m Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) K E (hN i hNi) c hc (hCap i)
  (S-A) hCompact hDifference hFinite.
have hEqual:=@current_compact_map_pushforward_subtract R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m S A hS hA hCompact.
by rewrite hEqual in hBound.
Qed.
End CurrentSmoothApproximationFlatDifference.
