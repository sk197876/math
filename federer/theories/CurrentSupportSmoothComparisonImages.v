(** Federer (1969), 4.1.15, p. 372: a common
    sequence of actual smooth images has both proposed
    Lipschitz images as its limit. Apply the original
    universal convergence condition of 4.1.14 and uniqueness
    on actual tests. The original compact index K is
    retained throughout; no mass premise occurs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormClassOneUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LipschitzUP
  SmoothCompactSet SmoothCompactNeighbourhoods CurrentSpaces CurrentSupportGeometry
  FlatCurrentsUP CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentFlatLipschitzPushforwardSealed CurrentSmoothApproximationUP
  CurrentOpenRestriction CurrentOpenRestrictionSupport CurrentFlatOpenRestriction
  CurrentCompactPushforwardAlgebra CurrentWeakSequenceLimit CurrentFlatSequenceLimits
  CurrentSupportSmoothComparisonUP CurrentSmoothSupportNeighbourhoodAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentSupportSmoothComparisonImages.
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
Hypothesis hFLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g.
Variable K:smooth_compact_set hNX U.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlatK:@is_flat_current_supported_in R h2 n m U hU K T.
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Variable Z:set X.
Variables a b:nat->X->Y.
Hypothesis hComparison:@is_current_support_smooth_comparison R n nu U V K f g
  (@current_support R h2 n U hU m T) Z a b.
Local Notation QF:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
  f hFImage hFLocal T hFlat).
Local Notation QG:=(@CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
  g hGImage hGLocal T hFlat).

(** Source for [current_support_smooth_comparison_images]: the
    conclusion from the two actual smooth approximations in
    Federer 4.1.15, p. 372. This supporting law
    accepts any witness of the independent comparison specification;
    its existence is discharged by the original radial smoothing. *)
Theorem current_support_smooth_comparison_images:QF=QG.
Proof.
pose hZ:=support_smooth_comparison_open hComparison.
pose hZU:=support_smooth_comparison_source hComparison.
pose hKZ:=support_smooth_comparison_contains hComparison.
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose hA:=support_smooth_comparison_first hComparison.
pose hB:=support_smooth_comparison_second hComparison.
pose S:=@current_open_restriction R h2 n m Z U hZ hU hZU T.
pose hS:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hFlatK.
pose hCompact:=@flat_supported_current_compact R h2 n m Z hZ KZ S hS.
have hInclusion:=@flat_current_neighbourhood_inclusion_recovery R h2 n m
  U Z hU hZ hZU K hKZ T hFlatK hCompact.
pose P:=fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (a i) (current_smooth_approximation_image hA i)
  (current_smooth_approximation_class hA i) m S hCompact.
pose Q:=fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (b i) (current_smooth_approximation_image hB i)
  (current_smooth_approximation_class hB i) m S hCompact.
have hSame:P=Q.
  apply:funext=>i.
  have[W [hW [hWZ [hTW hEqual]]]]:=support_smooth_comparison_neighbourhood hComparison i.
  have hSW:@current_support R h2 n Z hZ m S `<=` W.
    move=>x hx;apply:(@hTW x).
    exact:(@current_open_restriction_support_subset R h2 n m Z U hZ hU hZU T x hx).
  exact:(@current_smooth_support_neighbourhood_agreement R h2 n nu m Z V hZ hV
    (a i) (b i) (current_smooth_approximation_image hA i)
    (current_smooth_approximation_image hB i) (current_smooth_approximation_class hA i)
    (current_smooth_approximation_class hB i) S hCompact W hW hWZ hSW hEqual).
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hFImage hFLocal K.
pose gK:=@current_lipschitz_compact_image R n nu U V hU g hGImage hGLocal K.
have[EF hEF]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have[EG hEG]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV gK.
have hFInside x (hx:smooth_compact_carrier K x):
    norm_domain_interior NY (smooth_compact_carrier EF) (f x).
  apply:hEF;by exists x.
have hGInside x (hx:smooth_compact_carrier K x):
    norm_domain_interior NY (smooth_compact_carrier EG) (g x).
  apply:hEG;by exists x.
have hFPoint:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
  f hFImage hFLocal T hFlat).2 K hFlatK.
have hGPoint:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
  g hGImage hGLocal T hFlat).2 K hFlatK.
have hFLimit:=hFPoint.2 EF hFInside Z hZ hZU hKZ S hS hInclusion a hA.
have hGLimit:=hGPoint.2 EG hGInside Z hZ hZU hKZ S hS hInclusion b hB.
have hFWeak:=@current_flat_sequence_limit_weak R h2 nu m V hV EF P QF hFLimit.
have hGWeak:=@current_flat_sequence_limit_weak R h2 nu m V hV EG Q QG hGLimit.
rewrite -hSame in hGWeak.
exact:(@current_weak_sequence_limit_unique R h2 nu m V hV P QF QG hFWeak hGWeak).
Qed.
End CurrentSupportSmoothComparisonImages.
