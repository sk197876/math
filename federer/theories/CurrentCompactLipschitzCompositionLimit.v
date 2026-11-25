(** Federer (1969), 4.1.14, p. 371: composition
    follows from compatible original smooth approximations.
    Compare b_i#(a_i#T) with b_i#(f#T) in one
    target flat seminorm. The original common derivative
    cap controls the first error; the second is the
    defining approximation of g#(f#T). *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  LipschitzUP MetricLocalLipschitzComposition OpenLocalLipschitzCompact
  SmoothCompactSet SmoothCompactNeighbourhoods CurrentSpaces CurrentSupportGeometry
  CurrentProperSupport CurrentCompactMapProper CurrentPushforwardSealed
  CurrentPushforwardSupport CurrentPushforwardDataIndependence
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  SmoothFormPullbackComposition FlatCurrentsUP FlatCurrentFinite
  CurrentFlatCompactMonotone CurrentLipschitzCompactImage
  CurrentCompactLipschitzPushforwardUP CurrentSmoothApproximationUP
  CurrentSmoothApproximationCompactImage CurrentSmoothPushforwardFlatBound
  CurrentLipschitzFlatCoefficient CurrentMapDifferential EuclideanHomOperator
  CurrentFlatNorm CurrentFlatSequenceLimitUP CurrentFlatSequenceLimits
  CurrentFlatSequenceComparison CurrentLipschitzImageOriginalApproximation
  CurrentWeakSequenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactLipschitzCompositionLimit.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu omega m : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R omega).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R omega)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R omega)).
Variables (U : set X) (V : set Y) (W : set Z).
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hV : forall y, V y -> norm_domain_interior NY V y.
Hypothesis hW : forall z, W z -> norm_domain_interior NZ W z.
Variables (f : X -> Y) (g : Y -> Z).
Hypothesis hFImage : forall x, U x -> V (f x).
Hypothesis hGImage : forall y, V y -> W (g y).
Hypothesis hFLocal : @is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal : @is_locally_metric_lipschitz R
  (real_norm_metric_space hNY) (real_norm_metric_space hNZ) V g.
Local Notation gf := (fun x => g (f x)).
Let hGFImage : forall x, U x -> W (gf x) :=
  fun x hx => @hGImage (f x) (@hFImage x hx).
Let hGFLocal := @metric_local_lipschitz_composition R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  (real_norm_metric_space hNZ) U V f g hFImage hFLocal hGLocal.
Variable K : smooth_compact_set hNX U.
Variable E : smooth_compact_set hNY V.
Hypothesis hInside : forall x, smooth_compact_carrier K x ->
  norm_domain_interior NY (smooth_compact_carrier E) (f x).
Variable T : @current_space R h2 n U hU m.
Hypothesis hFlat : @is_flat_current_supported_in R h2 n m U hU K T.
Variable Q : @current_space R h2 nu V hV m.
Hypothesis hQ : @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
  f hFImage hFLocal K T Q.
Variables P S : @current_space R h2 omega W hW m.
Hypothesis hP : @is_current_compact_lipschitz_image R h2 n omega m U W hU hW
  gf hGFImage hGFLocal K T P.
Hypothesis hS : @is_current_compact_lipschitz_image R h2 nu omega m V W hV hW
  g hGImage hGLocal E Q S.
Variables (a : nat -> X -> Y) (b : nat -> Y -> Z).
Hypothesis hA : @is_current_smooth_approximation R n nu U V K f a.
Hypothesis hB : @is_current_smooth_approximation R nu omega V W E g b.
Hypothesis hAB : @is_current_smooth_approximation R n omega U W K gf
  (fun i x => b i (a i x)).
Local Notation fK := (@current_lipschitz_compact_image R n nu U V hU
  f hFImage hFLocal K).
Local Notation hTCompact := (@flat_supported_current_compact R h2 n m U hU K T hFlat).
Local Notation Ai := (fun i => @current_compact_map_pushforward R h2 n nu U V hU hV
  (a i) (current_smooth_approximation_image hA i)
  (current_smooth_approximation_class hA i) m T hTCompact).
Local Notation hAiCompact := (fun i => @current_compact_map_image_compact R h2 n nu
  U V hU hV (a i) (current_smooth_approximation_image hA i)
  (current_smooth_approximation_class hA i) m T hTCompact).

(** Source for [current_compact_lipschitz_composition_limit]:
    compatible approximations prove the original composition
    assertion of Federer 4.1.14, p. 371. This supporting
    limit statement imposes no normality or finite mass on T.
    The final existence theorem supplies the compatible families
    internally, so they are not additional original hypotheses. *)
Theorem current_compact_lipschitz_composition_limit : P=S.
Proof.
have hFKInE : smooth_compact_carrier fK `<=` smooth_compact_carrier E.
  move=> y [x hx <-].
  exact: (@norm_domain_interior_member R Y NY hNY
    (smooth_compact_carrier E) (f x) (@hInside x hx)).
have hQE := @flat_current_compact_monotone R h2 nu m V hV fK E hFKInE Q hQ.1.
pose hQCompact := @flat_supported_current_compact R h2 nu m V hV E Q hQE.
pose Bi := fun i => @current_compact_map_pushforward R h2 nu omega V W hV hW
  (b i) (current_smooth_approximation_image hB i)
  (current_smooth_approximation_class hB i) m Q hQCompact.
pose Ci := fun i => @current_compact_map_pushforward R h2 n omega U W hU hW
  (fun x => b i (a i x)) (current_smooth_approximation_image hAB i)
  (current_smooth_approximation_class hAB i) m T hTCompact.
pose Di := fun i => @current_compact_map_pushforward R h2 nu omega V W hV hW
  (b i) (current_smooth_approximation_image hB i)
  (current_smooth_approximation_class hB i) m (Ai i) (hAiCompact i).
have hComposition i : Ci i=Di i.
  have hOld := @current_compact_map_images_compose R h2 n nu omega U V W hU hV hW
    (a i) (b i) (current_smooth_approximation_image hA i)
    (current_smooth_approximation_image hB i)
    (current_smooth_approximation_class hA i)
    (current_smooth_approximation_class hB i) m T hTCompact (hAiCompact i).
  apply: (eq_trans _ hOld).
  exact: (@current_pushforward_data_independent R h2 n omega m U W hU hW T
    (fun x => b i (a i x)) _ _ _ _ _ _).
pose gE := @current_lipschitz_compact_image R nu omega V W hV
  g hGImage hGLocal E.
have [F hF] := @smooth_compact_neighbourhood_exists R Z NZ hNZ omega
  (@coordinate_basis R omega) (@coordinate_basisP R omega) W hW gE.
have hGInside : forall y, smooth_compact_carrier E y ->
    norm_domain_interior NZ (smooth_compact_carrier F) (g y).
  move=> y hy; apply: hF; by exists y.
have hGFInside : forall x, smooth_compact_carrier K x ->
    norm_domain_interior NZ (smooth_compact_carrier F) (gf x).
  move=> x hx; exact: @hGInside (f x)
    (@norm_domain_interior_member R Y NY hNY
      (smooth_compact_carrier E) (f x) (@hInside x hx)).
have hALimit := @current_lipschitz_image_original_approximation_flat R h2 n nu m
  U V hU hV f hFImage hFLocal K T hFlat Q hQ a hA E hInside.
have hBLimit := @current_lipschitz_image_original_approximation_flat R h2 nu omega m
  V W hV hW g hGImage hGLocal E Q hQE S hS b hB F hGInside.
have hCLimit := @current_lipschitz_image_original_approximation_flat R h2 n omega m
  U W hU hW gf hGFImage hGFLocal K T hFlat P hP
  (fun i x => b i (a i x)) hAB F hGFInside.
have hFClass := @norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY
  U f hU hFLocal.
have hGClass := @norm_open_local_lipschitz_class_zero R Y Z NY NZ hNY hNZ
  V g hV hGLocal.
have [NA hNA] := @current_smooth_approximation_eventual_compact_image R n nu
  U V K f a hA hFImage hFClass E hInside.
have [NB hNB] := @current_smooth_approximation_eventual_compact_image R nu omega
  V W E g b hB hGImage hGClass F hGInside.
have [c [hc hCap]] := current_smooth_approximation_bound hB.
pose D := current_lipschitz_flat_coefficient m c.
have hD : 0<=D := @current_lipschitz_flat_coefficient_nonnegative R m c hc.
have hSupportT := @flat_current_supported_support R h2 n m U hU K T hFlat.
have hSupportQ := @flat_current_supported_support R h2 nu m V hV E Q hQE.
have hSupportA : forall i, (NA<=i)%N ->
    @current_support R h2 nu V hV m (Ai i) `<=` smooth_compact_carrier E.
  move=> i hi y hy.
  have [x hx <-] := @current_pushforward_support_image R h2 n nu m U V hU hV
    T (a i) (current_smooth_approximation_image hA i)
    (current_smooth_approximation_class hA i) _ y hy.
  exact: hNA i hi x (hSupportT x hx).
have hClose : forall eps:R, 0<eps -> exists N:nat,
    forall i:nat, (N<=i)%N ->
      (@current_flat_norm R h2 omega m W hW F (Bi i-Ci i)<eps%:E)%E.
  move=> eps hEps.
  have hOne : 0<D+1.
    have hAtLeast : 1<=D+1 by rewrite lerDr.
    exact: lt_le_trans ltr01 hAtLeast.
  pose delta := eps/(D+1).
  have hDelta : 0<delta by rewrite /delta divr_gt0.
  have [N0 hN0] := hALimit delta hDelta.
  exists (maxn (maxn NA NB) N0)=> i hi.
  have hiA : (NA<=i)%N := leq_trans (leq_trans (leq_maxl NA NB)
    (leq_maxl (maxn NA NB) N0)) hi.
  have hiB : (NB<=i)%N := leq_trans (leq_trans (leq_maxr NA NB)
    (leq_maxl (maxn NA NB) N0)) hi.
  have hi0 : (N0<=i)%N := leq_trans (leq_maxr (maxn NA NB) N0) hi.
  have hApprox := hN0 i hi0.
  have hFinite : (@current_flat_norm R h2 nu m V hV E (Q-Ai i)< +oo)%E :=
    lt_trans hApprox (ltry delta).
  have hSupportError : @current_support R h2 nu V hV m (Q-Ai i)
      `<=` smooth_compact_carrier E.
    have h := @current_support_linear_subset R h2 nu m V hV E (-1)
      (Ai i) Q (hSupportA i hiA) hSupportQ.
    by rewrite scaleN1r addrC in h.
  pose hErrorCompact := @current_support_compact_bound R h2 nu m V hV E
    (Q-Ai i) hSupportError.
  have hBound := @current_smooth_pushforward_flat_bound R h2 nu omega m V W hV hW
    (b i) (current_smooth_approximation_image hB i)
    (current_smooth_approximation_class hB i) E F (hNB i hiB) c hc (hCap i)
    (Q-Ai i) hErrorCompact hSupportError hFinite.
  have hSubtract := @current_compact_map_pushforward_subtract R h2 nu omega V W hV hW
    (b i) (current_smooth_approximation_image hB i)
    (current_smooth_approximation_class hB i) m Q (Ai i)
    hQCompact (hAiCompact i) hErrorCompact.
  rewrite hSubtract in hBound.
  change (is_true ((@current_flat_norm R h2 omega m W hW F (Bi i-Di i) <=
    D%:E * @current_flat_norm R h2 nu m V hV E (Q-Ai i))%E)) in hBound.
  rewrite -(hComposition i) in hBound.
  have hDE : (0<=D%:E)%E by rewrite lee_fin.
  have hScaled := lee_wpmul2l hDE (ltW hApprox).
  have hTotal := le_trans hBound hScaled.
  rewrite -EFinM in hTotal.
  apply: (le_lt_trans hTotal); rewrite lte_fin.
  have hEnd : (D+1)*delta=eps by rewrite /delta mulrC divfK ?gt_eqF.
  have hStrict : D*delta<(D+1)*delta.
    by rewrite (ltr_pM2r hDelta) ltrDl ltr01.
  by rewrite hEnd in hStrict.
have hCLimitS := @current_flat_sequence_limit_compare R h2 omega m W hW F
  Bi Ci S hBLimit hClose.
exact: (@current_weak_sequence_limit_unique R h2 omega m W hW Ci P S
  (@current_flat_sequence_limit_weak R h2 omega m W hW F Ci P hCLimit)
  (@current_flat_sequence_limit_weak R h2 omega m W hW F Ci S hCLimitS)).
Qed.
End CurrentCompactLipschitzCompositionLimit.
