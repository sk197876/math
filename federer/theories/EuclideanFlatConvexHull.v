(** Federer (1969), 4.1.16, p. 374: every original
    flat current on R^n is flat on the precise convex
    hull C of its support, and F_K(T)=F_C(T) for every
    compact K containing C. Use the preceding retraction
    localisation and exact Lipschitz flat estimate. Empty
    support is treated before selecting a nearest map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  InnerConvex ConvexHull SmoothCompactSet CurrentSpaces CurrentSupportGeometry
  CurrentSupportExtensionality NormalCurrentsUP NormalCurrentLinear
  FlatCurrentsUP FlatCurrentFinite CurrentFlatCompactMonotone CurrentFlatNorm
  LipschitzUP LipschitzBasic RetractionUP CurrentLipschitzCompactImage
  CurrentFlatLipschitzPushforwardSealed SmoothCompactSetExtensionality
  CurrentFlatLipschitzSupportAgreement CurrentFlatLipschitzRetraction
  CurrentFlatIdentityPushforward EuclideanConvexNearestMapUP
  EuclideanConvexNearestMapLaws EuclideanConvexNearestMapOwnNorm
  EuclideanCompactNearestMap EuclideanFlatConvexHullIndex
  FlatCurrentNonexpandingPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EuclideanFlatConvexHull.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Local Notation U := (fun _:X=>True).
Variable hU : forall x,U x->norm_domain_interior N U x.
Variable T : @current_space R h2 n U hU m.
Hypothesis hFlat : @is_flat_current R h2 n m U hU T.
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation C := (@current_flat_convex_hull_index R h2 n m hU T hFlat).
Local Notation hConvex := (@current_flat_convex_hull_index_convex R h2 n m hU T hFlat).
Local Notation hSupport := (@current_flat_convex_hull_index_contains_support R h2 n m hU T hFlat).
Local Notation flatK K := (@is_flat_current_supported_in R h2 n m U hU K).
Local Notation F K := (@current_flat_norm R h2 n m U hU K).

(** Source for [euclidean_flat_convex_hull_empty_current]:
    the empty hull branch of Federer 4.1.16, p. 374.
    Its contained original support is empty, hence T=0
    by the earlier current support theorem. *)
Local Lemma euclidean_flat_convex_hull_empty_current :
  ~ (smooth_compact_carrier C !=set0) -> T=0.
Proof.
move=> hEmpty.
apply: (@current_empty_support_iff_zero R h2 n m U hU T).1.
move=> x hx; exfalso; apply: hEmpty; exists x; exact: hSupport x hx.
Qed.

(** Source for [euclidean_flat_current_convex_hull]:
    T belongs to F_(m,C)(R^n) for C=conv(spt T),
    Federer 4.1.16, p. 374. The original flat-union
    premise suffices, without finite mass, normality, nonzero
    T or a positive-degree restriction. *)
Theorem euclidean_flat_current_convex_hull : flatK C T.
Proof.
case: (pselect (smooth_compact_carrier C !=set0)) => [hNonempty|hEmpty].
- pose P := @euclidean_compact_convex_nearest_map R n
    (smooth_compact_carrier C) (smooth_compact_is_compact C) hNonempty hConvex.
  have hP := @euclidean_compact_convex_nearest_map_laws R n
    (smooth_compact_carrier C) (smooth_compact_is_compact C) hNonempty hConvex.
  have [K hK] := hFlat.
  pose L := smooth_compact_union K C.
  have hKL : smooth_compact_carrier K `<=` smooth_compact_carrier L.
    by move=> x hx; left.
  have hCL : smooth_compact_carrier C `<=` smooth_compact_carrier L.
    by move=> x hx; right.
  have hTL := @flat_current_compact_monotone R h2 n m U hU K L hKL T hK.
  have hRetraction := @euclidean_convex_nearest_map_compact_retraction R n
    (smooth_compact_carrier C) P hP hConvex (smooth_compact_carrier L) hCL.
  have hLip := @euclidean_convex_nearest_map_own_norm_lipschitz R n
    (smooth_compact_carrier C) P hP hConvex (smooth_compact_carrier L).
  exact: (@current_flat_retraction_localisation R h2 n m U hU
    L C P hRetraction hLip T).1 (conj hTL hSupport).
- have hZero : T=0 := euclidean_flat_convex_hull_empty_current hEmpty.
  have hNormalZero : @normal_currents_supported_in R h2 n U hU m C 0.
    split; first exact: (@normal_current_zero R h2 n U hU m).
    exact: (@current_support_zero_subset R h2 n m U hU C).
  have hZeroFlat := @supported_normal_current_is_flat R h2 n m U hU C 0 hNormalZero.
  have hMembership : flatK C T=flatK C 0 := congr1 (flatK C) hZero.
  by rewrite hMembership.
Qed.

(** Source for [euclidean_flat_current_convex_hull_norm]:
    F_K(T)=F_C(T) for every compact K containing the
    original C=conv(spt T), Federer 4.1.16, p. 374.
    Compact monotonicity gives one inequality; the nearest
    retraction, support coincidence and exact 4.1.14 estimate
    give the other. Infinite mass and degree zero remain. *)
Theorem euclidean_flat_current_convex_hull_norm
    (K : smooth_compact_set hN U)
    (hCK : smooth_compact_carrier C `<=` smooth_compact_carrier K) :
  F K T=F C T.
Proof.
case: (pselect (smooth_compact_carrier C !=set0)) => [hNonempty|hEmpty].
- pose P := @euclidean_compact_convex_nearest_map R n
    (smooth_compact_carrier C) (smooth_compact_is_compact C) hNonempty hConvex.
  have hP := @euclidean_compact_convex_nearest_map_laws R n
    (smooth_compact_carrier C) (smooth_compact_is_compact C) hNonempty hConvex.
  have hPImage : forall x,U x->U (P x) by move=> x _.
  have hPLocal : @is_locally_metric_lipschitz R XT XT U P.
    apply: metric_lipschitz_is_local.
    exact: (@euclidean_convex_nearest_map_own_norm_lipschitz R n
      (smooth_compact_carrier C) P hP hConvex U).
  have hIdImage : forall x,U x->U x by move=> x hx.
  have hIdLocal : @is_locally_metric_lipschitz R XT XT U (fun x=>x).
    apply: metric_lipschitz_is_local.
    exists 1; split; first exact: ltr01.
    split; first exact: ler01.
    by move=> x y _ _; rewrite mul1r.
  have hAgree : forall x,support x->P x=x.
    move=> x hx.
    have hxC : smooth_compact_carrier C x.
      exact: (@current_flat_convex_hull_index_contains_support R h2 n m hU
        T hFlat x hx).
    exact: (@euclidean_convex_nearest_map_fixed R n
      (smooth_compact_carrier C) P hP x hxC).
  have hSame := @current_flat_lipschitz_support_agreement R h2 n n m
    U U hU hU P (fun x=>x) hPImage hIdImage hPLocal hIdLocal T hFlat hAgree.
  have hIdentity := @current_flat_lipschitz_identity_pushforward R h2 n m
    U hU hIdImage hIdLocal T hFlat.
  have hPCurrent : @CurrentFlatLipschitzPushforward.value R h2 n n m U U hU hU
      P hPImage hPLocal T hFlat=T := eq_trans hSame hIdentity.
  have hImageIndex : @current_lipschitz_compact_image R n n U U hU
      P hPImage hPLocal K=C.
    apply: smooth_compact_set_extensionality.
    rewrite current_lipschitz_compact_image_carrier.
    exact: (@euclidean_convex_nearest_map_image R n
      (smooth_compact_carrier C) P hP (smooth_compact_carrier K) hCK).
  have hTK := @flat_current_compact_monotone R h2 n m U hU C K hCK T
    euclidean_flat_current_convex_hull.
  have hBound : @is_metric_lipschitz_bound R XT XT
      (smooth_compact_carrier K) P 1.
    exact: (metric_lipschitz_bound_restrict (fun _ _=>Logic.I)
      (@euclidean_convex_nearest_map_own_norm_bound R n
        (smooth_compact_carrier C) P hP hConvex)).
  have hBackward := @current_flat_nonexpanding_pushforward_bound R h2 n n m
    U U hU hU P hPImage hPLocal K hBound T hFlat hTK.
  rewrite hImageIndex hPCurrent in hBackward.
  apply/eqP; rewrite eq_le; apply/andP; split.
  * exact: (@current_flat_compact_monotone R h2 n m U hU C K hCK T).
  * exact: hBackward.
- have hZero : T=0 := euclidean_flat_convex_hull_empty_current hEmpty.
  have hKZero : F K T=0%E.
    have hEqual := congr1 (F K) hZero.
    by rewrite current_flat_norm_zero in hEqual.
  have hCZero : F C T=0%E.
    have hEqual := congr1 (F C) hZero.
    by rewrite current_flat_norm_zero in hEqual.
  exact: eq_trans hKZero (esym hCZero).
Qed.

(** Source for [federer_4_1_16]: the full concluding
    in-book assertion of Federer 4.1.16, p. 374.
    The only omitted sentence is its outside-source pointer
    to positive reach; neither current assertion is omitted. *)
Theorem federer_4_1_16 :
  flatK C T /\
  forall K:smooth_compact_set hN U,
    smooth_compact_carrier C `<=` smooth_compact_carrier K -> F K T=F C T.
Proof.
split; first exact: euclidean_flat_current_convex_hull.
exact: euclidean_flat_current_convex_hull_norm.
Qed.
End EuclideanFlatConvexHull.
