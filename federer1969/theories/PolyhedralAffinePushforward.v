(** Federer (1969), 4.1.23, pp. 379–380:
    arbitrary affine images preserve integral and real
    polyhedral chains at their original compact indices.
    The full hull of each generator is
    mapped into the target compact; neither compact
    is assumed convex. The affine map may
    be singular and the ambient dimensions independent. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient TopologicalGroupUP
  AffineMaps AffineConvexHullImage RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  SmoothCompactSet CurrentSpaces CurrentSupportGeometry CurrentProperSupport
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentCompactCurrentArithmetic CurrentCompactSmoothAlgebra
  CurrentPushforwardDataIndependence CurrentOpenRestriction
  CurrentNormalApproximationNeighbourhoodComparison
  CurrentFlatLipschitzTargetNeighbourhood CurrentJoinAffineSourcePushforward
  OrientedSimplexCurrentSealed OrientedSimplexCurrentAffine
  OrientedSimplexNormal OrientedSimplexHullSupport OpenSimplexGeometry
  PolyhedralCurrentGenerators PolyhedralCurrentAlgebra PolyhedralNormal
  GeneratedAdditiveSubgroupUP GeneratedLinearSubspaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralAffineImage.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu m : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation FullX := (fun _ : X => True).
Local Notation FullY := (fun _ : Y => True).
Local Notation hFullX := (fun (x:X) (_:True) => @norm_full_domain_interior R X NX x).
Local Notation hFullY := (fun (y:Y) (_:True) => @norm_full_domain_interior R Y NY y).
Variables (U : set X) (V : set Y).
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hV : forall y, V y -> norm_domain_interior NY V y.
Variable f : X -> Y.
Hypothesis hAffine : is_affine_map f.
Hypothesis hImage : forall x, U x -> V (f x).
Local Notation hf := (@euclidean_affine_map_smooth R n nu U hU f hAffine).
Local Notation hfFull := (@euclidean_affine_map_smooth R n nu FullX hFullX f hAffine).
Local Notation CU := (@current_space R h2 n U hU m).
Local Notation CV := (@current_space R h2 nu V hV m).
Local Notation Compact T := (@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU m T)).
Local Notation Push := (fun (S : CU) (hS : Compact S) =>
  @current_compact_map_pushforward R h2 n nu U V hU hV f hImage hf m S hS).

(** Source for [open_oriented_simplex_current_affine]:
    affine transfer of the actual simplex on
    its original open domain in Federer 4.1.23,
    pp. 379–380. Recover the ambient simplex
    using the preceding support-neighbourhood and target
    restriction laws, then apply 4.1.11, p. 366. *)
Theorem open_oriented_simplex_current_affine (v : 'I_(m.+1) -> X)
    (hHull : @polyhedral_simplex_vertex_hull R n m v `<=` U)
    (hCompact : Compact (@open_oriented_simplex_current R h2 n m U hU v)) :
  Push _ hCompact=@open_oriented_simplex_current R h2 nu m V hV (fun i => f (v i)).
Proof.
pose S := @OrientedSimplexCurrent.value R h2 n m v.
pose hNormal := @oriented_simplex_current_normal R h2 n m v.
pose imageFull := fun (x:X) (_:FullX x) => Logic.I.
pose imageU := fun (x:X) (_:U x) => Logic.I.
pose includeU := fun (x:X) (_:U x) => Logic.I.
pose includeV := fun (y:Y) (_:V y) => Logic.I.
have hSupport : @current_support R h2 n FullX hFullX m S `<=` U.
  exact: subset_trans (@oriented_simplex_current_hull_support R h2 n m v) hHull.
have hNeighbourhood := @current_normal_neighbourhood_compact_image R h2 n nu m
  U FullX FullY hU hFullX hFullY includeU f imageFull hfFull imageU hf
  S hNormal hSupport hCompact.
have hAffineImage : @current_compact_map_pushforward R h2 n nu
    FullX FullY hFullX hFullY f imageFull hfFull m S hNormal.2=
      @OrientedSimplexCurrent.value R h2 nu m (fun i => f (v i)).
  have hOld := @oriented_simplex_current_affine R h2 n nu f hAffine m v hNormal.2.
  have hSame : @current_compact_map_pushforward R h2 n nu
      FullX FullY hFullX hFullY f imageFull hfFull m S hNormal.2=
      @current_join_affine_current R h2 n nu f hAffine m S hNormal.2.
    exact: current_pushforward_data_independent.
  exact: eq_trans hSame hOld.
have hFullImage : @current_compact_map_pushforward R h2 n nu U FullY hU hFullY
    f imageU hf m (@open_oriented_simplex_current R h2 n m U hU v) hCompact=
      @OrientedSimplexCurrent.value R h2 nu m (fun i => f (v i)).
  exact: eq_trans (esym hNeighbourhood) hAffineImage.
have hTarget := @current_compact_map_target_neighbourhood_restriction R h2 n nu m
  U V FullY hU hV hFullY f hImage imageU includeV hf hf
  (@open_oriented_simplex_current R h2 n m U hU v) hCompact.
apply: (eq_trans (esym hTarget)).
change (@current_open_restriction R h2 nu m V FullY hV hFullY includeV
  (@current_compact_map_pushforward R h2 n nu U FullY hU hFullY
    f imageU hf m (@open_oriented_simplex_current R h2 n m U hU v) hCompact)=
  @current_open_restriction R h2 nu m V FullY hV hFullY includeV
    (@OrientedSimplexCurrent.value R h2 nu m (fun i=>f (v i)))).
by rewrite hFullImage.
Qed.

Variables (K : smooth_compact_set hNX U) (L : smooth_compact_set hNY V).
Hypothesis hKL : forall x, smooth_compact_carrier K x -> smooth_compact_carrier L (f x).

(** Source for [polyhedral_affine_generator_hull]: affine
    transfer preserves the full generator-hull condition
    of 4.1.22 in Federer 4.1.23,
    pp. 379–380, even when K or
    L is not convex. *)
Lemma polyhedral_affine_generator_hull (v : 'I_(m.+1) -> X) :
  @polyhedral_simplex_vertex_hull R n m v `<=` smooth_compact_carrier K ->
  @polyhedral_simplex_vertex_hull R nu m (fun i => f (v i)) `<=`
    smooth_compact_carrier L.
Proof.
move=> hHull.
have hVertices : [set y | exists i, f (v i)=y]=
    f @` [set x | exists i, v i=x].
  apply/seteqP; split.
  - move=> y [i <-]; exists (v i); first by exists i.
    reflexivity.
  - move=> y [x [i <-] <-]; by exists i.
rewrite /polyhedral_simplex_vertex_hull hVertices
  -(@affine_convex_hull_image R X Y f _ hAffine).
move=> y [x hx <-]; exact: (@hKL x (@hHull x hx)).
Qed.

(** Source for [integral_polyhedral_current_affine_pushforward]:
    the original affine transfer of integral
    polyhedral chains used by Federer 4.1.23,
    pp. 379–380. Every compactness witness is
    allowed; the full original K-image condition
    supplies each target generator, with no convexity
    assumption on either index. *)
Theorem integral_polyhedral_current_affine_pushforward (T : CU)
    (hPoly : @integral_polyhedral_current_class R h2 n m U hU K T)
    (hCompact : Compact T) :
  @integral_polyhedral_current_class R h2 nu m V hV L (Push T hCompact).
Proof.
pose Good := fun S : CU => exists hS : Compact S,
  @integral_polyhedral_current_class R h2 nu m V hV L (Push S hS).
have hZero : Good 0.
  exists (@current_compact_zero_support R h2 n m U hU).
  rewrite (@current_compact_map_pushforward_zero R h2 n nu U V hU hV
    f hImage hf m 0 _ (erefl 0)).
  exact: integral_polyhedral_current_zero.
have hAdd (S Q : CU) : Good S -> Good Q -> Good (S+Q).
  move=> [hS hPS] [hQ hPQ].
  have hSum : Compact (S+Q).
    have h := @current_compact_linear_support R h2 n m U hU 1 S Q hS hQ.
    by rewrite scale1r in h.
  exists hSum; rewrite (@current_compact_map_pushforward_add R h2 n nu
    U V hU hV f hImage hf m S Q hS hQ hSum).
  exact: integral_polyhedral_current_add hPS hPQ.
have hNeg (S : CU) : Good S -> Good (-S).
  move=> [hS hPS].
  have hNegative : Compact (-S).
    have h := @current_compact_scaled_support R h2 n m U hU S (-1) hS.
    by rewrite scaleN1r in h.
  exists hNegative.
  have hNegativeScale : Compact ((-1:R)*:S) by rewrite scaleN1r.
  have hScale := @current_compact_map_scaled_image R h2 n nu U V hU hV
    f hImage hf m S (-1) hS hNegativeScale.
  have hSame := @current_compact_map_pushforward_congruence R h2 n nu U V
    hU hV f hImage hf m ((-1:R)*:S) (-S) hNegativeScale hNegative
    (scaleN1r S).
  rewrite hSame scaleN1r in hScale; rewrite hScale.
  exact: integral_polyhedral_current_negate hPS.
have hGroup : is_subgroup (fun S Q : CU => S+Q) (fun S => -S) 0 Good.
  constructor; [exact: hZero|exact: hAdd|exact: hNeg].
have hGenerator : @polyhedral_simplex_generators R h2 n m U hU K `<=` Good.
  move=> S [v [hHull <-]].
  pose hS := @current_support_compact_bound R h2 n m U hU K
    (@open_oriented_simplex_current R h2 n m U hU v)
    (subset_trans (@open_simplex_current_hull_support R h2 n U hU m v) hHull).
  exists hS; rewrite (open_oriented_simplex_current_affine
    (subset_trans hHull (smooth_compact_in_domain K)) hS).
  exact: integral_polyhedral_current_generator (polyhedral_affine_generator_hull hHull).
have [hT hPT] := generated_additive_subgroup_least
  (@integral_polyhedral_current_class_laws R h2 n m U hU K) hGroup hGenerator hPoly.
have hSame := @current_compact_map_pushforward_congruence R h2 n nu U V hU hV
  f hImage hf m T T hT hCompact (erefl T).
by rewrite -hSame.
Qed.

(** Source for [real_polyhedral_current_affine_pushforward]:
    affine images preserve the original real
    polyhedral span in Federer 4.1.23,
    pp. 379–380. Real coefficients, singular
    maps, empty indices and every degree remain. *)
Theorem real_polyhedral_current_affine_pushforward (T : CU)
    (hPoly : @polyhedral_current_subspace R h2 n m U hU K T)
    (hCompact : Compact T) :
  @polyhedral_current_subspace R h2 nu m V hV L (Push T hCompact).
Proof.
pose Good := fun S : CU => exists hS : Compact S,
  @polyhedral_current_subspace R h2 nu m V hV L (Push S hS).
have hZero : Good 0.
  exists (@current_compact_zero_support R h2 n m U hU).
  rewrite (@current_compact_map_pushforward_zero R h2 n nu U V hU hV
    f hImage hf m 0 _ (erefl 0)); exact: subspace_zero.
have hLinear c (S Q : CU) : Good S -> Good Q -> Good (c*:S+Q).
  move=> [hS hPS] [hQ hPQ].
  pose hSum := @current_compact_linear_support R h2 n m U hU c S Q hS hQ.
  exists hSum; rewrite (@current_compact_map_pushforward_linear R h2 n nu
    U V hU hV f hImage hf m c S Q hS hQ hSum).
  have hScaled := @subspace_scale R CV
    (@polyhedral_current_subspace R h2 nu m V hV L) c (Push S hS) hPS.
  exact: (@subspace_add R CV (@polyhedral_current_subspace R h2 nu m V hV L)
    (c*:Push S hS) (Push Q hQ) hScaled hPQ).
have hAdd : forall S Q : CU, Good S -> Good Q -> Good (S+Q).
  move=> S Q hS hQ; have h := hLinear 1 S Q hS hQ; by rewrite scale1r in h.
have hScale : forall c (S : CU), Good S -> Good (c*:S).
  move=> c S hS; have h := hLinear c S 0 hS hZero; by rewrite addr0 in h.
pose GoodSpace := @Subspace R CU Good hZero hAdd hScale.
have hContained : @integral_polyhedral_current_class R h2 n m U hU K `<=` GoodSpace.
  move=> S hS.
  pose hCompactS := @current_support_compact_bound R h2 n m U hU K S
    (@integral_polyhedral_current_normal_support R h2 n m U hU K S hS).2.
  exists hCompactS; apply: integral_polyhedral_current_is_polyhedral.
  exact: integral_polyhedral_current_affine_pushforward hS hCompactS.
have [hT hPT] := generated_linear_subspace_least
  (@polyhedral_current_subspace_laws R h2 n m U hU K) (W:=GoodSpace) hContained hPoly.
have hSame := @current_compact_map_pushforward_congruence R h2 n nu U V hU hV
  f hImage hf m T T hT hCompact (erefl T).
by rewrite -hSame.
Qed.
End PolyhedralAffineImage.
