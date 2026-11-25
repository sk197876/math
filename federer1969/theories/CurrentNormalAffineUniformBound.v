(** Federer (1969), 4.1.14, p. 370: apply 4.1.13 to
    smooth approximations of a fixed normal current. The uniform
    difference and original K derivative cap bound the two
    variation integrals. The target compact E need contain only
    the actual support-segment hull. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanHomOperator CurrentMapDifferential
  CurrentDomain CurrentSpaces CurrentBoundary CurrentBoundarySupport
  CurrentIntegrationCriterion NormalCurrentsUP CurrentMassSealed
  SmoothCompactSet CurrentCompactPushforwardAlgebra CurrentAffineSegmentHull
  CurrentFlatAffineImages CurrentFlatCompactMonotone CurrentFlatNorm
  CurrentAffineConstantWeightBound SummableRealFunctionUP
  MeasureIntegralBounds NormalisedCurrentSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalAffineUniformBound.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U : set X) (V : set Y).
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hV : forall y, V y -> norm_domain_interior NY V y.
Variables f g : X -> Y.
Hypothesis hFImage : forall x, U x -> V (f x).
Hypothesis hGImage : forall x, U x -> V (g x).
Hypothesis hf : norm_class_all_orders hNX hNY U f.
Hypothesis hg : norm_class_all_orders hNX hNY U g.
Variable K : smooth_compact_set hNX U.
Variable E : smooth_compact_set hNY V.
Variable delta : R.
Hypothesis hDelta : 0<=delta.
Hypothesis hDisplacement : forall x, smooth_compact_carrier K x ->
  NY (g x-f x)<=delta.
Local Notation UT := (current_domain R n U).
Local Notation displacement := (fun x : UT => NY (g (set_val x)-f (set_val x))).
Local Notation Op := (@euclidean_operator_norm R n nu).
Local Notation rho := (fun x : UT => Num.max
  (Op (@current_map_differential R n nu U f (set_val x)))
  (Op (@current_map_differential R n nu U g (set_val x)))).

(** Source for [current_normal_affine_uniform_zero]: the
    degree-zero instance of the first Cauchy comparison in
    Federer 4.1.14, p. 370. There is no derivative factor
    or negative-degree boundary term. *)
Theorem current_normal_affine_uniform_zero
    (T : @current_space R h2 n U hU 0%N)
    (hNormal : @is_normal_current R h2 n U hU 0%N T)
    (hSupport : @current_support R h2 n U hU 0%N T `<=`
      smooth_compact_carrier K)
    (hHull : @current_affine_segment_hull R h2 n nu 0%N U hU f g T `<=`
      smooth_compact_carrier E) (mass : R)
    (hMass : @CurrentMass.value R h2 n 0%N U hU T=mass%:E) :
  (@current_flat_norm R h2 nu 0%N V hV E
    (@current_compact_map_pushforward R h2 n nu U V hU hV
      g hGImage hg 0%N T hNormal.2-
     @current_compact_map_pushforward R h2 n nu U V hU hV
      f hFImage hf 0%N T hNormal.2) <= (delta*mass)%R%:E)%E.
Proof.
have hC : @current_affine_segment_hull R h2 n nu 0%N U hU f g T `<=` V.
  move=> y hy; exact: smooth_compact_in_domain E y (hHull y hy).
pose C := @current_affine_image_compact R h2 n nu 0%N
  U V hU f g hf hg T hNormal hC.
have hMonotone := @current_flat_compact_monotone R h2 nu 0%N V hV
  C E hHull
  (@current_compact_map_pushforward R h2 n nu U V hU hV
    g hGImage hg 0%N T hNormal.2-
   @current_compact_map_pushforward R h2 n nu U V hU hV
    f hFImage hf 0%N T hNormal.2).
have hAffine := @federer_4_1_13_zero R h2 n nu U V hU hV
  f g hFImage hGImage hf hg T hNormal hC.
have hIntegral := @current_original_variation_bounded_integral R h2 n 0%N
  U hU T hNormal.1.1 mass delta displacement hMass
  (fun x hx => @hDisplacement (set_val x) (hSupport _ hx)).
exact: le_trans hMonotone (le_trans hAffine hIntegral).
Qed.

Variable c : R.
Hypothesis hc : 0<=c.
Hypothesis hDerivative : forall x, smooth_compact_carrier K x ->
  Num.max (Op (@current_map_differential R n nu U f x))
    (Op (@current_map_differential R n nu U g x))<=c.
(** Source for [affine_uniform_point_weight]: the original two
    integrands in the comparison of Federer 4.1.14, p. 370,
    have the stated constant cap on the original K. *)
Local Lemma affine_uniform_point_weight k (x : UT) :
  smooth_compact_carrier K (set_val x) ->
  displacement x*(rho x)^+k<=delta*c^+k.
Proof.
move=> hx; apply: nonnegative_affine_weight_cap.
- exact: real_seminorm_nonnegative hNY.1 _.
- have hNonnegative : 0<=Op (@current_map_differential R n nu U f (set_val x)) :=
    real_seminorm_nonnegative (@euclidean_operator_norm_is_norm R n nu).1 _.
  have hMaximum : Op (@current_map_differential R n nu U f (set_val x))<=rho x.
    by rewrite le_max lexx orTb.
  exact: le_trans hNonnegative hMaximum.
- exact: hDelta.
- exact: hc.
- exact: @hDisplacement _ hx.
- exact: @hDerivative _ hx.
Qed.

(** Source for [current_normal_affine_uniform_positive]: the
    positive-degree Cauchy comparison in Federer 4.1.14,
    p. 370: delta times c^m M(T)+c^(m-1) M(boundary T)
    bounds the flat difference. The two caps are required only
    on K; the exact support-segment hull lies in E. *)
Theorem current_normal_affine_uniform_positive j
    (T : @current_space R h2 n U hU j.+1)
    (hNormal : @is_normal_current R h2 n U hU j.+1 T)
    (hSupport : @current_support R h2 n U hU j.+1 T `<=`
      smooth_compact_carrier K)
    (hHull : @current_affine_segment_hull R h2 n nu j.+1 U hU f g T `<=`
      smooth_compact_carrier E) (mass boundaryMass : R)
    (hMass : @CurrentMass.value R h2 n j.+1 U hU T=mass%:E)
    (hBoundaryMass : @CurrentMass.value R h2 n j U hU
      (@current_boundary R h2 n j U hU T)=boundaryMass%:E) :
  (@current_flat_norm R h2 nu j.+1 V hV E
    (@current_compact_map_pushforward R h2 n nu U V hU hV
      g hGImage hg j.+1 T hNormal.2-
     @current_compact_map_pushforward R h2 n nu U V hU hV
      f hFImage hf j.+1 T hNormal.2) <=
    (delta*(c^+j.+1*mass+c^+j*boundaryMass))%R%:E)%E.
Proof.
have hC : @current_affine_segment_hull R h2 n nu j.+1 U hU f g T `<=` V.
  move=> y hy; exact: smooth_compact_in_domain E y (hHull y hy).
pose C := @current_affine_image_compact R h2 n nu j.+1
  U V hU f g hf hg T hNormal hC.
have hMonotone := @current_flat_compact_monotone R h2 nu j.+1 V hV
  C E hHull
  (@current_compact_map_pushforward R h2 n nu U V hU hV
    g hGImage hg j.+1 T hNormal.2-
   @current_compact_map_pushforward R h2 n nu U V hU hV
    f hFImage hf j.+1 T hNormal.2).
have hAffine := @federer_4_1_13_positive R h2 n nu j U V hU hV
  f g hFImage hGImage hf hg T hNormal hC.
have hIntegral := @current_original_variation_bounded_integral R h2 n j.+1
  U hU T hNormal.1.1 mass (delta*c^+j.+1)
  (fun x : UT => displacement x*(rho x)^+j.+1) hMass
  (fun x hx => affine_uniform_point_weight j.+1 (hSupport _ hx)).
pose B := @current_boundary R h2 n j U hU T.
have hBoundarySupport : @current_support R h2 n U hU j B `<=`
    smooth_compact_carrier K.
  move=> x hx; apply: hSupport.
  exact: (@current_boundary_support_subset R h2 n j U hU T x hx).
have hBoundaryIntegral := @current_original_variation_bounded_integral R h2 n j
  U hU B hNormal.1.2 boundaryMass (delta*c^+j)
  (fun x : UT => displacement x*(rho x)^+j) hBoundaryMass
  (fun x hx => affine_uniform_point_weight j (hBoundarySupport _ hx)).
have hSum := leeD hIntegral hBoundaryIntegral.
rewrite -EFinD in hSum.
have hValue : delta*c^+j.+1*mass+delta*c^+j*boundaryMass=
    delta*(c^+j.+1*mass+c^+j*boundaryMass) by ring.
rewrite hValue in hSum.
exact: le_trans hMonotone (le_trans hAffine hSum).
Qed.
End CurrentNormalAffineUniformBound.
