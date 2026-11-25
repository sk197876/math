(** Federer (1969), 4.1.14, p. 370: for a normal current,
    every original smooth approximation has a Cauchy image
    sequence in each prescribed F_E. Two such families approach
    one another. This is the first construction step, before
    the completion argument and extension to arbitrary flat
    currents. All derivative caps remain restricted to K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormClassOneUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothCompactSet
  CurrentSpaces CurrentBoundary CurrentIntegrationCriterion NormalCurrentsUP
  NormalCurrentBoundary CompactRepresentedCurrentMass CurrentMassSealed
  CurrentMassBasic CurrentCompactPushforwardAlgebra CurrentAffineSegmentHull
  CurrentFlatNorm CurrentFlatSequenceLimitUP CurrentSmoothApproximationUP
  CurrentSmoothApproximationSegments CurrentNormalAffineUniformBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalSmoothApproximationCauchy.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (Z : set X) (V : set Y).
Hypothesis hZ : forall x, Z x -> norm_domain_interior NX Z x.
Hypothesis hV : forall y, V y -> norm_domain_interior NY V y.
Variable K : smooth_compact_set hNX Z.
Variable f : X -> Y.
Hypothesis hImage : forall x, Z x -> V (f x).
Hypothesis hf : norm_class_zero NX NY Z f.
Variables g q : nat -> X -> Y.
Hypothesis hG : @is_current_smooth_approximation R n nu Z V K f g.
Hypothesis hQ : @is_current_smooth_approximation R n nu Z V K f q.

(** Source for [current_normal_smooth_approximations_compare]:
    the comparison implicit in Federer's normal-current
    construction, 4.1.14, p. 370. Any two allowed smooth
    families have arbitrarily small F_E difference, independently
    in their two eventual indices. No smoothness of f, global
    derivative cap or convexity of E or V is imposed. *)
Theorem current_normal_smooth_approximations_compare m
    (T : @current_space R h2 n Z hZ m)
    (hNormal : @is_normal_current R h2 n Z hZ m T)
    (hSupport : @current_support R h2 n Z hZ m T `<=`
      smooth_compact_carrier K)
    (E : smooth_compact_set hNY V)
    (hInterior : forall x, smooth_compact_carrier K x ->
      norm_domain_interior NY (smooth_compact_carrier E) (f x)) :
  forall epsilon : R, 0<epsilon -> exists N : nat, forall i j : nat,
    (N<=i)%N -> (N<=j)%N ->
    (@current_flat_norm R h2 nu m V hV E
      (@current_compact_map_pushforward R h2 n nu Z V hZ hV
        (q j) (current_smooth_approximation_image hQ j)
        (current_smooth_approximation_class hQ j) m T hNormal.2-
       @current_compact_map_pushforward R h2 n nu Z V hZ hV
        (g i) (current_smooth_approximation_image hG i)
        (current_smooth_approximation_class hG i) m T hNormal.2)
      < epsilon%:E)%E.
Proof.
have [Ns hNs] := @current_smooth_approximation_segments R n nu Z V K
  f g q hG hQ hImage hf E hInterior.
have [c [hcOne hCap]] := @current_smooth_approximation_common_derivative_cap
  R n nu Z V K f g q hG hQ.
have hc : 0<=c by lra.
case: m T hNormal hSupport => [|d] T hNormal hSupport epsilon he.
- have hFinite := @compact_represented_current_finite_mass R h2 n 0%N
    Z hZ T hNormal.1.1 hNormal.2.
  have [mass [hMassNonnegative hMass]] := @current_finite_mass_value
    R h2 n 0%N Z hZ T hFinite.
  pose delta := epsilon/(mass+1).
  have hDen : 0<mass+1 by lra.
  have hDelta : 0<delta by rewrite /delta divr_gt0.
  have [Nd hNd] := @current_smooth_approximation_difference R n nu Z V K
    f g q hG hQ delta hDelta.
  exists (maxn Ns Nd) => i j hi hj.
  have hiS := leq_trans (leq_maxl Ns Nd) hi.
  have hjS := leq_trans (leq_maxl Ns Nd) hj.
  have hiD := leq_trans (leq_maxr Ns Nd) hi.
  have hjD := leq_trans (leq_maxr Ns Nd) hj.
  have hDisplacement x : smooth_compact_carrier K x ->
      NY (q j x-g i x)<=delta.
    move=> hx; exact: ltW (hNd i j hiD hjD x hx).
  have hHull : @current_affine_segment_hull R h2 n nu 0%N
      Z hZ (g i) (q j) T `<=` smooth_compact_carrier E.
    move=> y [t [x [ht [hx <-]]]].
    have /andP [ht0 ht1] := ht.
    exact: @hNs i j hiS hjS x t (hSupport x hx) ht0 ht1.
  have hBound := @current_normal_affine_uniform_zero R h2 n nu Z V hZ hV
    (g i) (q j) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_image hQ j)
    (current_smooth_approximation_class hG i)
    (current_smooth_approximation_class hQ j) K E delta
    hDisplacement T hNormal hSupport hHull mass hMass.
  apply: le_lt_trans hBound _; rewrite lte_fin.
  have hEnd : delta*(mass+1)=epsilon by rewrite /delta divfK ?gt_eqF.
  have hStrict : delta*mass<delta*(mass+1).
    rewrite (ltr_pM2l hDelta); lra.
  by rewrite hEnd in hStrict.
- have hFinite := @compact_represented_current_finite_mass R h2 n d.+1
    Z hZ T hNormal.1.1 hNormal.2.
  have [mass [hMassNonnegative hMass]] := @current_finite_mass_value
    R h2 n d.+1 Z hZ T hFinite.
  pose B := @current_boundary R h2 n d Z hZ T.
  have hBoundaryNormal := @normal_current_boundary R h2 n Z hZ d T hNormal.
  have hBoundaryFinite := @compact_represented_current_finite_mass R h2 n d
    Z hZ B hNormal.1.2 hBoundaryNormal.2.
  have [boundaryMass [hBoundaryMassNonnegative hBoundaryMass]] :=
    @current_finite_mass_value R h2 n d Z hZ B hBoundaryFinite.
  pose bound := c^+d.+1*mass+c^+d*boundaryMass.
  have hBoundNonnegative : 0<=bound.
    apply: addr_ge0; apply: mulr_ge0; try exact: exprn_ge0 hc.
    + exact: hMassNonnegative.
    + exact: hBoundaryMassNonnegative.
  pose delta := epsilon/(bound+1).
  have hDen : 0<bound+1 by lra.
  have hDelta : 0<delta by rewrite /delta divr_gt0.
  have [Nd hNd] := @current_smooth_approximation_difference R n nu Z V K
    f g q hG hQ delta hDelta.
  exists (maxn Ns Nd) => i j hi hj.
  have hiS := leq_trans (leq_maxl Ns Nd) hi.
  have hjS := leq_trans (leq_maxl Ns Nd) hj.
  have hiD := leq_trans (leq_maxr Ns Nd) hi.
  have hjD := leq_trans (leq_maxr Ns Nd) hj.
  have hDisplacement x : smooth_compact_carrier K x ->
      NY (q j x-g i x)<=delta.
    move=> hx; exact: ltW (hNd i j hiD hjD x hx).
  have hHull : @current_affine_segment_hull R h2 n nu d.+1
      Z hZ (g i) (q j) T `<=` smooth_compact_carrier E.
    move=> y [t [x [ht [hx <-]]]].
    have /andP [ht0 ht1] := ht.
    exact: @hNs i j hiS hjS x t (hSupport x hx) ht0 ht1.
  have hBound := @current_normal_affine_uniform_positive R h2 n nu Z V hZ hV
    (g i) (q j) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_image hQ j)
    (current_smooth_approximation_class hG i)
    (current_smooth_approximation_class hQ j) K E delta (ltW hDelta)
    hDisplacement c hc (fun x hx => hCap i j x hx)
    d T hNormal hSupport hHull mass boundaryMass hMass hBoundaryMass.
  apply: le_lt_trans hBound _; rewrite lte_fin.
  change (is_true (delta*bound<epsilon)).
  have hEnd : delta*(bound+1)=epsilon by rewrite /delta divfK ?gt_eqF.
  have hStrict : delta*bound<delta*(bound+1).
    rewrite (ltr_pM2l hDelta); lra.
  by rewrite hEnd in hStrict.
Qed.

End CurrentNormalSmoothApproximationCauchy.

Section SingleNormalSmoothApproximationCauchy.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (Z : set X) (V : set Y).
Hypothesis hZ : forall x, Z x -> norm_domain_interior NX Z x.
Hypothesis hV : forall y, V y -> norm_domain_interior NY V y.
Variable K : smooth_compact_set hNX Z.
Variable f : X -> Y.
Hypothesis hImage : forall x, Z x -> V (f x).
Hypothesis hf : norm_class_zero NX NY Z f.
Variable g : nat -> X -> Y.
Hypothesis hG : @is_current_smooth_approximation R n nu Z V K f g.

(** Source for [current_normal_smooth_approximation_cauchy]: the
    original normal-current image sequence is Cauchy in F_E,
    Federer 4.1.14, p. 370. The proof is the preceding two-
    family comparison applied to one family twice. *)
Theorem current_normal_smooth_approximation_cauchy m
    (T : @current_space R h2 n Z hZ m)
    (hNormal : @is_normal_current R h2 n Z hZ m T)
    (hSupport : @current_support R h2 n Z hZ m T `<=`
      smooth_compact_carrier K)
    (E : smooth_compact_set hNY V)
    (hInterior : forall x, smooth_compact_carrier K x ->
      norm_domain_interior NY (smooth_compact_carrier E) (f x)) :
  @is_current_flat_cauchy_sequence R h2 nu m V hV E
    (fun i => @current_compact_map_pushforward R h2 n nu Z V hZ hV
      (g i) (current_smooth_approximation_image hG i)
      (current_smooth_approximation_class hG i) m T hNormal.2).
Proof.
move=> epsilon he.
have [N hN] := @current_normal_smooth_approximations_compare R h2 n nu
  Z V hZ hV K f hImage hf g g hG hG m T hNormal hSupport E hInterior epsilon he.
exists N => i j hi hj; exact: hN j i hj hi.
Qed.
End SingleNormalSmoothApproximationCauchy.
