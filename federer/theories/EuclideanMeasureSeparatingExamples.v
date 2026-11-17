(** Federer (1969), 2.10.6, p. 174:
    the two original Chapter 3 examples separate
    the second comparison group. Reuse their complete
    constructions and actual mass computations. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure ProjectionMeasure IntegralGeometricMeasure
  ProjectionBeta IntegralGeometricInfinity RectifiableGeometricBasicComparisons IntegralGeometricInfinityComparison
  CircularDiscLimitSealed CircularDiscExample BinaryCantorSetSealed EuclideanCantorProduct BinaryCantorSquareExample
  MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_6_caratheodory_gross_separation]:
    the first unbounded-ratio witness cited in
    Federer 2.10.6, p. 174, using
    the actual original 3.3.19 compact
    circular-disc set, pp. 302–306.
    Its Caratheodory measure is two, while
    Gross and every integral-geometric exponent vanish.
    The original construction and all mass identities
    are reused; no abstract hypothetical example is assumed. *)
Theorem federer_2_10_6_caratheodory_gross_separation (R : realType) :
  exists A : set (inner_metric_space (@euclidean_inner_productP R 2)), compact A /\
    @caratheodory_projection_measure R 2 1 A=(2:R)%:E /\
    @gross_measure R 2 1 A= 0 /\
    forall t : \bar R, 1<=t ->@integral_geometric_measure R 2 1 (leqnSn 1) t A= 0.
Proof.
pose A := @CircularDiscLimit.value R.
have [hN [hCompact [hMass [hQ [hQ1 [hPure [hCone [hProjection [hGross hDensity]]]]]]]]] :=
  @federer_3_3_19 R.
exists A; split; first exact hCompact.
split.
- rewrite -(@convex_integral_geometric_infinity R 2 1 (leqnSn 1) A).
  have h := hQ +oo (leey 1).
  by rewrite projection_beta_infinity mul1e in h.
split; first exact hGross.
move=> t hT.
apply/eqP; rewrite eq_le
  (@measure_nonnegative R _ _ (@integral_geometric_measure_is_measure R 2 1 (leqnSn 1) t hT) A) andbT.
have h := le_trans (@integral_geometric_below_infinity R 2 1 (leqnSn 1) t A hT)
  (@integral_geometric_infinity_gross_bound R 2 1 (leqnSn 1) A).
by rewrite hGross in h.
Qed.

(** Source for [federer_2_10_6_gross_integral_separation]:
    the second unbounded-ratio witness cited in
    Federer 2.10.6, p. 174, from
    the actual critical binary Cantor square
    of 3.3.20, pp. 306–309.
    Gross mass is 3/sqrt(5), Hausdorff
    length is sqrt(2), and every
    integral-geometric exponent vanishes. The original
    finite-mass nullity theorem applies because the
    independently computed Gross mass bounds I_infinity.
    Its strict positive mass and Hausdorff comparison
    are proved from these exact values. *)
Theorem federer_2_10_6_gross_integral_separation (R : realType) :
  exists E : set (inner_metric_space (@euclidean_inner_productP R 2)), compact E /\
    @gross_measure R 2 1 E=(3/Num.sqrt (5:R))%R%:E /\
    @hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)] 1 E=
      (Num.sqrt (2:R))%:E /\
    0<@gross_measure R 2 1 E /\
    @gross_measure R 2 1 E<
      @hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)] 1 E /\
    forall t : \bar R, 1<=t ->@integral_geometric_measure R 2 1 (leqnSn 1) t E= 0.
Proof.
have hPositive : (0<(1/2:R))%R by lra.
have hLessOne : ((1/2:R)<1)%R by lra.
have hDegree : (0<=2*(1/2:R))%R by lra.
pose A := @BinaryPowerCantor.value R (1/2:R) hPositive hLessOne.
pose E := euclidean_cantor_product A A.
have [hCompact [hLower [hUpper [hPure [hPureReal [hNoFinite [hInfinite hCritical]]]]]]] :=
  @federer_3_3_20 R (1/2:R) hPositive hLessOne hDegree (lexx _).
have [hHausdorff hGross] := hCritical erefl.
have hGuard : (erefl true)=(leqnSn 1) := Prop_irrelevance _ _.
rewrite hGuard in hNoFinite.
have hSqrt5 : (0<Num.sqrt (5:R))%R by rewrite sqrtr_gt0 ltr0n.
have hGrossPositive : (0<3/Num.sqrt (5:R))%R by rewrite divr_gt0 // ltr0n.
have hSqrtProduct : (0<=Num.sqrt (2:R)*Num.sqrt (5:R))%R.
  exact: mulr_ge0 (sqrtr_ge0 _) (sqrtr_ge0 _).
have hSquare : ((3:R)^+2<(Num.sqrt (2:R)*Num.sqrt (5:R))^+2)%R.
  rewrite exprMn !sqr_sqrtr ?(ler0n R) //; lra.
have hRoot : (3<Num.sqrt (2:R)*Num.sqrt (5:R))%R.
  by move: hSquare; rewrite (ltr_sqr (ler0n R 3) hSqrtProduct).
have hStrict : (3/Num.sqrt (5:R)<Num.sqrt (2:R))%R.
  by rewrite ltr_pdivrMr.
have hFinite : @integral_geometric_measure R 2 1 (leqnSn 1) +oo E< +oo.
  have h := @integral_geometric_infinity_gross_bound R 2 1 (leqnSn 1) E.
  rewrite hGross in h; exact: le_lt_trans h (ltry _).
have hZero := hNoFinite E (@subset_refl _ E) hFinite.
exists E; split; first exact hCompact.
split; first exact hGross.
split; first exact hHausdorff.
split; first by rewrite hGross lte_fin.
split; first by rewrite hGross hHausdorff lte_fin.
move=> t hT.
apply/eqP; rewrite eq_le
  (@measure_nonnegative R _ _ (@integral_geometric_measure_is_measure R 2 1 (leqnSn 1) t hT) E) andbT.
have h := @integral_geometric_below_infinity R 2 1 (leqnSn 1) t E hT.
by rewrite hZero in h.
Qed.

(** Source for [federer_2_10_6_unbounded_ratios]:
    direct failure of uniform bounded ratios in
    the second group C, G and I_t
    in Federer 2.10.6, p. 174.
    For every proposed finite factor the original
    circular-disc set defeats C<=cG and
    C<=cI_t, while the original critical
    Cantor square defeats G<=cI_t.
    The witnesses are actual compact Euclidean sets;
    every exponent through infinity remains. *)
Theorem federer_2_10_6_unbounded_ratios (R : realType) (t : \bar R) (c : R) :
  1<=t ->
  (exists A : set (inner_metric_space (@euclidean_inner_productP R 2)), compact A /\
    c%:E*@gross_measure R 2 1 A<@caratheodory_projection_measure R 2 1 A /\
    c%:E*@integral_geometric_measure R 2 1 (leqnSn 1) t A<@caratheodory_projection_measure R 2 1 A) /\
  (exists E : set (inner_metric_space (@euclidean_inner_productP R 2)), compact E /\
    c%:E*@integral_geometric_measure R 2 1 (leqnSn 1) t E<@gross_measure R 2 1 E).
Proof.
move=> hT; split.
- have [A [hA [hC [hG hI]]]] := @federer_2_10_6_caratheodory_gross_separation R.
  exists A; split=> //; rewrite hC hG (hI t hT) !mule0 lte_fin; split; exact: ltr0n.
- have [E [hE [hG [hH [hPositive [hStrict hI]]]]]] := @federer_2_10_6_gross_integral_separation R.
  exists E; split=> //; by rewrite (hI t hT) mule0.
Qed.
