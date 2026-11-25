(** Federer (1969), 3.2.46, p. 281: concatenate
    actual Lipschitz representatives. The joined curve has
    exactly the sum of their genuine length integrals; the
    possible missing derivative at the junction is null. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground LipschitzUP MetricCurveConcatenation
  MetricCurveConcatenationLaws LipschitzCurveAbsoluteContinuity
  RiemannianTensorUP RiemannianCurveCost RiemannianGlobalCurveAdmissible
  RiemannianCurveSubinterval RiemannianCurveIntegralSplitting
  RiemannianCurveIntervalCost RiemannianCurveTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_global_curves_concatenation]:
    the actual concatenation used for the triangle inequality
    in Federer 3.2.46, p. 281. Its admissibility and exact
    length sum are proved from the original curve integrals,
    not supplied as path-length axioms. Zero durations and
    zero Lipschitz bounds remain. *)
Theorem riemannian_global_curves_concatenation (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (C D : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n))
    a b c d L M :
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT C L ->
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT D M ->
  (forall t, A (C t)) -> (forall t, A (D t)) ->
  a <= b -> c <= d -> C b = D c ->
  is_riemannian_admissible_curve A (C a) (D d)
    (metric_curve_concatenation C D b c) a (b+d-c) /\
  riemannian_curve_cost g (metric_curve_concatenation C D b c) a (b+d-c) =
    (riemannian_curve_cost g C a b + riemannian_curve_cost g D c d)%E.
Proof.
move=> hC hD hCA hDA hab hcd hJoin.
pose E := metric_curve_concatenation C D b c.
pose e := b+d-c.
have hbe : b <= e by rewrite /e; lra.
have hae : a <= e := le_trans hab hbe.
have hE := metric_curve_concatenation_lipschitz hC hD hJoin.
have hEA : forall t, A (E t) := @metric_curve_concatenation_image R
  (R_n R n) C D A b c hCA hDA.
have hStart : E a = C a := @metric_curve_concatenation_left R
  (R_n R n) C D b c a hab.
have hEnd : E e = D d.
  rewrite /E (@metric_curve_concatenation_right R (R_n R n) C D b c e hJoin hbe).
  have he : e-b+c=d by rewrite /e; ring.
  by rewrite he.
have hAd := riemannian_global_curve_admissible hE hEA hae.
change (is_riemannian_admissible_curve A (E a) (E e) E a e) in hAd.
rewrite hStart hEnd in hAd; split; first exact hAd.
have hLeftAd := riemannian_admissible_curve_subinterval hAd (lexx a) hab hbe.
have hRightAd := riemannian_admissible_curve_subinterval hAd hab hbe (lexx e).
have hCAd := riemannian_global_curve_admissible hC hCA hab.
have hDAd := riemannian_global_curve_admissible hD hDA hcd.
have hLeftCost : riemannian_curve_cost g E a b = riemannian_curve_cost g C a b.
  apply: (riemannian_curve_interval_cost_agreement hg hLeftAd hCAd
    (metric_lipschitz_curve_locally_absolute_continuous hC)).
  move=> t /andP [hat htb]; exact: (@metric_curve_concatenation_left R (R_n R n) C D b c t htb).
pose F := fun t : real_line_metric R => D (t+(c-b)).
have hF := metric_curve_parameter_translation_bound (c-b) hD.
have hFA : forall t, A (F t) by move=> t; exact: hDA.
have hFAd := riemannian_global_curve_admissible hF hFA hbe.
have hRightCost : riemannian_curve_cost g E b e = riemannian_curve_cost g F b e.
  apply: (riemannian_curve_interval_cost_agreement hg hRightAd hFAd
    (metric_lipschitz_curve_locally_absolute_continuous hF)).
  move=> t /andP [hbt hte].
  rewrite /E (@metric_curve_concatenation_right R (R_n R n) C D b c t hJoin hbt) /F.
  have he : t-b+c=t+(c-b) by ring.
  by rewrite he.
have hFCost : riemannian_curve_cost g F b e = riemannian_curve_cost g D c d.
  have h := @riemannian_translated_curve_cost R n A g hg (D c) (D d) D c d (c-b) hDAd.
  have hFirst : c-(c-b)=b by ring.
  have hLast : d-(c-b)=e by rewrite /e; ring.
  by rewrite hFirst hLast in h.
have hCut : a <= b <= e by rewrite hab hbe.
have hSplit := riemannian_curve_cost_split hg hAd hCut.
by rewrite hLeftCost hRightCost hFCost in hSplit.
Qed.
