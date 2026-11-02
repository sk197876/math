(** Federer (1969), 3.2.6, pp. 245–246:
    absolute continuity on every compact interval supplies
    global continuity and locally finite variation, as used
    with 2.10.13 in the proof. These are metric facts. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricCurveAbsoluteContinuityUP MetricCurveAbsoluteContinuityBasic
  MetricAbsoluteContinuityFiniteVariation CurveVariationUP CurveArcLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_locally_absolutely_continuous_curve]: the
    first hypothesis of Federer 3.2.6, p. 245,
    specified through the existing finite-family absolute
    continuity laws on each nondegenerate compact interval. *)
Definition is_locally_absolutely_continuous_curve (R:realType) (Y:metricType R) (f:R->Y):Prop:=
  forall a b:R,a<b -> is_absolutely_continuous_metric_curve f a b.

(** Source for [locally_absolutely_continuous_curve_continuous]:
    continuity used in the appeal to 2.10.13 in the
    proof of Federer 3.2.6, pp. 245–246. A compact
    interval around each point gives a genuine neighbourhood. *)
Theorem locally_absolutely_continuous_curve_continuous (R:realType) (Y:metricType R) (f:R->Y):
  is_locally_absolutely_continuous_curve f -> continuous (f:real_line_metric R->Y).
Proof.
move=>hAC x W hW.
have [e he hBall]:=(metricType_numDomainType.nbhs_mdistP (f x) W).1 hW.
have he2:0<e/2 by rewrite divr_gt0 // ltr0n.
have hInterval:x-1<x+1 by lra.
have [d [hd hControl]]:=metric_absolute_continuity_increment_control (hAC _ _ hInterval) he2.
pose r:=Num.min d 1.
have hr:0<r by rewrite /r lt_min hd ltr01.
have hrd:r<=d by rewrite /r ge_min lexx.
have hr1:r<=1 by rewrite /r ge_min lexx orbT.
change (nbhs (x:real_line_metric R) [set y|W (f y)]).
apply:(filterS _ (nbhsx_ballx (x:real_line_metric R) r hr))=>y hy.
have hNear:`|y-x|<r.
  by move:hy; rewrite /ball /= distrC.
have hSmall:`|y-x|<=d:=le_trans (ltW hNear) hrd.
have hUnit:`|y-x|<=1:=le_trans (ltW hNear) hr1.
have hPlus:y-x<=`|y-x| :=ler_norm (y-x).
have hMinus:x-y<=`|y-x| by rewrite distrC; exact:ler_norm.
have hax:x-1<=x by lra.
have hxb:x<=x+1 by lra.
have hay:x-1<=y by lra.
have hyb:y<=x+1 by lra.
have hDist:=hControl x y hax hxb hay hyb hSmall.
apply:hBall; apply:(le_lt_trans hDist); by rewrite ltr_pdivrMr ?ltr0n // mulr_natr ltrDl.
Qed.

(** Source for [locally_absolutely_continuous_curve_finite_variation]:
    the locally finite variation needed for Federer 3.2.6,
    pp. 245–246, by the finite-family argument of 2.9.20
    extended to metric curves in 2.10.13. Equal endpoints
    of the source interval are retained. *)
Theorem locally_absolutely_continuous_curve_finite_variation (R:realType) (Y:metricType R) (f:R->Y):
  is_locally_absolutely_continuous_curve f -> curve_locally_finite_variation f.
Proof.
move=>hAC a b hab; case:(ltP a b)=>hStrict.
- exact (metric_absolute_continuity_finite_variation hab (hAC a b hStrict)).
- have he:a=b by apply/eqP; rewrite eq_le hab hStrict.
  by rewrite -he curve_variation_self ltry.
Qed.
