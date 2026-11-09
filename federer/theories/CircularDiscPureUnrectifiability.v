(** Federer (1969), 3.3.19, p. 304:
    the actual original circular-disc limit is
    purely (H1,1) unrectifiable. Use the
    proved original restriction identity and 3.2.26. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularTrigonometrySealed CircularHalfPeriodLower
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscExactMass CircularDiscRestrictedMeasures
  HausdorffMeasure ProjectionBeta RectifiableSetUP RectifiableFiniteHausdorffMass RectifiableGeometricMeasureEquality
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [circular_disc_purely_unrectifiable]:
    the final sentence of 3.3.19, p. 304:
    A is purely (H1,1) unrectifiable.
    Any actual rectifiable subset has finite H1
    mass and Q1=H1 by 3.2.26; the original
    restricted normalized identity and beta_1<1
    force that mass to vanish. No measurability
    of the original test subset is assumed. *)
Theorem circular_disc_purely_unrectifiable (R:realType)
    (H:nat->{fset (inner_metric_space (@euclidean_inner_productP R 2))})
    (A:set (inner_metric_space (@euclidean_inner_productP R 2))):
  is_circular_disc_tree H ->is_circular_disc_limit H A ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R 2)) 1) 1 A.
Proof.
move=>hH hA.
pose E:=inner_metric_space (@euclidean_inner_productP R 2).
pose mu:=@hausdorff_measure R [the metricType R of E] 1.
pose beta:=@projection_beta R 2 1 (leqnSn 1) 1.
have hMu:is_measure mu:=@hausdorff_measure_is_measure R [the metricType R of E] 1.
split=>//;move=>[F [hFA [hRect hPositive]]].
have hMeasureRect:=@rectifiable_hausdorff_measure_rectifiable R 1 2 F hRect.
have hRectQ:=((@federer_3_2_26 R 1 2 (leqnSn 1) F hMeasureRect).2.2.2 (1: \bar R)%E (lexx _)).1.
have hRestriction:=@circular_disc_restricted_normalized_measure_agreement R H hH A hA F.
have hIntersection:A `&` F=F.
  apply/seteqP;split.
  - by move=>x [_ hx].
  - move=>x hx;split=>//;exact:hFA x hx.
rewrite hIntersection hRectQ in hRestriction.
have hBetaPositive:0<beta:=@projection_beta_positive R 2 1 (leqnSn 1) 1 (lexx _).
have hPi:=@circular_half_period_at_least_three R.
have hNormalization:=@circular_disc_first_beta_normalization R.
have hScaled:=ler_wpM2l (ltW hBetaPositive) hPi.
rewrite hNormalization in hScaled.
have hBetaLess:beta<1 by nra.
have hFinite:mu F \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hMu F));exact:hMeasureRect.2.
have hValue:mu F=(fine (mu F))%:E by rewrite fineK.
have hRestrictionValue:(beta*fine (mu F))%:E=(fine (mu F))%:E.
  change ((beta%:E*mu F=mu F)%E) in hRestriction.
  by rewrite hValue -EFinM in hRestriction.
have hReal:beta*fine (mu F)=fine (mu F):=EFin_inj hRestrictionValue.
have hPositiveTyped:(0<mu F)%E:=hPositive.
have hPositiveReal:0<fine (mu F) by move:hPositiveTyped;rewrite hValue lte_fin.
have hContradiction:beta*fine (mu F)<1*fine (mu F) by rewrite ltr_pM2r.
rewrite mul1r hReal in hContradiction.
by move:hContradiction;rewrite ltxx.
Qed.
