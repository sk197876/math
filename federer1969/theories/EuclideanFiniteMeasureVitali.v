(** Federer (1969), 3.2.26(2), p. 261: the
    finite restricted Hausdorff measure on a compact chart
    satisfies the standing hypotheses of the centered-ball
    Vitali theorem. Finite-dimensional directional limitation
    supplies the required disjoint selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanMetricSeparability EuclideanDirectionalLimitation DirectionalLimitationUP
  CoveringFamilyUP CoveringRelationUP CenteredBallRelations CenteredBallVitali
  MetricClosedBalls MeasureUP MeasureBasic BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_finite_measure_centered_vitali]: the
    application of 2.8.15 in 3.2.26(2), p. 261,
    through the full centered-ball theorem 2.8.18,
    p. 152. Global finiteness supplies finite mass
    on every bounded set; no ambient Hausdorff local
    finiteness or extra doubling condition is assumed. *)
Lemma euclidean_finite_measure_centered_vitali (R:realType) n
    (mu:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R):
  is_measure mu ->is_borel_regular_measure mu ->mu setT < +oo ->
  is_vitali_relation mu (@centered_closed_ball_relation R
    (inner_metric_space (@euclidean_inner_productP R n))).
Proof.
move=>hMu hRegular hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose V:=@centered_closed_ball_relation R X.
have hContext:is_covering_theory_context (covering_relation_image V setT) mu.
  constructor.
  - exact hMu.
  - move=>B [x [_ [r [hr ->]]]]; exact:metric_closed_ball_closed.
  - move=>U hU; exact:(@borel_regular_open_measurable R X mu hRegular U hU).
  - move=>A _; apply:le_lt_trans _ hFinite.
    exact:(@measure_mono R (Choice.clone X _) mu hMu A setT (subsetT A)).
have hThird:(0<((1:R)/3)%R)%R by rewrite divr_gt0 // ltr0n.
have hThirdRange:(0<((1:R)/3)%R<=1/3)%R by apply/andP; split; last exact:lexx.
have [zeta hDirectional]:=euclidean_directional_limitation n hThirdRange.
pose C:set (set X):=[set setT].
have hCover:(\bigcup_(A in C) A)=setT.
  apply/seteqP; split=>x hx; first exact I.
  exists setT; first reflexivity; exact I.
have hLimited A:C A ->exists (xi: \bar R) (eta:R) (k:nat),is_directionally_limited_at A xi eta k.
  move=>hA; change (A=setT) in hA; rewrite hA.
  by exists +oo,(1/3)%R,zeta.
exact:(@federer_2_8_18 R X mu C hContext (@euclidean_metric_separable R n)
  (countable1 setT) hCover hLimited).
Qed.
