(** Federer(1969),3.2.44,p.278:
    actual open unit balls have genuinely rectifiable
    boundaries and positive finite closure volume. These
    whole-theorem regressions retain positive dimensions
    and the separate positive-volume line case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanBallVolume
  EuclideanUnitBallProjection EuclideanOpenConvexBoundary EuclideanBoundedClosure MetricBoundedClosureLaws
  RectifiableBoundaryIsoperimetric RectifiableSetUP HausdorffMeasure RealPower
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_unit_ball_isoperimetric_example]:
    the whole rectifiable-boundary conclusion of Federer
    3.2.44,p.278, on the actual open unit ball in every
    ambient dimension at least two. Earlier3.2.35 proves
    genuine boundary rectifiability. Positive actual ball
    volume ensures the displayed lower bound is substantive. *)
Example rectifiable_unit_ball_isoperimetric_example (R:realType) k:
  exists S:set (inner_metric_space (@euclidean_inner_productP R k.+2)),
    is_m_rectifiable k.+1 (closure S `\` interior S) /\
    (0<@euclidean_lebesgue_measure R k.+2 (closure S) < +oo)%E /\
    (((k.+2)%:R*real_power (euclidean_unit_ball_volume R k.+2) ((k.+2)%:R)^-1*
      real_power (fine (@euclidean_lebesgue_measure R k.+2 (closure S)))
        ((k.+1)%:R/(k.+2)%:R))%:E<=
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+2))
        k.+1 (closure S `\` interior S))%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R k.+2).
pose mu:=@euclidean_lebesgue_measure R k.+2.
pose S:set X:=[set x|inner_norm (@euclidean_inner_productP R k.+2) x<1].
have [hNe [hOpen [hConvex hBound]]]:=euclidean_unit_ball_convex_bounded R k.+2.
have hRect:=@euclidean_open_convex_boundary_rectifiable R k.+2 S hNe hOpen hConvex hBound.
rewrite subn1 in hRect.
have hCompact:compact (closure S):=euclidean_bounded_closure_compact hBound.
have hFinite:(mu (closure S) < +oo)%E:=euclidean_compact_finite hCompact.
have hPositive:(0<mu S)%E.
  rewrite /mu /S (euclidean_unit_ball_volumeE R k.+2).1 lte_fin.
  exact:(euclidean_unit_ball_volumeE R k.+2).2.
have hClosurePositive:(0<mu (closure S))%E:=lt_le_trans hPositive
  (@measure_mono R X mu (euclidean_lebesgue_is_measure R k.+2) _ _ (@subset_closure X S)).
have hFull:=@federer_3_2_44 R k S hFinite hRect.
exists S; split; first exact hRect.
split; first by apply/andP.
exact hFull.
Qed.

(** Source for [rectifiable_line_ball_isoperimetric_example]:
    the positive-volume dimension-one case of Federer
    3.2.44,p.278. The actual open unit line ball has a
    genuinely zero-rectifiable boundary; its Hausdorff
    counting mass is at least two. Its positive closure
    volume and boundary rectifiability are proved. *)
Example rectifiable_line_ball_isoperimetric_example (R:realType):
  exists S:set (inner_metric_space (@euclidean_inner_productP R 1)),
    is_m_rectifiable 0 (closure S `\` interior S) /\
    (0<@euclidean_lebesgue_measure R 1 (closure S) < +oo)%E /\
    ((2:R)%:E<=@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 1)) 0
      (closure S `\` interior S))%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose mu:=@euclidean_lebesgue_measure R 1.
pose S:set X:=[set x|inner_norm (@euclidean_inner_productP R 1) x<1].
have [hNe [hOpen [hConvex hBound]]]:=euclidean_unit_ball_convex_bounded R 1.
have hRect:=@euclidean_open_convex_boundary_rectifiable R 1 S hNe hOpen hConvex hBound.
rewrite subn1 in hRect.
have hCompact:compact (closure S):=euclidean_bounded_closure_compact hBound.
have hFinite:(mu (closure S) < +oo)%E:=euclidean_compact_finite hCompact.
have hPositive:(0<mu S)%E.
  rewrite /mu /S (euclidean_unit_ball_volumeE R 1).1 lte_fin.
  exact:(euclidean_unit_ball_volumeE R 1).2.
have hClosurePositive:(0<mu (closure S))%E:=lt_le_trans hPositive
  (@measure_mono R X mu (euclidean_lebesgue_is_measure R 1) _ _ (@subset_closure X S)).
have hFin:mu (closure S) \is a fin_num by rewrite (ge0_fin_numE (ltW hClosurePositive)); exact hFinite.
pose a:R:=fine (mu (closure S)).
have hMass:mu (closure S)=a%:E by rewrite /a fineK.
have ha:0<a by move:hClosurePositive; rewrite hMass lte_fin.
have hFull:=@positive_closure_rectifiable_boundary_isoperimetric R 0 S a hMass ha hRect.
rewrite /= mul0r invr1 euclidean_unit_ball_volume1 real_power_zero_exponent
  real_power_one_exponent ?ler0n // mulr1 mul1r in hFull.
exists S; split; first exact hRect.
split; first by apply/andP.
exact hFull.
Qed.
