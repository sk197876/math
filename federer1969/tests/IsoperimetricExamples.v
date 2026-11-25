(** Federer (1969), 3.2.43, printed p.278:
    actual positive-volume planar and line sources test the
    whole inequality; a zero-volume singleton tests the
    excluded zero-exponent extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerNormedTopology EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanLebesgueHaar
  EuclideanBallVolume EuclideanClosedBallVolume MetricClosedBalls MetricOpenThickening
  IsoperimetricInequality MinkowskiContents MinkowskiZeroCounting CountingMeasure NonnegativeSum NonnegativeSumSupport
  ApproximateDifferentialAffine RealPower MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [isoperimetric_positive_disc_example]: the whole
    inequality of Federer3.2.43,p.278, on the actual closed
    unit disc, with its proved positive finite original
    closure volume alpha(2). The asserted boundary-content
    lower bound is strictly positive. *)
Example isoperimetric_positive_disc_example (R:realType):
  exists S:set (inner_metric_space (@euclidean_inner_productP R 2)),
    @euclidean_lebesgue_measure R 2 (closure S)=(euclidean_unit_ball_volume R 2)%:E /\
    (0<((2:R)*real_power (euclidean_unit_ball_volume R 2) (1/2:R)*
      real_power (euclidean_unit_ball_volume R 2) (1/2:R))%:E)%E /\
    (((2:R)*real_power (euclidean_unit_ball_volume R 2) (1/2:R)*
      real_power (euclidean_unit_ball_volume R 2) (1/2:R))%:E<=
      lower_minkowski_content 1 (closure S `\` interior S))%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose S:set X:=metric_closed_ball (0:X) 1.
have hClosed:closed S:=@metric_closed_ball_closed R X 0 1.
have hClosure:closure S=S:=esym ((closure_id S).1 hClosed).
have hMass:@euclidean_lebesgue_measure R 2 (closure S)=(euclidean_unit_ball_volume R 2)%:E.
  by rewrite hClosure /S (@euclidean_closed_ball_normalized_volume R 2 (0:X) 1 ler01) expr1n mulr1.
have hFinite:(@euclidean_lebesgue_measure R 2 (closure S) < +oo)%E by rewrite hMass ltry.
have hAlpha:0<euclidean_unit_ball_volume R 2:=(euclidean_unit_ball_volumeE R 2).2.
have hPositive:(0<((2:R)*real_power (euclidean_unit_ball_volume R 2) (1/2:R)*
    real_power (euclidean_unit_ball_volume R 2) (1/2:R))%:E)%E.
  rewrite lte_fin; apply:mulr_gt0; last exact:real_power_strictly_positive _ hAlpha.
  apply:mulr_gt0; [by rewrite ltr0n|exact:real_power_strictly_positive _ hAlpha].
have h:=@federer_3_2_43 R 0 S hFinite.
rewrite hMass /= mul1r in h.
exists S; split; first exact hMass.
split; first exact hPositive.
by rewrite mul1r.
Qed.

(** Source for [isoperimetric_positive_unit_segment_example]:
    the positive-volume dimension-one case of Federer3.2.43,
    p.278. The actual closed unit segment has volume one,
    and the whole theorem forces at least two boundary atoms. *)
Example isoperimetric_positive_unit_segment_example (R:realType):
  exists S:set (inner_metric_space (@euclidean_inner_productP R 1)),
    @euclidean_lebesgue_measure R 1 (closure S)= 1%E /\
    ((2:R)%:E<=lower_minkowski_content 0 (closure S `\` interior S))%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose S:set X:=[set x|forall i,0<=x i<= 1]%R.
have hCompact:compact S:=@euclidean_closed_box_compact R 1 (fun _=>0) (fun _=>1).
have hClosed:closed S:=compact_closed (@metric_hausdorff R X) hCompact.
have hClosure:closure S=S:=esym ((closure_id S).1 hClosed).
have hMass:@euclidean_lebesgue_measure R 1 (closure S)= 1%E.
  rewrite hClosure /S (@euclidean_closed_box R 1 (fun _=>0) (fun _=>1) (fun _=>ler01)).
  by rewrite big_ord1 subr0.
have h:=@positive_closure_volume_isoperimetric R 0 S 1 hMass ltr01.
rewrite /= mul0r invr1 euclidean_unit_ball_volume1 real_power_zero_exponent
  real_power_one_exponent ?ler0n // mulr1 mul1r in h.
exists S; split; [exact hMass|exact h].
Qed.

(** Source for [isoperimetric_null_line_singleton_exclusion_example]:
    the zero-exponent qualification of Federer3.2.43,p.278.
    The actual line singleton has zero closure volume and
    boundary lower content one. The totalized printed right
    coefficient would be two, so that extension is false. *)
Example isoperimetric_null_line_singleton_exclusion_example (R:realType):
  exists S:set (inner_metric_space (@euclidean_inner_productP R 1)),
    @euclidean_lebesgue_measure R 1 (closure S)=0%E /\
    lower_minkowski_content 0 (closure S `\` interior S)= 1%E /\
    ~(((1:R)*real_power (euclidean_unit_ball_volume R 1) 1*
      real_power (fine (@euclidean_lebesgue_measure R 1 (closure S))) 0)%:E<=
      lower_minkowski_content 0 (closure S `\` interior S))%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose S:set X:=[set (0:X)].
have hClosed:closed S:=compact_closed (@metric_hausdorff R X) (@compact_set1 X 0).
have hClosure:closure S=S:=esym ((closure_id S).1 hClosed).
have hInterior:interior S=set0.
  apply/seteqP; split; last by move=>x [].
  move=>x hx.
  have hx0:x=(0:X):=interior_subset hx.
  rewrite hx0 in hx.
  have [d hd hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (0:X) S) hx.
  pose y:X:=[ffun _:'I_1=>d/2].
  have hHalf0:0<d/2 by rewrite divr_gt0.
  have hHalfLt:d/2<d by rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
  have hHalf:0<d/2<d by apply/andP.
  have hNear:mdist (0:X) y<d.
    rewrite inner_metric_normE subr0 euclidean_norm_one /y ffunE (ger0_norm (ltW hHalf0)).
    exact hHalfLt.
  have hZero:y=(0:X):=hBall y hNear.
  have hCoord:=congr1 (fun z:X=>z ord0) hZero.
  rewrite /y !ffunE in hCoord.
  have hPositive:0<d/2:=(andP hHalf).1.
  by rewrite hCoord ltxx in hPositive.
have hBoundary:closure S `\` interior S=S by rewrite hClosure hInterior setD0.
have hMass:@euclidean_lebesgue_measure R 1 (closure S)=0%E.
  rewrite hClosure; exact:(@positive_euclidean_singleton_null R 0 0).
have hCount:@counting_measure R X S= 1%E.
  rewrite /S counting_measure_sum nonnegative_sum_singleton; first reflexivity.
  by rewrite lee_fin ler01.
have hContent:lower_minkowski_content 0 (closure S `\` interior S)= 1%E.
  by rewrite hBoundary (zero_minkowski_contents_counting S).2.
exists S; split; first exact hMass.
split; first exact hContent.
rewrite hContent hMass fine0 real_power_zero_exponent euclidean_unit_ball_volume1
  real_power_one_exponent ?ler0n // mulr1 mul1r lee_fin.
move=>h.
have hStrict:(1:R)<2 by rewrite ltr1n.
have hBad:=lt_le_trans hStrict h.
by rewrite ltxx in hBad.
Qed.
