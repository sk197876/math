From Federer Require Import BoundaryLayerDistanceForm.
(** Federer (1969), 3.2.42, printed p. 278:
    concrete regressions retain a positive planar body and
    inner core, empty higher-dimensional sources, and an
    actual nonempty one-dimensional source with empty core. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanLebesgueHaar EuclideanClosedBallVolume EuclideanBallVolume
  BoundaryLayerVolume EuclideanInnerCoreBasic MetricClosedBalls MetricOpenThickening
  MetricOpenThickeningClosure RealPower MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [boundary_layer_positive_planar_core_example]:
    both estimates of Federer 3.2.42, p. 278, apply to
    the actual closed unit disc in R^2 at radius one half.
    Its actual inner core has strictly positive finite volume:
    it contains the actual radius-one-quarter closed ball. *)
Example boundary_layer_positive_planar_core_example (R:realType):
  exists S:set (inner_metric_space (@euclidean_inner_productP R 2)),
    (0<@euclidean_lebesgue_measure R 2 (closure S) < +oo)%E /\
    (0<@euclidean_lebesgue_measure R 2
      (~`metric_open_thickening (~`S) (1/2:R)) < +oo)%E /\
    (((2:R)*real_power (euclidean_unit_ball_volume R 2) (2:R)^-1*
      real_power (fine (@euclidean_lebesgue_measure R 2 (closure S))) (1/2:R))%:E<=
      @euclidean_lebesgue_measure R 2
        (metric_open_thickening S (1/2:R) `\` closure S)*(1/2:R)^-1%:E)%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose mu:=@euclidean_lebesgue_measure R 2.
pose S:set X:=metric_closed_ball (0:X) 1.
pose D:set X:=metric_closed_ball (0:X) (1/4:R).
pose T:set X:=~`metric_open_thickening (~`S) (1/2:R).
have hm:=euclidean_lebesgue_is_measure R 2.
have hHalf:0<(1/2:R) by rewrite divr_gt0.
have hQuarter:0<(1/4:R) by rewrite divr_gt0.
have hSmall:(1/4+1/2:R)<1 by clear -R; lra.
have hDT:D `<=` T.
  move=>x hx [y hy hNear]; apply:hy.
  change (is_true (mdist (0:X) y<=1)).
  have hX:(mdist (0:X) x<=1/4)%R:=hx.
  change (is_true (mdist y x<1/2)) in hNear.
  rewrite metric_sym in hNear.
  have hSum:mdist (0:X) x+mdist x y<1.
    exact:lt_trans (ler_ltD hX hNear) hSmall.
  exact:ltW (le_lt_trans (metric_triangle (0:X) x y) hSum).
have hSClosed:closed S:=(@metric_closed_ball_closed R X 0 1).
have hClosure:closure S=S:=esym ((closure_id S).1 hSClosed).
have hMass:mu S=(euclidean_unit_ball_volume R 2)%:E.
  rewrite /mu /S (@euclidean_closed_ball_normalized_volume R 2 (0:X) 1 ler01) expr1n mulr1.
  reflexivity.
have hPositive:(0<mu (closure S))%E.
  rewrite hClosure hMass lte_fin; exact:(euclidean_unit_ball_volumeE R 2).2.
have hFinite:(mu (closure S) < +oo)%E by rewrite hClosure hMass ltry.
have hDPositive:(0<mu D)%E.
  rewrite /mu /D (@euclidean_closed_ball_normalized_volume R 2 (0:X) (1/4) (ltW hQuarter)) lte_fin.
  exact:mulr_gt0 (euclidean_unit_ball_volumeE R 2).2 (exprn_gt0 2 hQuarter).
have hTPositive:(0<mu T)%E:=lt_le_trans hDPositive (@measure_mono R X mu hm _ _ hDT).
have hTS:T `<=` S:=positive_inner_core_subset hHalf.
have hTFinite:(mu T < +oo)%E.
  apply:le_lt_trans (@measure_mono R X mu hm _ _ hTS) _; by rewrite hMass ltry.
have [hOuter hInner]:=@federer_3_2_42 R 0 S (1/2:R) hFinite hHalf.
exists S; split; first by apply/andP.
split; first by apply/andP.
have hExp:((1:R)/(2:R))=(1/2:R) by reflexivity.
exact hOuter.
Qed.

(** Source for [boundary_layer_empty_plane_example]: the empty
    original source and empty core in Federer 3.2.42, p. 278,
    in dimension two. Both positive-exponent bounds are zero
    and follow from the whole paired theorem. *)
Example boundary_layer_empty_plane_example (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 2) in
  let S:set X:=set0 in
  (((2:R)*real_power (euclidean_unit_ball_volume R 2) (2:R)^-1*
    real_power (fine (@euclidean_lebesgue_measure R 2 (closure S))) (1/2:R))%:E<=
    @euclidean_lebesgue_measure R 2
      (metric_open_thickening S 1 `\` closure S))%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose S:set X:=set0.
have hFinite:(@euclidean_lebesgue_measure R 2 (closure S) < +oo)%E.
  by rewrite /S closure0 (measure_empty (euclidean_lebesgue_is_measure R 2)) ltry.
have h:=(@federer_3_2_42 R 0 S 1 hFinite ltr01).1.
by rewrite invr1 mule1 in h.
Qed.

(** Source for [boundary_layer_empty_core_line_exclusion_example]:
    the zero-exponent scope of Federer 3.2.42, p. 278.
    The actual nonempty open unit interval in R^1 has finite
    closure volume, but its radius-two inner core is empty.
    The inner layer has volume at most one, so division by two
    cannot meet the falsely totalized coefficient alpha(1)=2.
    This is a boundary qualification absent from the working erratum. *)
Example boundary_layer_empty_core_line_exclusion_example (R:realType):
  exists S:set (inner_metric_space (@euclidean_inner_productP R 1)),
    S !=set0 /\(@euclidean_lebesgue_measure R 1 (closure S) < +oo)%E /\
    (~`metric_open_thickening (~`S) (2:R))=set0 /\
    ~(((1:R)*real_power (euclidean_unit_ball_volume R 1) 1*
      real_power (fine (@euclidean_lebesgue_measure R 1
        (~`metric_open_thickening (~`S) (2:R)))) 0)%:E<=
      @euclidean_lebesgue_measure R 1
        (interior S `\` (~`metric_open_thickening (~`S) (2:R)))*(2:R)^-1%:E)%E.
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose mu:=@euclidean_lebesgue_measure R 1.
pose S:set X:=[set x|forall i,0<x i<1]%R.
pose Q:set X:=[set x|forall i,0<=x i<= 1]%R.
pose T:set X:=~`metric_open_thickening (~`S) (2:R).
have hm:=euclidean_lebesgue_is_measure R 1.
have hTwo:0<(2:R) by rewrite ltr0n.
have hHalf:0<(1/2:R)<1 by clear -R; lra.
have hSNe:S !=set0.
  exists ([ffun _:'I_1=>(1/2:R)]:X); by move=>i; rewrite ffunE.
have hSQ:S `<=` Q.
  move=>x hx i; have /andP[h0 h1]:=hx i; apply/andP; split; exact:ltW.
have hQCompact:compact Q:=@euclidean_closed_box_compact R 1
  (fun _:'I_1=>(0:R)) (fun _:'I_1=>(1:R)).
have hQClosed:closed Q:=compact_closed (@metric_hausdorff R X) hQCompact.
have hCQ:closure S `<=` Q.
  rewrite ((closure_id Q).1 hQClosed); exact:closureS hSQ.
have hFinite:(mu (closure S) < +oo)%E:=le_lt_trans
  (@measure_mono R X mu hm _ _ hCQ) (euclidean_compact_finite hQCompact).
have hEmpty:T=set0.
  apply/seteqP; split; last by move=>x [].
  move=>x hx.
  have hSX:=(@positive_inner_core_subset R X S 2 hTwo) x hx.
  have /andP[h0 h1]:=hSX ord0.
  have hOutside:(~`S) 0.
    move=>hAt; have h:=hAt ord0; by rewrite ffunE ltxx in h.
  have hNear:mdist (0:X) x<(2:R).
    rewrite inner_metric_normE subr0 euclidean_norm_one ger0_norm ?ltW //.
    exact:lt_trans h1 (ltr1n R 2).
  apply:hx; by exists (0:X).
have hMass:mu S= 1%E:=euclidean_unit_cube R 1.
have hSub:(interior S `\` T) `<=` S.
  move=>x [hx _]; exact:interior_subset hx.
have hBound:(mu (interior S `\` T)<= 1%E)%E.
  rewrite -hMass; exact:(@measure_mono R X mu hm _ _ hSub).
have hScaled:((mu (interior S `\` T)*(2:R)^-1%:E)<=(1/2:R)%:E)%E.
  have hInv:(0<=((2:R)^-1)%:E)%E by rewrite lee_fin invr_ge0 ler0n.
  have h:=lee_wpmul2r hInv hBound.
  rewrite mul1r; by rewrite -EFinM mul1r in h.
exists S; split; first exact hSNe.
split; first exact hFinite.
split; first exact hEmpty.
rewrite /T in hEmpty.
rewrite /T hEmpty in hScaled.
rewrite hEmpty (measure_empty hm) fine0 real_power_zero_exponent
  euclidean_unit_ball_volume1 real_power_one_exponent ?ler0n // mul1r mulr1.
move=>hWrong.
have hBad:=le_trans hWrong hScaled.
have hScalar:(2:R)>1/2 by clear -R; lra.
by move:hBad; rewrite lee_fin leNgt hScalar.
Qed.
