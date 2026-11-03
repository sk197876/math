(** Federer (1969), 3.2.42, printed p. 278:
    apply Brunn--Minkowski to the actual inner core and
    radius-r ball, whose sum lies in the original interior.
    Closedness and finite mass precede every cancellation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology
  EuclideanLebesgueDimensions EuclideanBallVolume VectorSetSum EuclideanInnerCoreBasic
  EuclideanInnerCoreBallSum BrunnMinkowskiBallIncrement FiniteMeasureIncrementRemainder
  MetricOpenThickening RealPower MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_boundary_layer_volume_nonempty_core]: direct
    second inequality of Federer 3.2.42, p. 278, for a
    nonempty actual core, including dimension one. The finite
    closure-volume hypothesis bounds the original closed core;
    no measurability or boundedness of S is assumed. The empty
    core in higher dimensions is handled separately by its zero
    volume and positive fractional exponent. *)
Theorem inner_boundary_layer_volume_nonempty_core (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) (r:R):
  (~`metric_open_thickening (~`S) r) !=set0 ->
  (@euclidean_lebesgue_measure R k.+1 (closure S) < +oo)%E ->0<r ->
  (((k.+1)%:R*real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*
    real_power (fine (@euclidean_lebesgue_measure R k.+1
      (~`metric_open_thickening (~`S) r))) (k%:R/(k.+1)%:R))%:E<=
    @euclidean_lebesgue_measure R k.+1
      (interior S `\` (~`metric_open_thickening (~`S) r))*r^-1%:E)%E.
Proof.
move=>hCoreNe hFinite hr.
pose E:=inner_metric_space (@euclidean_inner_productP R k.+1).
pose mu:=@euclidean_lebesgue_measure R k.+1.
pose T:set E:=~`metric_open_thickening (~`S) r.
pose a:R:=fine (mu T).
pose b:R:=(k.+1)%:R*real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*
  real_power a (k%:R/(k.+1)%:R).
have hm:=euclidean_lebesgue_is_measure R k.+1.
have hTS:T `<=` S:=positive_inner_core_subset hr.
have hTC:T `<=` closure S by move=>x hx; exact:subset_closure (hTS x hx).
have hTFinite:(mu T < +oo)%E:=le_lt_trans (@measure_mono R E mu hm _ _ hTC) hFinite.
have hTFin:mu T \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm T)); exact hTFinite.
have hMass:mu T=a%:E by rewrite /a fineK.
have hTMeas:measure_measurable mu T:=(euclidean_inner_core_closed_measurable S r).2.
have hBallInside:=@euclidean_inner_core_ball_sum_interior R k.+1 S r.
have hTI:T `<=` interior S.
  move=>x hx.
  have hZero:([set y:E | `|y|<r]) 0 by rewrite /= normr0.
  have hMember:=@vector_set_sum_contains E T [set y | `|y|<r] x 0 hx hZero.
  rewrite addr0 in hMember; exact:hBallInside x hMember.
have hIncrement:=@brunn_minkowski_ball_volume_increment R k T a r hCoreNe hMass hr.
have hMono:=@measure_mono R E mu hm _ _ hBallInside.
have hBound:=le_trans hIncrement hMono.
have hEq:(k.+1)%:R*real_power a (k%:R/(k.+1)%:R)*
    real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*r=b*r.
  rewrite /b; congr (_*r); exact:mulrAC.
rewrite hEq in hBound.
have hRemainder:=@finite_measure_increment_remainder R E mu T (interior S)
  a (b*r) hTMeas hTI hMass hBound.
change (is_true (b%:E<=mu (interior S `\` T)*r^-1%:E)%E).
rewrite (lee_pdivlMr _ _ hr) -EFinM.
exact hRemainder.
Qed.
