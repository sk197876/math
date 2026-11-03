(** Federer (1969), 3.2.42, printed p. 278:
    the first boundary-layer volume estimate for a nonempty
    original source. Closed-source volume is finite, but the
    actual exterior tube volume may be infinite. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanBallVolume BrunnMinkowskiBallIncrement
  EuclideanBallVectorSumTube MetricOpenThickening MetricOpenThickeningClosure
  FiniteMeasureIncrementRemainder RealPower TopologicalBorel MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [outer_boundary_layer_volume_nonempty]: direct
    first inequality of Federer 3.2.42, p. 278, with the
    source nonempty to include the dimension-one zero-volume
    case under the project's integer-power convention. The
    actual outer layer is {0<dist(x,S)<r}; its distance-free
    tube form also has a correct empty-set interpretation.
    No measurability or boundedness of S is assumed. *)
Theorem outer_boundary_layer_volume_nonempty (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) (r:R):
  S !=set0 ->(@euclidean_lebesgue_measure R k.+1 (closure S) < +oo)%E ->0<r ->
  (((k.+1)%:R*real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*
    real_power (fine (@euclidean_lebesgue_measure R k.+1 (closure S)))
      (k%:R/(k.+1)%:R))%:E<=
    @euclidean_lebesgue_measure R k.+1
      (metric_open_thickening S r `\` closure S)*r^-1%:E)%E.
Proof.
move=>hS hFinite hr.
pose E:=inner_metric_space (@euclidean_inner_productP R k.+1).
pose mu:=@euclidean_lebesgue_measure R k.+1.
pose C:=closure S.
pose a:R:=fine (mu C).
pose b:R:=(k.+1)%:R*real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*
  real_power a (k%:R/(k.+1)%:R).
have hm:=euclidean_lebesgue_is_measure R k.+1.
have hCNe:C !=set0.
  have [x hx]:=hS; exists x; exact:subset_closure hx.
have hCMeas:measure_measurable mu C.
  apply:euclidean_borel_measurable; apply:closed_borel_set; exact:closed_closure.
have hCFin:mu C \is a fin_num by rewrite ge0_fin_numE ?measure_nonnegative //; exact hFinite.
have hMass:mu C=a%:E by rewrite /a fineK.
have hIncrement:=@brunn_minkowski_ball_volume_increment R k C a r hCNe hMass hr.
rewrite -euclidean_ball_vector_sum_tube /C metric_open_thickening_closure in hIncrement.
have hEq:(k.+1)%:R*real_power a (k%:R/(k.+1)%:R)*
    real_power (euclidean_unit_ball_volume R k.+1) ((k.+1)%:R)^-1*r=b*r.
  rewrite /b; congr (_*r); exact:mulrAC.
rewrite hEq in hIncrement.
have hIncluded:C `<=` metric_open_thickening S r.
  rewrite /C -metric_open_thickening_closure.
  exact:(@metric_open_thickening_includes R E C r hr).
have hRemainder:=@finite_measure_increment_remainder R E mu C
  (metric_open_thickening S r) a (b*r) hCMeas hIncluded hMass hIncrement.
change (is_true (b%:E<=mu (metric_open_thickening S r `\` C)*r^-1%:E)%E).
rewrite (lee_pdivlMr _ _ hr) -EFinM.
exact hRemainder.
Qed.
