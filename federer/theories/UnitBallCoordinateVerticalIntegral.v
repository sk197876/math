(** Federer 2.10.27, p. 191: actual scalar sections of the
    auxiliary unit-ball coordinate power. The symmetric power
    integral supplies all sections, including zero-radius tangencies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanCoordinateSplit EuclideanHeadBallSections RealPower RealSymmetricPowerIntegral
  UnitBallCoordinatePowerSummability LebesgueScalarMeasure MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureIntegralUP MeasureConullZeroIntegral PartialFunctionBasic
  SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [unit_ball_coordinate_vertical_integral]: supporting
    scalar-section evaluation in the real-degree profile identity of
    Federer 2.10.27, p. 191. Every positive real degree is allowed;
    exterior sections are zero and tangent intervals have zero length. *)
Theorem unit_ball_coordinate_vertical_integral (R:realType) m (k:R)
    (g:inner_metric_space (@euclidean_inner_productP R m.+1)->R)
    (y:inner_metric_space (@euclidean_inner_productP R m)):
  0<k ->is_unit_ball_coordinate_power ord0 (k-1) g ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun t=>g (euclidean_join (y,t))))
    (if inner_norm (@euclidean_inner_productP R m) y<= 1
     then (2*k^-1*real_power (Num.sqrt (1-(inner_norm (@euclidean_inner_productP R m) y)^+2)) k)%:E
     else 0%E).
Proof.
move=> hk hg.
case:(leP (inner_norm (@euclidean_inner_productP R m) y) 1)=>hy.
- apply:(@real_symmetric_power_integral R k _ _ hk (sqrtr_ge0 _)).
  + move=> t ht.
    have hBall:=(@euclidean_head_unit_ball_section R m y t hy).2 ht.
    by rewrite (hg.1 _ hBall) euclidean_join_head.
  + move=> t ht.
    have hNot:1<inner_norm (@euclidean_inner_productP R m.+1) (euclidean_join (y,t)).
      rewrite ltNge;apply/negP=> hBall.
      have hLe:=(@euclidean_head_unit_ball_section R m y t hy).1 hBall.
      have h:=lt_le_trans ht hLe;by rewrite ltxx in h.
    exact:hg.2 _ hNot.
- apply:(@measure_almost_zero_integral R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) (real_total_integrand (fun t=>g (euclidean_join (y,t))))).
  apply:(@measure_almost_everywhere_mono R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) setT _ _
    (measure_almost_everywhere_true (lebesgue_scalar_is_measure R)))=>t _.
  apply/real_total_integrand_graph.
  by rewrite (hg.2 _ (@euclidean_head_unit_ball_empty_section R m y t hy)).
Qed.
