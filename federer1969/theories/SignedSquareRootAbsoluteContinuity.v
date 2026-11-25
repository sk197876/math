(** Federer (1969), 3.2.7, p. 246:
    the signed square-root parameter is absolutely
    continuous on compact intervals. Invoke the already
    proved null-image criterion of 2.10.13, p. 177;
    no absolute continuity is assumed in its proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground SignedSquareRootSealed SignedSquareRootLaws SignedSquareRootDerivative
  SignedSquareRootContinuity ScalarDerivativeNullImages RealCurveDerivativeUP CurveArcLength StieltjesMonotone
  CurveNullImageCriterion MetricCurveAbsoluteContinuityUP LocallyAbsolutelyContinuousCurve
  HausdorffLengthReal MeasureUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [signed_root_locally_absolutely_continuous]:
    supporting reparameterization in the third example
    of Federer 3.2.7, p. 246. Monotonicity gives
    finite variation; actual finite derivatives off zero
    give null-image preservation, and continuity includes zero. *)
Theorem signed_root_locally_absolutely_continuous (R:realType):
  is_locally_absolutely_continuous_curve
    (@SignedSquareRoot.value R:real_line_metric R->real_line_metric R).
Proof.
pose G:=@SignedSquareRoot.value R.
have hBV:curve_locally_finite_variation (G:R->real_line_metric R).
  exact (@monotone_locally_finite_variation R G (@signed_root_monotone R)).
have hFinite x:x!=0%R -> exists v,has_real_curve_derivative G x v.
  move=>hx; exists (2*Num.sqrt `|x|)^-1; exact:signed_root_actual_derivative hx.
have hNull:=@scalar_derivative_off_point_preserves_null_sets R G 0%R hFinite.
move=>a b hab.
apply:(@continuous_bv_curve_null_image_criterion R [the metricType R of real_line_metric R]
  G a b hBV (@signed_root_continuous R) hab).2.
move=>N hNI hN; rewrite hausdorff_length_real_eq_lebesgue.
exact (hNull N hN).
Qed.
