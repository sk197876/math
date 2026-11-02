(** Federer (1969), 3.2.33, p. 270: differentiate
    the actual scalar integral defining g at every interior
    point, using continuity rather than an almost-everywhere claim. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import ExtendedRealOrderTopology RealNormUP RealMetricBackground RealOpenIntervals NormClassOneUP
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureSubsetIntegral LebesgueScalarMeasure
  BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions RealSegmentIntegralDifference
  FiniteSubsetRealConstantBounds RealCurveDerivativeUP RealIncrementDifferentiation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_scalar_prefix_derivative]: g'= psi
    in the smooth example of Federer 3.2.33, p. 270.
    Continuity bounds psi on every sufficiently short interval
    through x. Additivity identifies the actual integral with
    g(b)-g(a), and finite signed constant bounds give the
    two-sided derivative. No external fundamental theorem or
    derivative field is assumed. *)
Theorem continuous_scalar_prefix_derivative (R:realType) (psi g:R->R) x:
  norm_class_zero (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (fun _=>True) psi ->
  (forall t,0<=t<= 1 ->is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,t]
    (partial_function_total (fun t:real_line_metric R=>((psi t)%:E:extended_real_line R))) (g t)%:E) ->
  real_open_interval 0 1 x ->has_real_curve_derivative g x (psi x).
Proof.
move=>hPsi hPrimitive [hx0 hx1].
have hm:=lebesgue_scalar_is_measure R.
apply:interval_increment_bounds_derivative=>e he.
have [d [hd hCont]]:=(hPsi x Logic.I).2 e he.
pose r:R:=Order.min d (Order.min x (1-x)).
have hr:0<r by rewrite /r !lt_min hd hx0 subr_gt0 hx1.
have hrd:r<=d by rewrite /r ge_min lexx.
have hrx:r<=x.
  apply:le_trans (_:r<=Order.min x (1-x)) _; first by rewrite /r ge_min lexx orbT.
  by rewrite ge_min lexx.
have hr1:r<= 1-x.
  apply:le_trans (_:r<=Order.min x (1-x)) _; first by rewrite /r ge_min lexx orbT.
  by rewrite ge_min lexx orbT.
exists r; split; first exact hr.
move=>a b /andP [hax hxb] /andP [hWidth hSmall].
have ha0:0<=a by lra.
have hb1:b<= 1 by lra.
have hab:a<=b by lra.
have ha1:a<= 1 by lra.
have hb0:0<=b by lra.
have hI:=@lebesgue_segment_integral_finite_difference R
  (partial_function_total (fun t:real_line_metric R=>((psi t)%:E:extended_real_line R)))
  0 a b (g a) (g b) ha0 hab (hPrimitive a (ltac:(by apply/andP; split)))
  (hPrimitive b (ltac:(by apply/andP; split))).
have hSet:measure_measurable (@lebesgue_scalar_measure R) `[a,b].
  apply:(@borel_regular_borel_measurable R (real_line_metric R) (@lebesgue_scalar_measure R)
    hm (lebesgue_scalar_borel_regular R)).
  exact:(closed_borel_set (@segment_closed_real R a b)).
have hBound t:`[a,b] t ->psi x-e<=psi t<=psi x+e.
  change ((a<=t<=b)->psi x-e<=psi t<=psi x+e).
  move=>/andP [hat htb].
  have hClose:`|t-x|<d.
    rewrite ltr_norml; apply/andP; split; lra.
  have hValue:=hCont (t-x) Logic.I hClose.
  have hEq:x+(t-x)= t by ring.
  rewrite hEq ltr_norml in hValue.
  have /andP [hLow hHigh]:=hValue; apply/andP; split; lra.
have hBounds:=@finite_subset_real_constant_bounds R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm `[a,b] psi (b-a) (g b-g a) (psi x-e) (psi x+e)
  hSet (lebesgue_scalar_segment hab) hBound hI.
exact:(conj (andP hBounds).1 (andP hBounds).2).
Qed.
