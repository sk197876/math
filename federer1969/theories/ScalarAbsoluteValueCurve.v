(** Federer (1969), 3.2.7, p. 246, final
    example: |x| is nonexpanding and has actual unit
    speed off zero. Retain its undefined derivative
    at zero in the weighted source graph. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology RealCurveDerivativeUP RealCurveDerivativeIntegrands
  LocalRealDerivativeAgreement PartialFunctionUP PartialFunctionBasic PartialDensityProduct SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_slope_actual_derivative]: supporting
    affine derivative used on the two open half-lines
    in the final example of Federer 3.2.7, p. 246.
    It is proved from the actual quotient limit. *)
Lemma scalar_slope_actual_derivative (R:realType) (c a:R):
  has_real_curve_derivative (fun x:R=>c*x) a c.
Proof.
move=>e he; exists 1; split; first exact:ltr01.
move=>h /andP[hh hSmall].
have h0:h!= 0 by rewrite -normr_gt0.
have hEq:(c*(a+h)-c*a)/h-c= 0 by field; rewrite (negbTE h0).
by rewrite hEq normr0.
Qed.

(** Source for [scalar_absolute_value_nonexpanding]: the
    Lipschitz hypothesis in the last example of
    Federer 3.2.7, p. 246, by the reverse
    triangle inequality for the scalar norm. *)
Lemma scalar_absolute_value_nonexpanding (R:realType):
  is_metric_lipschitz_bound setT (fun x:real_line_metric R=>(`|x| : real_line_metric R)) 1.
Proof.
split; first exact:ler01.
move=>x y _ _; rewrite !real_line_metric_distanceE mul1r.
have hh:=ler_dist_normD x (-y); by rewrite normrN in hh.
Qed.

(** Source for [scalar_absolute_value_unit_speed]: the
    actual Jacobian-one calculation off zero for the
    final example of Federer 3.2.7, p. 246.
    The scalar one-dimensional Jacobian is the absolute
    derivative; no value is supplied at zero. *)
Lemma scalar_absolute_value_unit_speed (R:realType) (x:R):
  x!= 0 -> partial_function_graph
    (real_curve_absolute_derivative_integrand (fun t:R=>`|t|)) x 1%:E.
Proof.
move=>hx0; case:(ltP 0 x)=>hx.
- have hd:0<x/2 by rewrite divr_gt0.
  have hLocal y:`|y-x|<x/2 -> 1*y=`|y|.
    rewrite ltr_norml=>/andP[hl hu].
    have hy:0<=y by lra.
    by rewrite mul1r (ger0_norm hy).
  have hD:=@real_derivative_neighbourhood_agreement R (fun t:R=>1*t) (fun t:R=>`|t|)
    x (x/2) 1 hd hLocal (scalar_slope_actual_derivative 1 x).
  exists 1; split=>//; by rewrite normr1.
- have hn:x<0 by rewrite lt_neqAle hx0 hx.
  have hd:0<(-x)/2 by rewrite divr_gt0 // oppr_gt0.
  have hLocal y:`|y-x|<(-x)/2 -> (-1)*y=`|y|.
    rewrite ltr_norml=>/andP[hl hu].
    have hy:y<= 0 by lra.
    by rewrite mulN1r (ler0_norm hy).
  have hD:=@real_derivative_neighbourhood_agreement R (fun t:R=>(-1)*t) (fun t:R=>`|t|)
    x ((-x)/2) (-1) hd hLocal (scalar_slope_actual_derivative (-1) x).
  exists (-1); split=>//; by rewrite normrN normr1.
Qed.

(** Source for [absolute_value_weighted_source_identity_almost]:
    the left integrand x J_1|x| equals x off
    the single null source point zero in the last
    example of Federer 3.2.7, p. 246.
    Both graphs retain their exact original domains. *)
Lemma absolute_value_weighted_source_identity_almost (R:realType):
  measure_almost_equal (@lebesgue_scalar_measure R)
    (partial_density_product (real_total_integrand (fun x:R=>x))
      (real_curve_absolute_derivative_integrand (fun x:R=>`|x|)))
    (real_total_integrand (fun x:R=>x)).
Proof.
have hm:=lebesgue_scalar_is_measure R.
have hOff:measure_almost_everywhere (@lebesgue_scalar_measure R) (~` [set (0:R)]).
  by rewrite /measure_almost_everywhere setCK lebesgue_scalar_singleton.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ hOff)=>x hx.
have hx0:x!= 0 by apply/eqP=>he; exact (hx he).
exists x%:E; split; last by apply/real_total_integrand_graph.
apply/partial_density_product_graph; exists x%:E,1%:E; split; first by apply/real_total_integrand_graph.
split; first exact (scalar_absolute_value_unit_speed hx0).
by rewrite mule1.
Qed.
