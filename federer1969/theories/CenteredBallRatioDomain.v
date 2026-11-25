(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostBasic
  MeasureDerivationContext MeasureDerivates NullBallLocus MetricClosedBalls CoveringFamilyUP
  CoveringFamilyLaws CoveringRelationUP CoveringRelationFineness CoveringRelationLimits
  CenteredBallRelations MetricDiameterUP MetricDiameter ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [centered_ball_ratio_positive_domain]: supporting
    actual quotient values outside P in Federer 2.9.15,
    p. 160. Every positive-radius ball centered outside
    P has positive finite phi mass. The numerator need not
    be finite or regular for this domain assertion. *)
Lemma centered_ball_ratio_positive_domain (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (x : X) (r : R) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x -> (0<r)%R ->
  partial_function_graph (measure_ratio_function psi phi) (metric_closed_ball x r)
    (psi (metric_closed_ball x r)/phi (metric_closed_ball x r)).
Proof.
move=> hphi hx hr; have hm := derivation_measure_law hphi.
have hp := @outside_null_ball_points_positive R X phi x r hm hx hr.
have hf : phi (metric_closed_ball x r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact (@derivation_measure_bounded_finite R X phi hphi _
    (@covering_closed_ball_bounded R X x r (ltW hr))).
exact: measure_ratio_positive_finite_denominator hp hf.
Qed.

(** Source for [centered_ratio_domain_fine]: supporting domain
    fineness outside P in Federer 2.9.15, p. 160.
    All positive-radius centered balls have actual defined
    quotients there, and their diameters tend to zero. No
    equality between a ball diameter and twice its radius
    is assumed, so isolated points are included. *)
Lemma centered_ratio_domain_fine (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  covering_relation_fine_at (fun x S => centered_closed_ball_relation x S /\
    partial_function_domain (measure_ratio_function psi phi) S) x.
Proof.
move=> hphi hx.
apply: (@covering_relation_fine_mono R X (@centered_closed_ball_relation R X)
  (fun x S => centered_closed_ball_relation x S /\
    partial_function_domain (measure_ratio_function psi phi) S) x _
  (@centered_closed_balls_fine R X x)).
move=> S hS; split=> //; have [r [hr ->]] := hS.
exists (psi (metric_closed_ball x r)/phi (metric_closed_ball x r)).
exact: centered_ball_ratio_positive_domain hphi hx hr.
Qed.

(** Source for [centered_derivate_outside_null_ball_points]:
    supporting exclusion of P from W in Federer 2.9.15,
    p. 160. At a point with a null ball all sufficiently
    small centered cells have zero denominator, hence the
    ordinary covering derivate has no value, including infinity.
    This enforces the partial-division convention of 2.1.1. *)
Lemma centered_derivate_outside_null_ball_points (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (x : X) y :
  is_measure phi ->
  partial_function_graph (measure_derivate psi phi (@centered_closed_ball_relation R X)) x y ->
  ~ measure_null_ball_points phi x.
Proof.
move=> hm [_ [hu hl]] [r [hr hz]].
pose V := @centered_closed_ball_relation R X.
pose f := measure_ratio_function psi phi.
have hempty : covering_value_range V f x r=set0.
  apply/seteqP; split=> q; last by move=> [].
  move=> [S [hS [hdiam hq]]].
  have hsub : S `<=` metric_closed_ball x r.
    move=> z hzS; have hxS := @centered_closed_balls_covering R X x S hS.
    have hd := metric_diameter_upper (extended_metric_diameter_specification S) hxS hzS.
    have hh := le_lt_trans hd hdiam; rewrite lte_fin in hh; exact: ltW hh.
  have hzS := @measure_null_subset R X phi hm S (metric_closed_ball x r) hsub hz.
  exfalso; apply: (@measure_ratio_zero_denominator R X psi phi S hzS).
  by exists q.
have hup := @covering_upper_limit_le_level R X V f x r hr.
have hlo := @covering_lower_limit_ge_level R X V f x r hr.
rewrite hempty extended_real_sup_empty hu in hup.
rewrite hempty extended_real_inf_empty hl in hlo.
by have := le_trans hlo hup.
Qed.
