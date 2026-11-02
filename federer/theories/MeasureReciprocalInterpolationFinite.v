(** Federer (1969), 2.4.17, p. 90: multiplicative form of logarithmic
    convexity. This supporting theorem treats two positive reciprocal
    exponents and strictly positive weights. Zero weights and the reciprocal
    endpoint zero are separate cases. All norm values here may be zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP RealPower
  MeasureUP MeasurableFunctionUP MeasureLpNorm
  ReciprocalInterpolationAlgebra MeasureFinitePowerInterpolation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_reciprocal_interpolation_finite]: Supporting Federer
    2.4.17, p. 90. *)
Lemma measure_reciprocal_interpolation_finite (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u v a b A B : R) (f : partial_function X (real_norm_metric_space hN)) :
  (0 < u)%R -> (u <= 1)%R -> (0 < v)%R -> (v <= 1)%R ->
  (0 < a)%R -> (0 < b)%R -> (a+b= 1)%R ->
  is_measure_measurable_function mu f ->
  measure_lp_norm mu N u^-1 f=A%:E -> measure_lp_norm mu N v^-1 f=B%:E ->
  measure_lp_norm mu N (a * u+b * v)^-1 f <= (real_power A a * real_power B b)%:E.
Proof.
move=> hu hu1 hv hv1 ha hb hab hf hA hB.
pose w := (a * u+b * v)%R.
have [hw hw1] := @positive_weighted_reciprocal_bounds R a b u v ha hb hab hu hu1 hv hv1.
have hwne : w != 0%R by rewrite gt_eqF.
have hane : a != 0%R by rewrite gt_eqF.
have hbne : b != 0%R by rewrite gt_eqF.
have huinv : (1 <= u^-1)%R by rewrite invf_ge1.
have hvinv : (1 <= v^-1)%R by rewrite invf_ge1.
have hwinv : (1 <= w^-1)%R by rewrite invf_ge1.
have hp : (1 <= w/(a * u))%R := @positive_fraction_sum_ge_one R (a * u)%R (b * v)%R (mulr_gt0 ha hu) (mulr_ge0 (ltW hb) (ltW hv)).
have hq : (1 <= w/(b * v))%R.
  rewrite /w addrC; exact: positive_fraction_sum_ge_one (mulr_gt0 hb hv) (mulr_ge0 (ltW ha) (ltW hu)).
have hpq : ((w/(a * u))^-1+(w/(b * v))^-1= 1)%R := interpolation_fraction_conjugate hwne.
have hr : (0 < a/w)%R by rewrite divr_gt0.
have hs : (0 < b/w)%R by rewrite divr_gt0.
have hrp : ((a/w) * (w/(a * u))=u^-1)%R := @interpolation_fraction_cancel R a u w hane hwne.
have hsq : ((b/w) * (w/(b * v))=v^-1)%R := @interpolation_fraction_cancel R b v w hbne hwne.
have hrs : (a/w+b/w=w^-1)%R by rewrite -mulrDl hab mul1r.
have hA0 : (0 <= A)%R.
  have hh := @measure_lp_norm_nonnegative R X V N hN mu u^-1 f hm huinv hf.
  by move: hh; rewrite hA lee_fin.
have hB0 : (0 <= B)%R.
  have hh := @measure_lp_norm_nonnegative R X V N hN mu v^-1 f hm hvinv hf.
  by move: hh; rewrite hB lee_fin.
have hbnd := @measure_finite_power_interpolation R X V N hN mu hm (w/(a * u))%R (w/(b * v))%R
  (a/w)%R (b/w)%R A B f hp hq hpq hr hs.
rewrite hrp hsq hrs in hbnd.
have hh := hbnd huinv hvinv hwinv hf hA hB.
rewrite invrK real_power_product ?real_power_nonnegative //
  !real_power_positive_iterate // ?divfK // in hh.
Qed.
