(** Federer (1969), 3.1.2, p. 212, through the density definition
    2.9.12, p. 158: null exceptional sets have density zero when all
    positive-radius centered balls have positive finite measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostBasic
  MeasureRestriction MeasureDerivates MeasureSetDensity MeasureApproximateLimitUP CenteredBallRelations
  MetricClosedBalls CoveringRelationFineness CoveringFiniteLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [centered_null_set_density_zero]: supporting null-set
    case of the approximate limit in Federer 3.1.2, p. 212. Every
    relevant ratio is defined and zero; no artificial ratio is used on
    null balls. The positive finite ball hypotheses are proved separately
    for Euclidean and scalar Lebesgue measure. *)
Theorem centered_null_set_density_zero (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A : set X) a :
  is_measure phi ->
  (forall x r, (0<r)%R -> 0<phi (metric_closed_ball x r) /\
    phi (metric_closed_ball x r) \is a fin_num) ->
  phi A=0 -> partial_function_graph (measure_set_density phi
    (@centered_closed_ball_relation R X) A) a 0.
Proof.
move=> hm hballs hA.
have hzero S : phi (A `&` S)=0.
  exact: (@measure_null_subset R X phi hm (A `&` S) A (fun x hx=>hx.1) hA).
have hratio x S : centered_closed_ball_relation x S ->
    partial_function_graph (measure_ratio_function (measure_restrict phi A) phi) S 0.
  move=> [r [hr ->]]; have [hp hf] := hballs x r hr.
  have h := @measure_ratio_positive_finite_denominator R X (measure_restrict phi A) phi
    (metric_closed_ball x r) hp hf.
  by rewrite /measure_restrict hzero mul0e in h.
apply: (@covering_finite_limit_of_small_values R X
  (@centered_closed_ball_relation R X) (measure_ratio_function (measure_restrict phi A) phi) a 0).
- apply: (@covering_relation_fine_mono R X (@centered_closed_ball_relation R X)
    (fun x S => centered_closed_ball_relation x S /\
      partial_function_domain (measure_ratio_function (measure_restrict phi A) phi) S)
    a _ (@centered_closed_balls_fine R X a)).
  move=> S hS; split=> //; exists 0; exact: hratio a S hS.
- move=> e he; exists 1%R; split; first exact: ltr01.
  move=> S y hS _ hy.
  have -> : y=0 := partial_function_single_valued hy (hratio a S hS).
  split; rewrite ?sub0r ?add0r lte_fin //; by rewrite oppr_lt0.
Qed.

(** Source for [centered_almost_constant_approximate_limit]: supporting
    constant-quotient case of Federer 3.1.2, p. 212. A partial function
    equal to y outside a null set has approximate limit y; points outside
    its domain must be included in that exceptional set. *)
Theorem centered_almost_constant_approximate_limit (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R)
    (f : partial_function X Y) (N : set X) a y :
  is_measure phi ->
  (forall x r, (0<r)%R -> 0<phi (metric_closed_ball x r) /\
    phi (metric_closed_ball x r) \is a fin_num) ->
  phi N=0 -> (forall x, ~ N x -> partial_function_graph f x y) ->
  is_measure_approximate_limit phi (@centered_closed_ball_relation R X) f a y.
Proof.
move=> hm hb hN hf W hW.
apply: (@centered_null_set_density_zero R X phi
  (~` partial_function_preimage f W) a hm hb).
apply: (@measure_null_subset R X phi hm _ N _ hN)=> x hx.
apply: contrapT=> hn; apply: hx; exists y; split; first exact: hf.
exact: nbhs_singleton hW.
Qed.
