(** Federer (1969), 3.3.17, pp. 300–301: the exact
    original upper-density equality at relative density-one points. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureDerivationContext MeasureDerivates
  CenteredBallRelations MetricDensities MetricDensityNumericalBounds MetricDensityMonotonicity
  MetricDensityOneFiniteUpperBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_density_one_upper_agreement]: the exact
    upper-density equation in the proof of Federer 3.3.17,
    pp. 300–301. Domination and the ORIGINAL relative derivate
    value one give equality of the ORIGINAL upper m densities.
    If the numerator density is finite, use the proved finite
    transfer bound; if it is infinite, monotonicity retains
    infinity. No finite upper-density premise is added. *)
Theorem metric_density_one_upper_agreement (R:realType) (X:metricType R) m
    (psi nu:set X->\bar R) (a:X):
  is_derivation_measure psi ->is_measure nu ->(forall S,nu S<=psi S) ->
  partial_function_graph (measure_derivate nu psi (@centered_closed_ball_relation R X)) a 1 ->
  upper_metric_density m nu a=upper_metric_density m psi a.
Proof.
move=>hPsi hNu hDomination hOne.
have hMono:=(@metric_densities_monotone R X m nu psi a hDomination).2.
have hNonnegative:=(@metric_densities_nonnegative R X m nu a hNu).2.
have hReverse:upper_metric_density m psi a<=upper_metric_density m nu a.
  case hValue:(upper_metric_density m nu a)=>[b| |].
  - have hB:(0<=b)%R by move:hNonnegative; rewrite hValue lee_fin.
    have hBound:upper_metric_density m nu a<=b%:E by rewrite hValue.
    exact:(@metric_density_one_finite_upper_bound R X m psi nu a b hPsi hOne hB hBound).
  - exact:leey.
  - by rewrite hValue leNgt ltNyr in hNonnegative.
by apply/eqP; rewrite eq_le hMono hReverse.
Qed.
