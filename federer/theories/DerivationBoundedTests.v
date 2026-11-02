(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableTotalBasic
  MeasureDerivationContext DerivationCountableMeasurability CountablyMeasurableFunctions
  MeasureEssentialNormUP MeasureEssentialNorm TotalEssentialNormBound TotalScalarLpUP
  TotalScalarLpCharacteristic CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_constant_one_linfinity]: supporting
    bounded tests in the Daniell comparison of Federer 2.9.10,
    p. 157. The constant one belongs to total L-infinity(phi)
    because class M is countably finite; finite phi(X) is not
    required. The nonzero-locus condition from 2.4.12 is retained. *)
Lemma derivation_constant_one_linfinity (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_derivation_measure phi -> total_scalar_lp phi +oo (fun _ => 1%R).
Proof.
move=> hphi; have hm := derivation_measure_law hphi.
have hf := @measurable_total_constant R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] phi hm 1%R.
have ha : measure_almost_everywhere phi [set _ : X | (`|1 : R|<=1)%R].
  apply: (@measure_almost_everywhere_mono R X phi hm setT _ _ (measure_almost_everywhere_true hm)).
  by move=> x _; rewrite normr1 lexx.
have hb := @total_essential_norm_bound R X phi hm (fun _ => 1%R) 1%R ler01 ha.
split; first exact: leey.
split=> //; split; first exact: le_lt_trans hb (ltry _).
apply: (@countably_measurable_function_on_countable_source R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] phi hm 0%R _ _ _ hf).
- change (closed [set (0%R : real_norm_metric_space (scalar_absolute_value_norm R))]).
  apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
- exact: derivation_measure_measurable_countably_measurable hphi (measure_measurable_whole hm).
Qed.

(** Source for [derivation_characteristic_linfinity]: supporting
    characteristic test for identifying k with D in Federer
    2.9.10, p. 157. Every measurable characteristic function is
    an admissible bounded test for class M, even when its measure
    is infinite; the later uniqueness step uses bounded targets. *)
Lemma derivation_characteristic_linfinity (R : realType) (X : metricType R)
    (phi : set X -> \bar R) A (s : X -> R) :
  is_derivation_measure phi -> is_characteristic_function A s -> measure_measurable phi A ->
  total_scalar_lp phi +oo s.
Proof.
move=> hphi hs hA.
have h := @total_scalar_lp_characteristic_piece R X phi (derivation_measure_law hphi) +oo A s
  (fun _ => 1%R) hs hA (@derivation_constant_one_linfinity R X phi hphi).
have he : (fun x => (1*s x)%R)=s by apply: funext=> x; rewrite mul1r.
by rewrite he in h.
Qed.
