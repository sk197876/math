(** Federer (1969), 3.2.41, printed p. 278, final proof paragraph:
    density-one hulls are monotone under inclusion. This supporting
    form requires positive finite masses on related cells, as supplied
    by the actual positive-radius Euclidean balls. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureRestriction
  MeasureDerivationContext MeasureDerivates MeasureDensityPoints SetDensityRatios
  CoveringFamilyUP CoveringRelationFineness CoveringRelationLimits CoveringFiniteLimitBounds
  MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [density_one_points_monotone]: supporting density-hull
    inclusion in Federer 3.2.41, p. 278. The original arbitrary sets
    need not be measurable. A defined density-one ratio for A is
    squeezed below the ratios for B and the exact whole-cell ratio one. *)
Theorem density_one_points_monotone (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (V : X -> set X -> Prop) (A B : set X) :
  is_derivation_measure mu ->
  (forall x S, V x S -> 0<mu S /\ mu S \is a fin_num) ->
  A `<=` B -> measure_density_one_points mu V A `<=` measure_density_one_points mu V B.
Proof.
move=> hmu hCells hAB x hx.
have hm := derivation_measure_law hmu.
have hDomain z S : V z S ->
    partial_function_domain (measure_ratio_function (measure_restrict mu B) mu) S.
  move=> hS; have [hp hf] := hCells z S hS.
  exists (measure_restrict mu B S/mu S).
  exact: measure_ratio_positive_finite_denominator hp hf.
apply: (@covering_finite_limit_of_small_values R X V
  (measure_ratio_function (measure_restrict mu B) mu) x 1%R).
- apply: (@covering_relation_fine_mono R X V
    (fun z S => V z S /\ partial_function_domain
      (measure_ratio_function (measure_restrict mu B) mu) S) x _ hx.1).
  move=> S hS; split=> //; exact: hDomain x S hS.
- move=> e he.
  have [d [hd hs]] := @covering_finite_limit_small_values R X V
    (measure_ratio_function (measure_restrict mu A) mu) x 1 e hx he.
  exists (Num.min d 1)%R; split; first by rewrite lt_min hd ltr01.
  move=> S y hS hDiam hy.
  have hSmall : extended_metric_diameter S<d%:E.
    apply: lt_le_trans hDiam _; by rewrite lee_fin ge_min lexx.
  have hBound : metric_set_bounded S.
    apply: lt_trans hDiam _; exact: ltry.
  have [hp hf] := hCells x S hS.
  have hA := @measure_ratio_positive_finite_denominator R X
    (measure_restrict mu A) mu S hp hf.
  have hLower := @bounded_density_ratio_order R X mu A B S _ y hmu hBound
    (fun z hz => conj (hAB z hz.1) hz.2) hA hy.
  have hFull := @measure_ratio_positive_finite_denominator R X
    (measure_restrict mu setT) mu S hp hf.
  have hpe : mu S=(fine (mu S))%:E by rewrite fineK.
  have hp0 : (0<fine (mu S))%R by move: hp; rewrite hpe lte_fin.
  rewrite /measure_restrict setTI hpe inver (gt_eqF hp0) -EFinM divff ?gt_eqF // in hFull.
  have hUpper := @bounded_density_ratio_order R X mu B setT S y 1 hmu hBound
    (fun z hz => conj Logic.I hz.2) hy hFull.
  split; first exact: lt_le_trans (hs S _ hS hSmall hA).1 hLower.
  apply: le_lt_trans hUpper _; rewrite lte_fin; lra.
Qed.
