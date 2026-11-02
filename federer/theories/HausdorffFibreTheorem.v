(** Federer (1969), 2.10.25, pp. 188–189: public integer-degree theorem with
    the actual least Lipschitz constant. All ingredients are obtained
    through existing abstract measure, covering-infimum, limit and Lipschitz
    interfaces. No measurability of the fibre integrand is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  LipschitzUP LipschitzConstant HausdorffMeasure HausdorffFibreCost HausdorffFibreCutoffs
  HausdorffFibreIntegralBound MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_25]: direct inequality in
    2.10.25, p. 188, with its printed alternative
    support/properness hypothesis. Degrees k,m are natural
    numbers, including zero; the optional real-degree
    Gamma extension is not claimed. The integral is
    the upper integral of an arbitrary fibre-mass function. *)
Theorem federer_2_10_25 (R : realType) (X Y : metricType R)
    (f : X -> Y) (hf : is_metric_lipschitz setT f) k m A :
  hausdorff_fibre_integral_condition f A k m ->
  measure_upper_integral (@hausdorff_measure R Y m)
    (partial_function_total (hausdorff_fibre_mass f A k))<=
    (hausdorff_fibre_bound_constant k m (metric_lipschitz_constant hf))%:E*
      @hausdorff_measure R X (k+m) A.
Proof.
exact: hausdorff_lipschitz_fibre_integral_bound
  (least_metric_lipschitz_bound (metric_lipschitz_constant_specification hf)).
Qed.
