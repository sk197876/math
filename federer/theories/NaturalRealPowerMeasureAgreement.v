(** Federer (1969), 2.10.2(1), p. 171, used in 3.2.24,
    p. 260: identify the existing natural-degree Hausdorff measure
    with the real-power gauge at that same natural exponent and
    its actual unit-ball coefficient. No real-degree Gamma identity
    is needed or assumed. Both implementations remain opaque. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import HausdorffDiameterCost HausdorffMeasure HausdorffMeasureUP
  MetricRealPowerMeasure MetricRealPowerMeasureUP RealPowerNaturalHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [natural_real_power_measure_agreement]: supporting
    gauge identification for the counterexample in Federer 3.2.24,
    p. 260, by the natural-degree definition 2.10.2(1), p. 171.
    Equality of the diameter costs and abstract uniqueness prove
    equality on every set, including zero degree. *)
Theorem natural_real_power_measure_agreement (R:realType) (X:metricType R) m:
  @metric_real_power_measure R X (hausdorff_normalisation R m) m%:R=
    @hausdorff_measure R X m.
Proof.
apply:funext=>A.
exact:(@metric_real_power_measure_unique R X (hausdorff_normalisation R m) m%:R _ _
  (@metric_real_power_measure_specification R X (hausdorff_normalisation R m) m%:R)
  (hausdorff_natural_real_power_laws (@hausdorff_measure_specification R X m)) A).
Qed.
