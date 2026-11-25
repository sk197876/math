(** Federer (1969), 3.2.41, printed p. 278, final proof paragraph:
    taking the density-one hull twice has no further effect.
    This supporting pointwise fact is proved through exact test masses,
    not by discarding a possibly non-null hull difference. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureDensityPoints MeasureDerivationContext
  DensityOneMeasureTests MeasureTestDerivateAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_one_points_idempotent]: supporting hull law
    for the last inclusion in Federer 3.2.41, p. 278. Equality holds
    as actual point sets, rather than only almost everywhere, for
    every original set allowed by 2.9.11, p. 158. *)
Theorem density_one_points_idempotent (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) :
  is_measure_derivation_context mu V ->
  measure_density_one_points mu V (measure_density_one_points mu V A)=
    measure_density_one_points mu V A.
Proof.
move=> hc; apply/seteqP; split=> x.
- exact: (@measure_test_derivate_agreement R X mu V A
    (measure_density_one_points mu V A) hc
    (fun T hT => @density_one_points_measure_test R X mu V A T hc hT) x 1).2.
- exact: (@measure_test_derivate_agreement R X mu V A
    (measure_density_one_points mu V A) hc
    (fun T hT => @density_one_points_measure_test R X mu V A T hc hT) x 1).1.
Qed.
