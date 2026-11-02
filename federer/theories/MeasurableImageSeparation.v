(** Federer (1969), 2.3.2(8), p. 74: the necessary metric separation
    inequality. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasurableFunctionUP
  MeasurableFunctionBorel TopologicalBorel MeasurableSeparationUP MetricSeparationClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_function_image_separated]: direct
    forward direction of Federer 2.3.2(8), p. 74. The
    closed preimage of closure(A) separates the two test pieces. *)
Theorem measurable_function_image_separated (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) :
  is_measure_measurable_function mu f -> is_measure_image_separated mu f.
Proof.
move=> hf T A B hs.
have hC : measure_measurable mu (partial_function_preimage f (closure A)).
  apply: (@measurable_function_borel_preimage R X Y mu hm f hf).
  apply: closed_borel_set; exact: closed_closure.
rewrite (hC T); apply: leeD.
- apply: (@measure_mono R X mu hm)=> x [hx [y [hy ha]]].
  split=> //; exists y; split=> //; exact: subset_closure ha.
- apply: (@measure_mono R X mu hm)=> x [hx [y [hy hb]]].
  split=> //; move=> [z [hz hzc]].
  have he : y = z := partial_function_single_valued hy hz.
  apply: (@metric_separated_closure_disjoint R Y A B hs y hb).
  by rewrite he.
Qed.
