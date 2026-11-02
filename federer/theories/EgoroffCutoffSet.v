(** Federer (1969), 2.3.7, p. 78, final set B and uniform convergence.
    Source context: UniformPartialConvergenceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import PartialFunctionUP UniformPartialConvergenceUP
  MeasurableMetricDistance MetricDeviationTails PartialSequenceCommonDomain EgoroffThresholds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [egoroff_cutoff_set]: direct final formula for B in Federer
    2.3.7, p. 78, intersected with the conull common domain as explicitly
    done. *)
Definition egoroff_cutoff_set (R : realType) (X : Type) (Y : metricType R)
    (f : nat -> partial_function X Y) (g : partial_function X Y) (J : nat -> nat) :=
  partial_sequence_common_domain f g `\`
    \bigcup_i partial_metric_deviation_tail f g (egoroff_threshold i) (J i).

(** Source for [egoroff_cutoff_uniform]: the uniform convergence
    conclusion in Federer 2.3.7, p. 78. Removing one tail
    for each dyadic threshold supplies a single index bound valid
    at every point of B. No measure premise is needed here. *)
Lemma egoroff_cutoff_uniform (R : realType) (X : Type) (Y : metricType R)
    (f : nat -> partial_function X Y) (g : partial_function X Y) (J : nat -> nat) :
  partial_function_uniformly_converges_on (egoroff_cutoff_set f g J) f g.
Proof.
constructor; first by move=> x [hx _].
move=> e he; have [i hi] := egoroff_threshold_small he.
exists (J i)=> n hn x y z [_ hx] hy hz.
have hlt : mdist y z < egoroff_threshold i.
  rewrite ltNge; apply/negP=> hbad; apply: hx; exists i; first exact Logic.I.
  exists n=> //; exists y, z; by split=> //; split.
exact: lt_trans hlt hi.
Qed.
