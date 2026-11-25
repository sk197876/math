(** Federer (1969), 2.2.8, p. 64, the completeness hypothesis on X. The
    specification below is the standard Cauchy-filter formulation of
    completeness, with an existential limit instead of a chosen default
    point. It therefore imposes no unintended inhabitance premise. Source
    editions: MetricClosedBalls.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_complete_metric_space]: the abstract completeness
    hypothesis in Federer 2.2.8, p. 64: every proper Cauchy
    filter converges. This predicate states laws of a supplied space;
    it introduces no unproved global axiom or chosen construction. *)
Definition is_complete_metric_space (R : realType) (T : metricType R) : Prop :=
  forall F : set_system T, ProperFilter F -> cauchy F -> exists x : T, F --> x.
