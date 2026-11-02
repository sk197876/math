(** Sealed Borel range reductions for Federer (1969), 2.3.6, p. 77. Source
    context: ClosedSubsetBorelRetractionUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import MetricSubsetBackground ClosedSubsetBorelRetractionUP
  ClosedSubsetBorelRetractionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type ClosedSubsetBorelRetractionSignature.
(** Source for [value]: abstract supporting range reduction
    in Federer 2.3.6, p. 77, final paragraph. *)
Parameter value : forall (R : realType) (Y : metricType R) (S : set Y),
  metric_subset S -> closed S -> Y -> metric_subset S.
(** Source for [laws]: Borel measurability and preservation
    of support points for Federer 2.3.6, p. 77. *)
Parameter laws : forall (R : realType) (Y : metricType R) (S : set Y)
  (s0 : metric_subset S) (hS : closed S),
  is_closed_subset_borel_retraction (@value R Y S s0 hS).
End ClosedSubsetBorelRetractionSignature.
Module ClosedSubsetBorelRetraction : ClosedSubsetBorelRetractionSignature.
(** Source for [value]: private witness choice for the
    range reduction supporting Federer 2.3.6, p. 77. *)
Definition value (R : realType) (Y : metricType R) (S : set Y)
    (s0 : metric_subset S) (hS : closed S) :=
  projT1 (cid (@closed_subset_borel_retraction_exists R Y S s0 hS)).
(** Source for [laws]: the witness satisfies its abstract
    range-reduction laws for Federer 2.3.6, p. 77. *)
Lemma laws (R : realType) (Y : metricType R) (S : set Y)
    (s0 : metric_subset S) (hS : closed S) :
  is_closed_subset_borel_retraction (@value R Y S s0 hS).
Proof. exact: projT2 (cid (@closed_subset_borel_retraction_exists R Y S s0 hS)). Qed.
End ClosedSubsetBorelRetraction.
