(** Opaque diameter interface supporting Federer (1969),
    2.10.1, p. 170. Downstream arguments use only its
    upper-bound and least-bound laws. Source: MetricDiameterUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MetricDiameterUP MetricDiameterConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type MetricDiameterSignature.
(** Source for [value]: the diameter in Federer 2.10.1, p. 170. *)
Parameter value : forall (R : realType) (X : metricType R), set X -> \bar R.
(** Source for [laws]: diameter order laws supporting
    Federer 2.10.1, p. 170. *)
Parameter laws : forall (R : realType) (X : metricType R) (A : set X),
  is_extended_metric_diameter A (@value R X A).
End MetricDiameterSignature.

Module MetricDiameter : MetricDiameterSignature.
(** Source for [value]: choice from the proved diameter
    existence result supporting Federer 2.10.1, p. 170. *)
Definition value (R : realType) (X : metricType R) (A : set X) :=
  projT1 (cid (@extended_metric_diameter_exists R X A)).
(** Source for [laws]: proved laws of the chosen diameter,
    supporting Federer 2.10.1, p. 170. *)
Lemma laws (R : realType) (X : metricType R) (A : set X) :
  is_extended_metric_diameter A (@value R X A).
Proof. exact: projT2 (cid (@extended_metric_diameter_exists R X A)). Qed.
End MetricDiameter.
