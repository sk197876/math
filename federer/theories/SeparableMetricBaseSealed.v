(** Sealed countable-base witness supporting Federer (1969), 2.2.4, p. 62.
    The enumeration of balls is private. Source context:
    SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import CountableOpenBaseUP SeparableMetricBaseConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SeparableMetricBaseSignature.
(** Source for [value]: abstract countable-base witness supporting
    the cardinality argument in Federer 2.2.4, p. 62. *)
Parameter value : forall (R : realType) (T : metricType R) (D : set T),
  countable D -> dense D -> nat -> set T.
(** Source for [laws]: the countable-base laws supporting Federer 2.2.4, p.
    62 *)
Parameter laws : forall (R : realType) (T : metricType R) (D : set T)
  (hc : countable D) (hd : dense D), is_countable_open_base (@value R T D hc hd).
End SeparableMetricBaseSignature.
Module SeparableMetricBase : SeparableMetricBaseSignature.
(** Source for [value]: private witness selected from the proved
    countable-base existence used for Federer 2.2.4, p. 62. *)
Definition value (R : realType) (T : metricType R) (D : set T)
    (hc : countable D) (hd : dense D) :=
  projT1 (cid (@separable_metric_countable_base_exists R T D hc hd)).
(** Source for [laws]: the proved witness satisfies the abstract
    base specification supporting Federer 2.2.4, p. 62. *)
Lemma laws (R : realType) (T : metricType R) (D : set T)
    (hc : countable D) (hd : dense D) : is_countable_open_base (@value R T D hc hd).
Proof. exact: projT2 (cid (@separable_metric_countable_base_exists R T D hc hd)). Qed.
End SeparableMetricBase.
