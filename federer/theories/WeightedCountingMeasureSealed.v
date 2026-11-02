(** Opaque implementation boundary for the weighted counting measure
    supporting Federer 2.10.14, p. 177. This file only seals
    the proved witness; source locators accompany the specification
    and witness declarations. Downstream proofs use the exposed laws. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal.
From Federer Require Import WeightedCountingMeasureUP WeightedCountingMeasureConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type WeightedCountingMeasureSignature.
  (** Source for [value]: sealed weighted numerical-sum witness
      supporting Federer 2.10.14, p. 177; laws precede existence. *)
  Parameter value : forall (R : realType) (X : choiceType),
    (X -> \bar R) -> set X -> \bar R.
  (** Source for [laws]: abstract finite-sum laws of 2.1.1,
      pp. 51–53, for the auxiliary budgets of 2.10.14, p. 177. *)
  Parameter laws : forall (R : realType) (X : choiceType) (w : X -> \bar R),
    is_weighted_counting_measure w (@value R X w).
End WeightedCountingMeasureSignature.
Module WeightedCountingMeasure : WeightedCountingMeasureSignature.
  (** Source for [value]: encapsulated proved numerical-sum
      implementation supporting Federer 2.10.14, p. 177. *)
  Definition value := @weighted_counting_measure_witness.
  (** Source for [laws]: proved laws of the sealed witness,
      supporting the jump budgets in Federer 2.10.14, p. 177. *)
  Definition laws := @weighted_counting_measure_witness_laws.
End WeightedCountingMeasure.
