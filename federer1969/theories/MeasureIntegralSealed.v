(** Opaque integral assignment for Federer (1969), 2.4.2, p. 81. It is
    exposed only for a function proved integrable; no default value is
    assigned to nonintegrable functions. Source context:
    MeasureIntegralUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type MeasureIntegralSignature.
(** Source for [value]: integral of an integrable function,
    Federer 2.4.2, p. 81, second defining display. *)
Parameter value : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (f : partial_function X (extended_real_line R)), is_measure_integrable mu f -> \bar R.
(** Source for [laws]: the integral has the common upper/lower
    value prescribed in Federer 2.4.2, p. 81. *)
Parameter laws : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (f : partial_function X (extended_real_line R)) (hf : is_measure_integrable mu f),
  is_measure_integral mu f (@value R X mu f hf).
End MeasureIntegralSignature.
Module MeasureIntegral : MeasureIntegralSignature.
(** Source for [value]: private selection of the value whose
    existence is proved by integrability, Federer 2.4.2, p. 81. *)
Definition value (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (f : partial_function X (extended_real_line R)) (hf : is_measure_integrable mu f) := projT1 (cid hf).
(** Source for [laws]: the selected value satisfies the integral
    specification in Federer 2.4.2, p. 81. *)
Lemma laws (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (f : partial_function X (extended_real_line R)) (hf : is_measure_integrable mu f) :
  is_measure_integral mu f (@value R X mu f hf).
Proof. exact: projT2 (cid hf). Qed.
End MeasureIntegral.
