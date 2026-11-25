(** Opaque upper/lower integral interface for Federer (1969), 2.4.2, p. 81.
    Source context: MeasureIntegralUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP MeasureIntegralBoundsConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type MeasureIntegralBoundsSignature.
(** Source for [value]: abstract upper/lower values defined in
    Federer 2.4.2, p. 81. *)
Parameter value : forall (R : realType) (X : choiceType), (set X -> \bar R) ->
  partial_function X (extended_real_line R) -> \bar R * \bar R.
(** Source for [laws]: greatest-lower-bound and least-upper-bound
    laws for the two integrals in Federer 2.4.2, p. 81. *)
Parameter laws : forall (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (f : partial_function X (extended_real_line R)),
  is_measure_upper_integral mu f (@value R X mu f).1 /\ is_measure_lower_integral mu f (@value R X mu f).2.
End MeasureIntegralBoundsSignature.
Module MeasureIntegralBounds : MeasureIntegralBoundsSignature.
(** Source for [value]: private selection of the proved integral
    bounds from Federer 2.4.2, p. 81. *)
Definition value (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (f : partial_function X (extended_real_line R)) := projT1 (cid (@measure_integral_bounds_exist R X mu f)).
(** Source for [laws]: the selected values satisfy the abstract
    specifications in Federer 2.4.2, p. 81. *)
Lemma laws (R : realType) (X : choiceType) (mu : set X -> \bar R)
  (f : partial_function X (extended_real_line R)) :
  is_measure_upper_integral mu f (@value R X mu f).1 /\ is_measure_lower_integral mu f (@value R X mu f).2.
Proof. exact: projT2 (cid (@measure_integral_bounds_exist R X mu f)). Qed.
End MeasureIntegralBounds.
