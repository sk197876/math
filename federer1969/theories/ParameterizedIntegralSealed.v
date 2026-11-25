(** Opaque witness interface for the partial inner integral in Federer
    (1969), 2.6.2(4), p. 115. Source context and precise domain convention:
    ParameterizedIntegralUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP ParameterizedIntegralUP ParameterizedIntegralConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ParameterizedIntegralSignature.
(** Source for [value]: abstract inner-integral function in
    Federer 2.6.2(4), p. 115. *)
Parameter value : forall (R : realType) (X : Type) (Y : choiceType),
  (set Y -> \bar R) -> (X -> partial_function Y (extended_real_line R)) -> partial_function X (extended_real_line R).
(** Source for [laws]: exact integrability-domain and integral-
    value laws for Federer 2.6.2(4), p. 115. *)
Parameter laws : forall (R : realType) (X : Type) (Y : choiceType)
  (mu : set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)),
  is_parameterized_integral mu f (@value R X Y mu f).
End ParameterizedIntegralSignature.
Module ParameterizedIntegral : ParameterizedIntegralSignature.
(** Source for [value]: private choice of the proved inner-
    integral witness supporting Federer 2.6.2(4), p. 115. *)
Definition value (R : realType) (X : Type) (Y : choiceType)
    (mu : set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :=
  projT1 (cid (@parameterized_integral_exists R X Y mu f)).
(** Source for [laws]: the chosen witness satisfies the
    abstract specification for Federer 2.6.2(4), p. 115. *)
Lemma laws (R : realType) (X : Type) (Y : choiceType)
    (mu : set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :
  is_parameterized_integral mu f (@value R X Y mu f).
Proof. exact: projT2 (cid (@parameterized_integral_exists R X Y mu f)). Qed.
End ParameterizedIntegral.
