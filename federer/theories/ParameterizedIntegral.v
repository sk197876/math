(** Federer (1969), 2.6.2(4), p. 115: public partial inner-integral
    function, accessed only through the opaque specification. Source
    context: ParameterizedIntegralUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP ParameterizedIntegralUP ParameterizedIntegralSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [parameterized_integral]: public inner-integral
    function in Federer 2.6.2(4), p. 115, with
    no values outside the actual integrability domain. *)
Definition parameterized_integral (R : realType) (X : Type) (Y : choiceType)
    (mu : set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :=
  @ParameterizedIntegral.value R X Y mu f.

(** Source for [parameterized_integral_specification]: exposed
    graph laws for the inner integral in Federer 2.6.2(4), p. 115. *)
Lemma parameterized_integral_specification (R : realType) (X : Type) (Y : choiceType)
    (mu : set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :
  is_parameterized_integral mu f (parameterized_integral mu f).
Proof. exact: ParameterizedIntegral.laws. Qed.

(** Source for [parameterized_integral_domain]: exact domain
    of the inner-integral function in Federer 2.6.2(4),
    p. 115: precisely the parameters with an integrable section. *)
Lemma parameterized_integral_domain (R : realType) (X : Type) (Y : choiceType)
    (mu : set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) x :
  partial_function_domain (parameterized_integral mu f) x <-> is_measure_integrable mu (f x).
Proof.
split=> [[a ha]|[a ha]]; exists a.
- exact: (parameterized_integral_specification mu f x a).1 ha.
- exact: (parameterized_integral_specification mu f x a).2 ha.
Qed.
