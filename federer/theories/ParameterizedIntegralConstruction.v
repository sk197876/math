(** Federer (1969), 2.6.2(4), p. 115: existence of the partial
    inner-integral function. Integral uniqueness makes the defining relation
    single valued. This private witness supports the abstract graph
    specification; downstream proofs use only the sealed laws. Source
    context and domain convention: ParameterizedIntegralUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP
  MeasureIntegralUniqueness ParameterizedIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [parameterized_integral_exists]: supporting
    existence of the inner-integral function in Federer 2.6.2(4),
    p. 115, from uniqueness of the integral in 2.4.2, p. 81. *)
Theorem parameterized_integral_exists (R : realType) (X : Type) (Y : choiceType)
    (mu : set Y -> \bar R) (f : X -> partial_function Y (extended_real_line R)) :
  exists g, is_parameterized_integral mu f g.
Proof.
have hs : forall x a b, is_measure_integral mu (f x) a -> is_measure_integral mu (f x) b -> a = b.
  move=> x a b; exact: measure_integral_unique.
exists (@Build_partial_function X (extended_real_line R)
  (fun x a => is_measure_integral mu (f x) a) hs).
by move=> x a.
Qed.
