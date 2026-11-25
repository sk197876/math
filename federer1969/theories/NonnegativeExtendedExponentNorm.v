(** Public integral-root and essential-bound laws for the nonnegative
    extended-input norm in Federer (1969), 2.10.5, p. 172. All consequences
    use the sealed specification. Source context and extended-input
    convention: NonnegativeExtendedExponentNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  MeasurableFunctionUP MeasureIntegralUP ExtendedPositivePower
  NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [nonnegative_extended_exponent_norm]:
    public value of the formulas used in Federer
    2.10.5, p. 172, with the construction opaque. *)
Definition nonnegative_extended_exponent_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) (t : \bar R) :=
  NonnegativeExtendedExponentNorm.value mu f t.

(** Source for [nonnegative_extended_exponent_norm_specification]:
    integral-root or essential-bound characterization
    of the numerator in Federer 2.10.5, p. 172. *)
Lemma nonnegative_extended_exponent_norm_specification (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) (t : \bar R) :
  is_measure mu -> (forall x, 0<=f x) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_nonnegative_extended_exponent_norm mu f t (nonnegative_extended_exponent_norm mu f t).
Proof. exact: NonnegativeExtendedExponentNorm.laws. Qed.

(** Source for [nonnegative_extended_exponent_norm_ge0]:
    supporting nonnegativity of the gauge numerator
    in Federer 2.10.5, p. 172. *)
Lemma nonnegative_extended_exponent_norm_ge0 (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> extended_real_line R) (t : \bar R) :
  is_measure mu -> (forall x, 0<=f x) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  0<=nonnegative_extended_exponent_norm mu f t.
Proof.
move=> hm hf0 ht hf.
exact: nonnegative_extended_exponent_norm_nonnegative
  (@nonnegative_extended_exponent_norm_specification R X mu f t hm hf0 ht hf).
Qed.
