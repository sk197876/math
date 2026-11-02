(** Federer (1969), 2.4.10, p. 85, first definition: an integral over A is
    the integral of f_A. We retain abstract value specifications and require
    proved integrability for a signed integral getter. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_subset_integral]: abstract value
    specification of the subset integral in Federer 2.4.10,
    p. 85, using the existing integral laws for f_A. *)
Definition is_measure_subset_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) (f : partial_function X (extended_real_line R)) a :=
  is_measure_integral mu (partial_function_zero_extension (0 : extended_real_line R) A f) a.

(** Source for [is_measure_subset_integrable]: existence of the subset
    integral in Federer 2.4.10, p. 85 *)
Definition is_measure_subset_integrable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) (f : partial_function X (extended_real_line R)) :=
  is_measure_integrable mu (partial_function_zero_extension (0 : extended_real_line R) A f).

(** Source for [measure_subset_upper_integral]: upper integral over A in
    Federer 2.4.10, p. 85, including its use in the density measure *)
Definition measure_subset_upper_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) (f : partial_function X (extended_real_line R)) :=
  measure_upper_integral mu (partial_function_zero_extension (0 : extended_real_line R) A f).

(** Source for [measure_subset_lower_integral]: Supporting definition for
    Federer 2.4.10, p. 85: the lower integral over A is the lower integral
    of the zero extension f_A. *)
Definition measure_subset_lower_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) (f : partial_function X (extended_real_line R)) :=
  measure_lower_integral mu (partial_function_zero_extension (0 : extended_real_line R) A f).

(** Source for [measure_subset_integral]: public integral over
    A in Federer 2.4.10, p. 85; a proof of
    integrability is required, so undefined signed differences
    are not assigned default values. *)
Definition measure_subset_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) (f : partial_function X (extended_real_line R))
    (hf : is_measure_subset_integrable mu A f) := measure_integral hf.

(** Source for [measure_subset_integral_laws]: defining laws
    of the subset integral getter in Federer 2.4.10, p. 85. *)
Lemma measure_subset_integral_laws (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) (f : partial_function X (extended_real_line R))
    (hf : is_measure_subset_integrable mu A f) :
  is_measure_subset_integral mu A f (measure_subset_integral hf).
Proof. exact: measure_integral_specification. Qed.
