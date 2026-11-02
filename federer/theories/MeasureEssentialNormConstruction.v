(** Private existence proof for the infimum in Federer (1969), 2.4.12, p.
    86. The already proved completeness of the extended reals supplies the
    witness. Source context and threshold convention:
    MeasureEssentialNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureEssentialNormUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_norm_exists]: existence of
    the defining infimum in Federer 2.4.12, p. 86,
    by extended-real completeness in 2.1.1, p. 51. *)
Theorem measure_essential_norm_exists (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :
  exists a, is_measure_essential_norm mu N f a.
Proof.
exists (extended_real_inf (measure_essential_norm_feasible mu N f)); split.
- exact: extended_real_inf_lower.
- exact: extended_real_inf_greatest.
Qed.
