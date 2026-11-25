(** Private witness for the integral map in Federer (1969), 2.5.1, p. 92.
    The already specified lower integral is finite on L; its real value
    furnishes a witness. Downstream arguments use only the sealed functional
    specification. Source conventions: RealIntegralFunctionalUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureIntegralBounds MeasureIntegralUniqueness SummableRealFunctionUP RealIntegralFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_integral_functional_exists]: existence of the integral
    assignment in Federer 2.5.1, p. 92 This private construction does not
    prescribe mathematically relevant values outside L. *)
Lemma real_integral_functional_exists (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) :
  L `<=` summable_real_functions mu -> exists A, is_real_integral_functional mu L A.
Proof.
move=> hL; exists (fun f => fine (measure_lower_integral mu (real_total_integrand f)))=> f hf.
have [a ha] := hL f hf.
have he := measure_lower_integral_unique (measure_lower_integral_specification mu _) ha.2.2.
by rewrite he.
Qed.
