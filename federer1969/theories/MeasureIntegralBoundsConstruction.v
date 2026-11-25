(** Existence of the upper and lower integral values in Federer (1969),
    2.4.2, p. 81, from the abstract complete extended-real order developed
    in 2.1.1. Source context: MeasureIntegralUP.v. No integral theorem is
    imported. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBounds PartialFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_integral_bounds_exist]: existence of the
    two extremal values in Federer 2.4.2, p. 81, even
    when one or both approximating families are empty. *)
Theorem measure_integral_bounds_exist (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) :
  exists p : \bar R * \bar R, is_measure_upper_integral mu f p.1 /\ is_measure_lower_integral mu f p.2.
Proof.
exists (extended_real_inf (measure_upper_step_values mu f), extended_real_sup (measure_lower_step_values mu f)).
split; split.
- exact: extended_real_inf_lower.
- exact: extended_real_inf_greatest.
- exact: extended_real_sup_upper.
- exact: extended_real_sup_least.
Qed.
