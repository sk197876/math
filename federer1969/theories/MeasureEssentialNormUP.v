(** Federer (1969), 2.4.12, p. 86, definition of phi_(infinity) We
    explicitly take the infimum over nonnegative thresholds, including
    infinity. The displayed sources do not specify this range: allowing
    negative thresholds would give minus infinity for every function under
    the zero measure, contradicting the stated seminorm property. This
    boundary clarification is local, not an entry in Federer's erratum. The
    source's partial domains are retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureGauge ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_norm_feasible]: the null
    strict-superlevel thresholds in Federer 2.4.12, p. 86.
    Nonnegativity is explicit to preserve the norm convention
    also for the zero measure; infinity is always admissible. *)
Definition measure_essential_norm_feasible (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) r :=
  0 <= r /\ mu (partial_norm_superlevel N f r) = 0.

(** Source for [is_measure_essential_norm]: abstract infimum specification
    of phi_(infinity) in Federer 2.4.12, p. 86 The value is characterised by
    its order laws. *)
Definition is_measure_essential_norm (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) a :=
  (forall r, measure_essential_norm_feasible mu N f r -> a <= r) /\
  (forall b, (forall r, measure_essential_norm_feasible mu N f r -> b <= r) -> b <= a).
