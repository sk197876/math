(** Federer (1969), 2.5.3, p. 94: approximation of nonnegative summable
    functions by L+ in integral absolute error. This supporting predicate
    concerns total real-valued functions; the final density theorem must
    also retain Federer's partial-domain convention. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [is_positive_lattice_l1_approximable]: Supporting Federer
    2.5.3, p. 94.The approximation property is specified without choosing
    representatives or defining a quotient L1 space. *)
Definition is_positive_lattice_l1_approximable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) (f : X -> R) :=
  summable_real_functions mu f /\ forall d : R, (0 < d)%R ->
    exists (h : X -> R) (e : R), positive_function_lattice L h /\
      is_measure_integral mu (real_total_integrand (fun x => `|h x-f x|%R)) e%:E /\ (e < d)%R.
