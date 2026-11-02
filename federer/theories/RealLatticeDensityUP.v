(** Federer (1969), 2.5.9, p. 100: a measurable density represents the given
    functional on the original lattice. The specification below imposes
    neither an essential bound nor countable support; those belong to
    conclusions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasurableFunctionUP
  TotalScalarLpUP MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_real_lattice_density]: direct integral formula
    and measurability in Federer 2.5.9, p. 100.
    Every product must have the stated finite integral; a totalized
    integral value alone does not satisfy this specification. *)
Definition is_real_lattice_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) (A : (X -> R) -> R) (k : X -> R) :=
  is_measure_measurable_function mu (total_scalar_function k) /\
  forall f, L f -> is_measure_integral mu (real_total_integrand (fun x => (f x*k x)%R)) (A f)%:E.
