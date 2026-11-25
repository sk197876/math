(** Federer (1969), 2.5.1, pp. 91–92: the lattice of summable total
    real-valued functions. Total finite values distinguish this lattice from
    the earlier partial-function integration domain. The definition uses the
    existing abstract integral specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureStepIntegralIdentification MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_integrand]: the real-valued total functions of
    Federer 2.5.1, p. 91, viewed in the existing extended-real integral
    theory *)
Definition real_total_integrand (R : realType) (X : Type) (f : X -> R) :=
  partial_real_function_embed (partial_function_total (f : X -> real_line_metric R)).

(** Source for [summable_real_functions]: direct summable-function example
    in Federer 2.5.1, p. 91 The lattice laws are proved separately. *)
Definition summable_real_functions (R : realType) (X : choiceType) (mu : set X -> \bar R) :=
  [set f : X -> R | is_measure_summable mu (real_total_integrand f)].

(** Source for [real_total_integrand_graph]: supporting exact graph
    identification for the integral in Federer 2.5.1, p. 92 No null
    extension is needed because these functions are total. *)
Lemma real_total_integrand_graph (R : realType) (X : Type) (f : X -> R) x y :
  partial_function_graph (real_total_integrand f) x y <-> (f x)%:E=y.
Proof.
split; first by move=> [a [ha he]]; rewrite (ha : f x=a).
by move=> he; exists (f x); split.
Qed.
