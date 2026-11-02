(** Federer (1969), 2.4.2, p. 81: upper and lower functions, upper and lower
    integrals, integrability and summability. The function to be integrated
    may take extended real values; its upper and lower approximants are
    real-valued step functions as in 2.4.1. Exact partial domains and
    almost-everywhere inequalities are retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureStepFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_step_upper_locus]: supporting precise
    almost-everywhere inequality u(x)>=f(x) in Federer 2.4.2,
    p. 81; both values must be defined at such a point. *)
Definition partial_step_upper_locus (R : realType) (X : Type)
    (u : partial_function X (real_line_metric R)) (f : partial_function X (extended_real_line R)) :=
  [set x | exists y z, partial_function_graph u x y /\ partial_function_graph f x z /\ z <= y%:E].

(** Source for [partial_step_lower_locus]: supporting precise
    inequality u(x)<=f(x) in Federer 2.4.2, p. 81. *)
Definition partial_step_lower_locus (R : realType) (X : Type)
    (u : partial_function X (real_line_metric R)) (f : partial_function X (extended_real_line R)) :=
  [set x | exists y z, partial_function_graph u x y /\ partial_function_graph f x z /\ y%:E <= z].

(** Source for [is_measure_upper_function]: direct upper-function
    definition of Federer 2.4.2, p. 81. *)
Definition is_measure_upper_function (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) (u : partial_function X (real_line_metric R)) :=
  is_measure_step_function mu u /\ measure_almost_everywhere mu (partial_step_upper_locus u f).

(** Source for [is_measure_lower_function]: direct lower-function
    definition of Federer 2.4.2, p. 81. *)
Definition is_measure_lower_function (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) (u : partial_function X (real_line_metric R)) :=
  is_measure_step_function mu u /\ measure_almost_everywhere mu (partial_step_lower_locus u f).

(** Source for [measure_upper_step_values]: the numbers assigned
    to all upper functions in Federer 2.4.2, p. 81. *)
Definition measure_upper_step_values (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) :=
  [set a | exists u, is_measure_upper_function mu f u /\ is_measure_step_integral mu u a].

(** Source for [measure_lower_step_values]: the numbers assigned
    to all lower functions in Federer 2.4.2, p. 81. *)
Definition measure_lower_step_values (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) :=
  [set a | exists u, is_measure_lower_function mu f u /\ is_measure_step_integral mu u a].

(** Source for [is_measure_upper_integral]: abstract greatest-
    lower-bound specification for the upper integral in Federer
    2.4.2, p. 81; the family may be empty. *)
Definition is_measure_upper_integral (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) a :=
  (forall b, measure_upper_step_values mu f b -> a <= b) /\
  (forall c, (forall b, measure_upper_step_values mu f b -> c <= b) -> c <= a).

(** Source for [is_measure_lower_integral]: abstract least-
    upper-bound specification for the lower integral in Federer
    2.4.2, p. 81; the family may be empty. *)
Definition is_measure_lower_integral (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) a :=
  (forall b, measure_lower_step_values mu f b -> b <= a) /\
  (forall c, (forall b, measure_lower_step_values mu f b -> b <= c) -> a <= c).

(** Source for [is_measure_integral]: direct integral specification
    in Federer 2.4.2, p. 81: measurability and coincident
    upper and lower integrals, with either infinite value permitted. *)
Definition is_measure_integral (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) a :=
  is_measure_measurable_function mu f /\ is_measure_upper_integral mu f a /\ is_measure_lower_integral mu f a.

(** Source for [is_measure_integrable]: direct integrability
    definition of Federer 2.4.2, p. 81. *)
Definition is_measure_integrable (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) := exists a, is_measure_integral mu f a.

(** Source for [is_measure_summable]: direct summability
    definition of Federer 2.4.2, p. 81, final sentence:
    an integrable function whose integral is finite. *)
Definition is_measure_summable (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) := exists a : R, is_measure_integral mu f a%:E.
