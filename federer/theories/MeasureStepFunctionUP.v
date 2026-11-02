(** Federer (1969), 2.4.1, pp. 80–81: step functions have countable real
    range and a defined extended numerical sum of value times fibre measure.
    The sum need not be finite; positive or negative infinity is permitted,
    but an undefined difference of infinite variations is excluded. The
    multiplication convention is 0 times infinity equals 0. Partial domains
    remain explicit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureUP MeasurableFunctionUP NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_function_range]: supporting set-theoretic
    image of a partial function in Federer 2.4.1, p. 80. *)
Definition partial_function_range (X Y : Type) (f : partial_function X Y) : set Y :=
  [set y | exists x, partial_function_graph f x y].

(** Source for [is_measure_step_integral]: the numerical sum in
    Federer 2.4.1, p. 80, with its definedness recorded
    as a predicate rather than a default for undefined sums. *)
Definition is_measure_step_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (u : partial_function X (real_line_metric R)) (z : \bar R) :=
  numerical_sum setT (fun y : R => y%:E * mu (partial_function_preimage u [set y])) = Some z.

(** Source for [is_measure_step_function]: direct step-function definition
    in Federer 2.4.1, p. 80 The range is countable, not necessarily finite,
    and the numerical sum may be infinite. *)
Record is_measure_step_function (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (u : partial_function X (real_line_metric R)) : Prop := {
  (** Source for [step_function_measurable]: measurability clause
      of Federer 2.4.1, p. 80, including the conull domain. *)
  step_function_measurable : is_measure_measurable_function mu u;
  (** Source for [step_function_countable_range]: countable real
      image clause of Federer 2.4.1, p. 80. *)
  step_function_countable_range : countable (partial_function_range u);
  (** Source for [step_function_sum_defined]: existence of the
      extended numerical sum in Federer 2.4.1, p. 80. *)
  step_function_sum_defined : exists z, is_measure_step_integral mu u z
}.

(** Source for [measure_step_integral_unique]: supporting
    uniqueness of the assigned sum in Federer 2.4.1, p. 80. *)
Lemma measure_step_integral_unique (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (u : partial_function X (real_line_metric R)) a b :
  is_measure_step_integral mu u a -> is_measure_step_integral mu u b -> a=b.
Proof. move=> ha hb; by move: hb; rewrite /is_measure_step_integral ha=> -[]. Qed.
