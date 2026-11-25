(** Federer (1969), 2.9.22, p. 167: the bounded measurable field v(x)
    representing the scalar derivatives in the Lipschitz case. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  PartialFunctionBasic MeasureAlmostUP MeasurableFunctionUP ReflexiveLipschitzWeakDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_bounded_weak_derivative_field]: supporting
    specification of v in Federer 2.9.22, p. 167, from
    its dual definition through measurability and the bound.
    Norm differentiability of g is a subsequent theorem,
    rather than a field in this intermediate specification. *)
Record is_bounded_weak_derivative_field (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (ed : Hom D (Hom E R^o))
    (mu : set (real_line_metric R) -> \bar R) (g v : R -> E) (L : R) : Prop := {
  (** Source for [bounded_weak_field_bound]: the bound
      |v(x)|<=Lip(g), Federer 2.9.22, p. 167.
      A bounded representative is supplied even off the conull set. *)
  bounded_weak_field_bound : forall x, N (v x)<=L;
  (** Source for [bounded_weak_field_scalar_derivatives]: the
      simultaneous dual identity in Federer 2.9.22, p. 167.
      One conull set works for every continuous functional. *)
  bounded_weak_field_scalar_derivatives : measure_almost_everywhere mu
    (fun x => is_weak_normed_curve_derivative ed g x (v x));
  (** Source for [bounded_weak_field_measurable]: measurability
      of v used before the vector integral in Federer 2.9.22, p. 167. *)
  bounded_weak_field_measurable : is_measure_measurable_function mu
    (partial_function_total (v : real_line_metric R -> real_norm_metric_space hN))
}.
