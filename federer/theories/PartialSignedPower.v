(** Federer (1969), 2.4.14, p. 88: the two signed-power functions in
    Holder's equality condition. The operations below keep exact partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionPostcomposition SignedRealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_signed_real_power]: the function
    |f|^p sign f in Federer 2.4.14, p. 88;
    no value is assigned outside f's domain. *)
Definition partial_signed_real_power (R : realType) (X : Type) (p : R)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  partial_function_postcompose f (fun x => (signed_real_power p x : R)).

(** Source for [partial_signed_power_dependence_locus]: supporting pointwise
    relation in the equality condition of Federer 2.4.14, p. 88 The scalar
    coefficient is global when this locus is asserted to be conull. Both
    original values must exist. *)
Definition partial_signed_power_dependence_locus (R : realType) (X : Type) (p q c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  [set x | exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\
    signed_real_power p a = c * signed_real_power q b].
