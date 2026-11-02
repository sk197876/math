(** Federer (1969), 2.5.16, p. 110: "for any metric space Y we can consider
    the Banach space E of all bounded real valued continuous functions on Y
    with the norm nu(f) = sup im |f| whenever f in E". This specification
    describes E through its evaluation map: evaluation preserves the vector
    operations, identifies the vectors, and represents precisely the bounded
    continuous real functions on Y; the norm of a vector is the least
    nonnegative bound of the absolute values of its evaluation, the
    specification of sup im |f| already used for 2.5.19, p. 113, which gives
    the value zero when Y is empty. A concrete subtype supplies existence
    separately. The local erratum has no entry for p. 110. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
From Federer Require Import MetricBoundedContinuousEmbedding UniformFunctionNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_bounded_continuous_space]: abstract
    realisation of the space E of all bounded real valued continuous
    functions on Y with the norm nu(f) = sup im |f|, Federer 2.5.16,
    p. 110. *)
Record is_bounded_continuous_space (R : realType) (Y : metricType R)
    (V : lmodType R) (ev : V -> Y -> R) (N : V -> R) : Prop := {
  (** Source for [bounded_continuous_evaluation_linear]: the vector
      operations of E are pointwise, Federer 2.5.16, p. 110. *)
  bounded_continuous_evaluation_linear : forall c u v y, ev (c *: u + v) y = c * ev u y + ev v y;
  (** Source for [bounded_continuous_evaluation_member]: the members
      of E are bounded continuous real valued functions on Y, Federer
      2.5.16, p. 110. *)
  bounded_continuous_evaluation_member : forall v, bounded_continuous_functions (ev v);
  (** Source for [bounded_continuous_evaluation_injective]: a member
      of E is determined by its values, Federer 2.5.16, p. 110. *)
  bounded_continuous_evaluation_injective : injective ev;
  (** Source for [bounded_continuous_evaluation_surjective]: E
      contains all bounded real valued continuous functions on Y,
      Federer 2.5.16, p. 110. *)
  bounded_continuous_evaluation_surjective : forall f, bounded_continuous_functions f ->
    exists v, ev v = f;
  (** Source for [bounded_continuous_norm_supremum]: the norm
      nu(f) = sup im |f| of Federer 2.5.16, p. 110, by its
      least-bound specification. *)
  bounded_continuous_norm_supremum : forall v, is_uniform_function_norm (ev v) (N v)
}.
