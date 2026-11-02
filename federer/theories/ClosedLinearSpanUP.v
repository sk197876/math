(** Linear topological background for Federer (1969), 2.3.8, p. 78,
    essential separability and additive closure, and 2.3.9, pp. 79–80,
    limits in the same function set. The span is specified by minimality;
    existence constructions must prove these laws. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality reals topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_closed_linear_span]: supporting universal property of the
    closed linear span used in Federer 2.3.8, p. 78 The supplied subspace is
    the least closed subspace containing D. *)
Record is_closed_linear_span (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (D : set (real_norm_metric_space hN)) (Z : subspace V) : Prop := {
  (** Source for [closed_linear_span_closed]: Supporting Federer 2.3.8–2. *)
  closed_linear_span_closed : closed (fun y : real_norm_metric_space hN => Z y);
  (** Source for [closed_linear_span_contains]: the generators
      lie in their span, supporting Federer 2.3.8, p. 78. *)
  closed_linear_span_contains : D `<=` Z;
  (** Source for [closed_linear_span_least]: minimality of the
      supporting closed linear span for Federer 2.3.8, p. 78. *)
  closed_linear_span_least : forall W : subspace V,
    closed (fun y : real_norm_metric_space hN => W y) -> D `<=` W -> Z `<=` W
}.

(** Source for [is_separable_linear_envelope]: supporting existence
    specification for the separable-subspace reduction in Federer
    2.3.8, p. 78. The envelope is closed, separable in its
    induced metric, and contains the supplied set of values. *)
Definition is_separable_linear_envelope (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (A : set (real_norm_metric_space hN)) (Z : subspace V) :=
  closed (fun y : real_norm_metric_space hN => Z y) /\ A `<=` Z /\
  exists D : set (metric_subset (fun y : real_norm_metric_space hN => Z y)),
    countable D /\ dense D.

(** Source for [closed_linear_span_unique_membership]: supporting
    uniqueness from the universal property for Federer 2.3.8,
    p. 78; no chosen construction enters this argument. *)
Lemma closed_linear_span_unique_membership (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (D : set (real_norm_metric_space hN))
    (Z W : subspace V) : is_closed_linear_span D Z -> is_closed_linear_span D W ->
  forall x, Z x <-> W x.
Proof.
move=> hz hw x; split.
- exact: (closed_linear_span_least hz (closed_linear_span_closed hw) (closed_linear_span_contains hw)).
- exact: (closed_linear_span_least hw (closed_linear_span_closed hz) (closed_linear_span_contains hz)).
Qed.
