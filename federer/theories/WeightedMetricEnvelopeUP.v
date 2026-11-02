(** Federer (1969), 2.10.24, pp. 186–187: define lambda_delta(f) as the
    infimum of weighted covering costs. Cover weights are finite nonnegative
    real numbers on a countable generator family; their pointwise sum
    dominates the nonnegative extended-real function f almost everywhere for
    the final measure. These abstract infimum laws precede existence and
    sealing. The definition is meaningful independently of the later
    equality hypotheses. no matching weighted-infimum item was located. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MetricDiameter MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_generator_sum]: direct sum
    over generators containing x in 2.10.24,
    p. 186, second display. Only active members
    of G contribute; the weights remain real-valued. *)
Definition weighted_generator_sum (R : realType) (X J : choiceType)
    (S : J -> set X) (G : set J) (u : J -> R) (x : X) :=
  nonnegative_sum [set j | G j /\ S j x] (fun j=>(u j)%:E).

(** Source for [weighted_generator_cost]: direct weighted
    total cost in 2.10.24, p. 186,
    first display. Extended multiplication retains the
    project's nonnegative convention zero times infinity zero. *)
Definition weighted_generator_cost (R : realType) (J : choiceType)
    (c : J -> \bar R) (G : set J) (u : J -> R) :=
  nonnegative_sum G (fun j=>(u j)%:E*c j).

(** Source for [is_weighted_metric_cover]: direct
    admissibility conditions for lambda_delta(f) in
    2.10.24, p. 186. An indexed generator
    family records F, and weights are totalised
    outside G without imposing conditions there. *)
Record is_weighted_metric_cover (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (psi : set X -> \bar R) (delta : \bar R)
    (f : X -> \bar R) (G : set J) (u : J -> R) : Prop := {
  (** Source for [weighted_metric_cover_countable]: direct
      countability condition in 2.10.24, p. 186. *)
  weighted_metric_cover_countable : countable G;
  (** Source for [weighted_metric_cover_nonnegative]: direct
      finite nonnegative real weight condition in
      2.10.24, p. 186. *)
  weighted_metric_cover_nonnegative : forall j, G j -> (0<=u j)%R;
  (** Source for [weighted_metric_cover_diameter]: direct
      diameter restriction in 2.10.24, p. 186. *)
  weighted_metric_cover_diameter : forall j, G j -> extended_metric_diameter (S j)<=delta;
  (** Source for [weighted_metric_cover_dominates]: direct
      almost-everywhere domination requirement in
      2.10.24, p. 186, second display. *)
  weighted_metric_cover_dominates : measure_almost_everywhere psi [set x | f x<=weighted_generator_sum S G u x]
}.

(** Source for [is_weighted_metric_envelope]: direct
    greatest-lower-bound specification of lambda_delta
    in 2.10.24, p. 186. Nonnegativity of f
    and positivity of delta are standing hypotheses
    of the printed application, separate from the infimum laws. *)
Record is_weighted_metric_envelope (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R)
    (lambda : (X -> \bar R) -> \bar R) : Prop := {
  (** Source for [weighted_metric_envelope_lower]: each
      admissible weighted covering cost bounds lambda,
      2.10.24, p. 186. *)
  weighted_metric_envelope_lower : forall f G u,
    is_weighted_metric_cover S psi delta f G u -> lambda f<=weighted_generator_cost c G u;
  (** Source for [weighted_metric_envelope_greatest]: greatest
      lower bound of admissible weighted covering costs,
      2.10.24, p. 186. *)
  weighted_metric_envelope_greatest : forall f b,
    (forall G u, is_weighted_metric_cover S psi delta f G u -> b<=weighted_generator_cost c G u) -> b<=lambda f
}.
