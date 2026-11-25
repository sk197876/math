(** Federer (1969), 3.1.2, pp. 211–212: approximate differentiability
    replaces the remainder limit by the approximate limit of 2.9.12.
    Quotients retain their actual punctured domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNorm RealMetricBackground EuclideanLebesgueDimensions
  CenteredBallRelations PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureApproximateLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_remainder_quotient]: the first limit in
    Federer 3.1.2, p. 212. It is defined only at x in A with x different
    from a; the norm denominator is then positive. *)
Definition approximate_remainder_quotient (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (A : R_n R n -> Prop) (f : R_n R n -> Y)
    (a : R_n R n) (L : Hom (R_n R n) Y) :
    partial_function (inner_metric_space (@euclidean_inner_productP R n)) (real_line_metric R) :=
  partial_function_source_restrict [set x | A x /\ x != a]
    (partial_function_total (fun x => NY (f x-f a-L (x-a)) /
      inner_norm (@euclidean_inner_productP R n) (x-a))).

(** Source for [has_approximate_differential]: approximate differentiability
    with the candidate linear map L, Federer 3.1.2, p. 212. The point a
    must belong to the actual domain because f(a) occurs in the quotient.
    No neighborhood of a is required to lie in A. *)
Definition has_approximate_differential (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (A : R_n R n -> Prop) (f : R_n R n -> Y)
    (a : R_n R n) (L : Hom (R_n R n) Y) :=
  A a /\ @is_measure_approximate_limit R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R n)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)])
    (approximate_remainder_quotient NY A f a L) a (0 : real_line_metric R).

(** Source for [approximately_differentiable_at]: existence of a linear
    approximate differential, Federer 3.1.2, p. 212, opening definition. *)
Definition approximately_differentiable_at (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (A : R_n R n -> Prop) (f : R_n R n -> Y) (a : R_n R n) :=
  exists L : Hom (R_n R n) Y, has_approximate_differential NY A f a L.

(** Source for [is_approximate_differential_graph]: notation ap Df in
    Federer 3.1.2, p. 212. Its exact partial graph is specified by the
    defining approximation, with no value assigned where it fails. *)
Definition is_approximate_differential_graph (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (A : R_n R n -> Prop) (f : R_n R n -> Y)
    (D : partial_function (R_n R n) (Hom (R_n R n) Y)) :=
  forall a L, partial_function_graph D a L <->
    has_approximate_differential NY A f a L.
