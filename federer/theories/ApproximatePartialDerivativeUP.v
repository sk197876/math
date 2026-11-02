(** Federer (1969), 3.1.2, p. 212: approximate partial derivatives
    use scalar Lebesgue approximate limits of coordinate-line quotients. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates RealNormUP
  NormMetric RealMetricBackground LebesgueScalarMeasure CenteredBallRelations
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureApproximateLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_partial_quotient]: last display in Federer
    3.1.2, p. 212. Its domain consists of nonzero scalar increments
    whose coordinate-line points belong to the actual domain of f. *)
Definition approximate_partial_quotient (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (a : R_n R n) (i : 'I_n) :
    partial_function (real_line_metric R) (real_norm_metric_space hNY) :=
  partial_function_source_restrict
    [set t | t != 0 /\ A (a+t*:(@coordinate_basis R n i))]
    (partial_function_total (fun t => t^-1*:(f (a+t*:(@coordinate_basis R n i))-f a))).

(** Source for [has_approximate_partial_derivative]: the approximate
    partial derivative ap D_i f(a) in Federer 3.1.2, p. 212. The
    base point belongs to the actual domain, and the quotient converges
    approximately with respect to scalar Lebesgue measure. *)
Definition has_approximate_partial_derivative (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (a : R_n R n) (i : 'I_n) (v : Y) :=
  A a /\ @is_measure_approximate_limit R
    [the metricType R of real_line_metric R]
    [the topologicalType of real_norm_metric_space hNY] (@lebesgue_scalar_measure R)
    (@centered_closed_ball_relation R [the metricType R of real_line_metric R])
    (approximate_partial_quotient hNY A f a i) (0 : real_line_metric R) v.

(** Source for [is_approximate_partial_derivative_graph]: exact partial
    graph specification of ap D_i f in Federer 3.1.2, p. 212. *)
Definition is_approximate_partial_derivative_graph (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (i : 'I_n) (D : partial_function (R_n R n) Y) :=
  forall a v, partial_function_graph D a v <->
    has_approximate_partial_derivative hNY A f a i v.
