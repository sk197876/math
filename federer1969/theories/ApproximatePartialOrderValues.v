(** Federer (1969), 3.1.4, p. 214: upper and lower approximate
    coordinate quotients describe the exact graph and domain of ap D_i f.
    This file uses only the sealed derivative's public graph law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanLebesgueDimensions RealMetricBackground RealNormUP NormMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialFunctionPostcomposition PartialProductSections CoordinateDifferenceQuotient
  ApproximatePartialDerivative ApproximatePartialOrderGraphs EuclideanApproximateRealOrder
  MeasureApproximateOrderLimits CenteredBallRelations ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ScalarOrderValues.
Variable R : realType.
Variable n : nat.
Variable i : 'I_n.
Variable A : set (R_n R n).
Variable f : R_n R n -> R^o.
Local Notation hN := (scalar_absolute_value_norm R).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R 1)).
Local Notation F := (partial_function_source_restrict A
  (partial_function_total (fun x=>(f x : real_line_metric R)))).
Local Notation Q := (partial_function_postcompose (euclidean_joint_coordinate_quotient i F)
  (fun y : real_line_metric R=>(y%:E : extended_real_line R))).
Local Notation V := (@centered_closed_ball_relation R [the metricType R of E]).

(** Source for [approximate_partial_upper_value]: the function g_i
    explicitly defined at the start of the proof of Federer 3.1.4,
    p. 214. It can take either infinite value outside the derivative
    domain; no default finite derivative is substituted. *)
Definition approximate_partial_upper_value a :=
  measure_approximate_upper_limit (@euclidean_lebesgue_measure R 1) V
    (partial_product_vertical_section Q a) (0 : E).

(** Source for [approximate_partial_lower_value]: the corresponding
    lower limit function in Federer 3.1.4, p. 214, first proof paragraph. *)
Definition approximate_partial_lower_value a :=
  measure_approximate_lower_limit (@euclidean_lebesgue_measure R 1) V
    (partial_product_vertical_section Q a) (0 : E).

(** Source for [approximate_partial_scalar_order_graph]: the finite
    equality test for the approximate partial derivative in Federer
    3.1.4, p. 214. Base-domain membership makes the printed use of
    f(a) explicit, consistently with the definition in 3.1.2. *)
Theorem approximate_partial_scalar_order_graph a c :
  partial_function_graph (approximate_partial_derivative hN A f i) a c <->
  A a /\ approximate_partial_upper_value a=c%:E /\ approximate_partial_lower_value a=c%:E.
Proof.
rewrite approximate_partial_derivative_graph approximate_partial_real_section_limit_iff.
by rewrite euclidean_approximate_real_order_iff.
Qed.

(** Source for [approximate_partial_scalar_order_domain]: the set A_i
    in Federer 3.1.4, p. 214, is the base domain intersected with the
    finite equality locus of its upper and lower approximate quotients. *)
Theorem approximate_partial_scalar_order_domain :
  partial_function_domain (approximate_partial_derivative hN A f i)=
  A `&` [set a | exists c : R, approximate_partial_upper_value a=c%:E /\
    approximate_partial_lower_value a=c%:E].
Proof.
apply/seteqP; split=> a.
- move=> [c hc]; have [ha hv] := (approximate_partial_scalar_order_graph a c).1 hc.
  split=> //; by exists c.
- move=> [ha [c hv]]; exists c; apply: (approximate_partial_scalar_order_graph a c).2.
  by split.
Qed.
End ScalarOrderValues.
