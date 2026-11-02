(** Federer (1969), 3.1.4, p. 214: reduction of approximate partial
    derivatives to scalar target coordinates. This file treats nonempty
    target-coordinate families; the empty target is handled separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  HilbertFormCompactness InnerMetric RealNormUP NormMetric RealMetricBackground
  LebesgueScalarMeasure CenteredBallRelations PartialFunctionUP PartialFunctionPostcomposition
  MeasureApproximateLimitUP ApproximateLimitGraphEquivalence ApproximatePartialDerivativeUP
  ApproximatePartialDerivative ScalarSourceEuclideanApproximateCoordinates
  ScalarApproximateTargetTopology InnerApproximateTargetTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Coordinates.
Variable R : realType.
Variables m n : nat.
Variable A : set (R_n R m).
Variable f : R_n R m -> R_n R n.+1.
Variable a : R_n R m.
Variable i : 'I_m.
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation hS := (scalar_absolute_value_norm R).
Local Notation Q := (approximate_partial_quotient hN A f a i).
Local Notation QS j := (approximate_partial_quotient hS A (fun x=>f x j) a i).

(** Source for [approximate_partial_coordinate_quotient_graph]:
    coordinate evaluation commutes with the punctured quotient in
    Federer 3.1.2, p. 212, used in the reduction of 3.1.4, p. 214. *)
Lemma approximate_partial_coordinate_quotient_graph j t z :
  partial_function_graph (partial_function_postcompose Q
    (fun v=>(v j : real_line_metric R))) t z <->
  partial_function_graph (partial_function_postcompose (QS j)
    (fun v=>(v : real_line_metric R))) t z.
Proof.
split.
- move=> [v [[ht <-] <-]].
  exists (t^-1*(f (a+t*:(@coordinate_basis R m i)) j-f a j)); split.
  + by split.
  + by rewrite !ffunE.
- move=> [v [[ht <-] <-]].
  exists (t^-1*:(f (a+t*:(@coordinate_basis R m i))-f a)); split.
  + by split.
  + by rewrite !ffunE.
Qed.

(** Source for [approximate_partial_positive_target_coordinates]:
    the scalar reduction in Federer 3.1.4, p. 214. The value of
    the vector partial derivative is determined by all scalar partials,
    on precisely the original coordinate-line domain. *)
Theorem approximate_partial_positive_target_coordinates (v : R_n R n.+1) :
  has_approximate_partial_derivative hN A f a i v <->
  forall j : 'I_n.+1,
    has_approximate_partial_derivative hS A (fun x=>f x j) a i (v j).
Proof.
rewrite /has_approximate_partial_derivative inner_norm_approximate_limit_iff
  scalar_source_euclidean_approximate_coordinates.
split.
- move=> [ha hv] j; split=> //.
  apply: (scalar_norm_approximate_limit_iff _ _ _ _ _).2.
  exact: (approximate_limit_graph_equivalent
    (approximate_partial_coordinate_quotient_graph j) (hv j)).
- move=> hc; split; first exact: (hc ord0).1.
  move=> j.
  have hh := (scalar_norm_approximate_limit_iff _ _ _ _ _).1 (hc j).2.
  apply: (approximate_limit_graph_equivalent _ hh)=> t z.
  exact: iff_sym (approximate_partial_coordinate_quotient_graph j t z).
Qed.
End Coordinates.
