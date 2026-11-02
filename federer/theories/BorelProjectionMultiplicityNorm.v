(** Federer (1969), 2.10.15, p. 178, used in
    3.2.26(3), p. 262: the actual multiplicity profile
    is measurable and its norm is bounded by beta_t I_t.
    The existing shrinking-tree argument also covers degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  EuclideanProjectionMetric OrthogonalProjectionProbability ProjectionBeta
  IntegralGeometricMeasure IntegralGeometricMultiplicity ProjectionMultiplicityIntegral
  NonnegativeExtendedExponentNorm PartialFunctionBasic MeasurableFunctionUP
  ClosedCoverTreeUP CoverPartitionTreeUP ClosedCoverTreeSealed CoverPartitionTreeSealed
  TopologicalBorel MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_projection_multiplicity_norm]: the
    multiplicity norm estimate of 2.10.15, p. 178,
    applied in 3.2.26(3), p. 262. Instantiate the
    already proved shrinking-tree integral and norm bound,
    retaining the empty exterior word in degree zero. *)
Lemma borel_projection_multiplicity_norm (R:realType) n m
    (hmn:(m<=n)%N) (A:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  borel_set A ->1<=t ->
  is_measure_measurable_function (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projection_multiplicity_integral (m:=m) A)) /\
  nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (projection_multiplicity_integral (m:=m) A) t<=
    (@projection_beta R n m hmn t)%:E*@integral_geometric_measure R n m hmn t A.
Proof.
move=>hA ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have [D [hD hDense]]:=euclidean_metric_separable R n.
have hX:(@setT X)!=set0 by exists (0%R:X).
pose E:=@ClosedCoverTree.value R X D hD hDense hX.
pose P:=@CoverPartitionTree.value X E.
have hE:=@ClosedCoverTree.laws R X D hD hDense hX.
have hP:=@CoverPartitionTree.laws X E.
split.
- exact:(@projection_multiplicity_tree_parameter_integral R n m hmn E P A hE hP hA).1.
- exact:(@projection_multiplicity_tree_norm_bound R n m hmn E P A t hE hP hA ht).
Qed.
