(** Federer (1969), 3.1.4, p. 214: measurable approximate partial
    derivatives with a positive-dimensional Euclidean target, reduced
    to the proved scalar statements. Original partial domains are kept. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  HilbertFormCompactness InnerMetric RealNormUP NormMetric RealMetricBackground
  EuclideanCoordinateTopology EuclideanLebesgueDimensions PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialFunctionPostcomposition PartialZeroExtension
  ApproximatePartialDerivative ApproximatePartialCoordinates ScalarApproximatePartialMeasurable
  ScalarApproximateTargetTopology ScalarNormExtendedEmbedding
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureCountableClosure
  MeasurableFunctionUP MeasurablePostcomposition BorelFunctionBasic MeasurableGraphEquivalence
  MeasurableEuclideanCoordinates RestrictedFunctionMeasurability MeasurableConullSourceRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section PositiveTarget.
Variable R : realType.
Variables m n : nat.
Variable A : set (R_n R m).
Variable f : R_n R m -> R_n R n.+1.
Variable i : 'I_m.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n.+1)).
Local Notation Leb := (@euclidean_lebesgue_measure R m).
Local Notation hm := (euclidean_lebesgue_is_measure R m).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n.+1)).
Local Notation hS := (scalar_absolute_value_norm R).
Local Notation D := (approximate_partial_derivative hN A f i).
Local Notation Dj j := (approximate_partial_derivative hS A (fun x=>f x j) i).
Hypothesis hf : @is_measure_measurable_function R [the choiceType of X]
  [the topologicalType of Y] Leb (partial_function_source_restrict A (partial_function_total f)).

(** Source for [approximate_partial_scalar_component_measurable]:
    scalar reduction of the input in Federer 3.1.4, p. 214,
    by continuous coordinate projections and 2.3.2(4). *)
Lemma approximate_partial_scalar_component_measurable j :
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] Leb
    (partial_function_source_restrict A (partial_function_total (fun x=>f x j))).
Proof.
have hh := measurable_function_borel_postcomposition hm hf
  (continuous_borel_function (@euclidean_coordinate_continuous R n.+1 j)).
apply: (measurable_function_graph_equivalent _ hh)=> x y.
split; first by move=> [v [[ha <-] <-]].
by move=> [ha <-]; exists (f x); split=> //; split.
Qed.

(** Source for [approximate_partial_positive_target_domain]:
    the scalar reduction of A_i in Federer 3.1.4, p. 214.
    A vector partial exists exactly when all its scalar coordinates
    exist. The target dimension is explicitly positive. *)
Theorem approximate_partial_positive_target_domain :
  partial_function_domain D=\bigcap_j partial_function_domain (Dj j).
Proof.
apply/seteqP; split=> a.
- move=> [v hv] j _; exists (v j).
  apply: (approximate_partial_derivative_graph hS A _ i a (v j)).2.
  apply: (approximate_partial_positive_target_coordinates _ _ _ _ _).1 _ j.
  exact: (approximate_partial_derivative_graph hN A f i a v).1 hv.
- move=> ha.
  have hc : forall j, exists c, partial_function_graph (Dj j) a c.
    by move=> j; exact: ha j Logic.I.
  have [v hv] := choice hc.
  exists [ffun j=>v j].
  apply: (approximate_partial_derivative_graph hN A f i a _).2.
  apply: (approximate_partial_positive_target_coordinates _ _ _ _ _).2=> j.
  rewrite ffunE; exact: (approximate_partial_derivative_graph hS A _ i a _).1 (hv j).
Qed.

(** Source for [approximate_partial_positive_target_domain_measurable]:
    the first conclusion of Federer 3.1.4, p. 214, for every
    positive-dimensional target. It is a finite measurable intersection. *)
Theorem approximate_partial_positive_target_domain_measurable :
  measure_measurable Leb (partial_function_domain D).
Proof.
rewrite approximate_partial_positive_target_domain.
apply: (measure_measurable_countable_intersection hm); first exact: countableP.
move=> j _; exact: approximate_partial_scalar_domain_measurable
  (approximate_partial_scalar_component_measurable j).
Qed.

(** Source for [approximate_partial_positive_target_measurable]:
    the second conclusion of Federer 3.1.4, p. 214. Each scalar
    partial is restricted to the common derivative domain. Auxiliary
    zero extensions occur only outside that scalar partial's domain. *)
Theorem approximate_partial_positive_target_measurable :
  @is_measure_measurable_function R [the choiceType of X] [the topologicalType of Y]
    (measure_restrict Leb (partial_function_domain D)) D.
Proof.
pose Ai := partial_function_domain D.
pose mu := measure_restrict Leb Ai.
pose hmu := measure_restrict_is_measure hm Ai.
have hd : measure_almost_everywhere mu Ai.
  change (Leb (Ai `&` (~` Ai))=0%E); rewrite setICr; exact: measure_empty hm.
apply: (measurable_euclidean_coordinate_criterion hmu hd).2=> j.
have hfj := approximate_partial_scalar_component_measurable j.
have hAj := @approximate_partial_scalar_domain_measurable R m i A (fun x=>f x j) hfj.
have hDj := @approximate_partial_scalar_measurable R m i A (fun x=>f x j) hfj.
pose Z := partial_function_zero_extension (0 : real_norm_metric_space hS)
  (partial_function_domain (Dj j)) (Dj j).
have hZ := restricted_measurable_zero_extension hm (0 : real_norm_metric_space hS) hAj hDj.
have hZr := measurable_function_borel_postcomposition hm hZ
  (continuous_borel_function (@scalar_norm_real_identity_continuous R)).
have hZmu := measurable_function_for_restricted_measure hm Ai hZr.
have hres := measurable_conull_source_restriction hmu hd hZmu.
apply: (measurable_function_graph_equivalent _ hres)=> a c.
split.
- move=> [ha [b [hb <-]]].
  have [v hv] := ha.
  have hvj : partial_function_graph (Dj j) a (v j).
    apply: (approximate_partial_derivative_graph hS A _ i a _).2.
    exact: (@approximate_partial_positive_target_coordinates R m n A f a i v).1
      ((approximate_partial_derivative_graph hN A f i a v).1 hv) j.
  have haj : partial_function_domain (Dj j) a by exists (v j).
  have hbD := (@partial_function_zero_extension_on (R_n R m) (real_norm_metric_space hS) 0
    (partial_function_domain (Dj j)) (Dj j) a b haj).1 hb.
  exists v; split=> //; exact: partial_function_single_valued hvj hbD.
- move=> [v [hv <-]].
  have hvj : partial_function_graph (Dj j) a (v j).
    apply: (approximate_partial_derivative_graph hS A _ i a _).2.
    exact: (@approximate_partial_positive_target_coordinates R m n A f a i v).1
      ((approximate_partial_derivative_graph hN A f i a v).1 hv) j.
  split; first by exists v.
  exists (v j); split=> //; apply: (@partial_function_zero_extension_on (R_n R m) (real_norm_metric_space hS) 0 (partial_function_domain (Dj j)) (Dj j) a (v j) _).2=> //.
  by exists (v j).
Qed.
End PositiveTarget.
