(** Federer (1969), 3.1.4, pp. 214–215: the increasing
    measurable sets B(i,j,p) exhaust the scalar approximate-partial
    domain. Closed radius sections give an auxiliary stronger cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric RealNormUP RealMetricBackground EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  ApproximatePartialDerivative ScalarApproximatePartialMeasurable
  CoordinateRemainderSetMeasurable ApproximatePartialRemainderDensity
  EuclideanSmallMassCutoffs MeasureUP MeasureFiniteClosure MeasurableFunctionUP
  MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section UniformCutoffs.
Variable R : realType.
Variable m : nat.
Variable i : 'I_m.
Variables f g : R_n R m -> R^o.
Variables e c : R.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Leb := (@euclidean_lebesgue_measure R m).
Local Notation Ai := (partial_function_domain
  (approximate_partial_derivative (scalar_absolute_value_norm R) setT f i)).

(** Source for [approximate_partial_uniform_cutoff]: B(i,j,p)
    of Federer 3.1.4, p. 214. Taking e=c=1/j and p+1
    as the positive index gives the printed tolerances. Closed scalar
    balls strengthen its auxiliary radius condition. *)
Definition approximate_partial_uniform_cutoff p : set X :=
  Ai `&` euclidean_small_mass_cutoff (coordinate_remainder_exception_set i f g e) c p.

(** Source for [approximate_partial_uniform_cutoff_increasing]:
    monotonicity B(i,j,p) subset B(i,j,p+1), Federer 3.1.4, p. 215. *)
Lemma approximate_partial_uniform_cutoff_increasing p q :
  (p<=q)%N -> approximate_partial_uniform_cutoff p `<=` approximate_partial_uniform_cutoff q.
Proof.
move=> hpq x [hx hb]; split=> //; exact: (@euclidean_small_mass_cutoff_increasing R m 1 (coordinate_remainder_exception_set i f g e) c p q hpq x hb).
Qed.

(** Source for [approximate_partial_uniform_cutoff_measurable]:
    measurability of B(i,j,p), Federer 3.1.4, p. 215,
    from the measurable partial domain and 3.1.3(1). *)
Lemma approximate_partial_uniform_cutoff_measurable p :
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] Leb (partial_function_total f) ->
  @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] Leb (partial_function_total g) ->
  measure_measurable Leb (approximate_partial_uniform_cutoff p).
Proof.
move=> hf hg.
have hfA : @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] Leb
    (partial_function_source_restrict setT (partial_function_total f)).
  apply: (measurable_function_graph_equivalent _ hf)=> x y; by split=> [hy|[_ hy]].
apply: (measure_measurable_intersection (euclidean_lebesgue_is_measure R m)).
- exact: (@approximate_partial_scalar_domain_measurable R m i setT f hfA).
- apply: euclidean_small_mass_cutoff_measurable.
  exact: coordinate_remainder_exception_measurable hf hg.
Qed.

(** Source for [approximate_partial_uniform_cutoffs_exhaust]:
    A_i=union_p B(i,j,p), Federer 3.1.4, p. 215. Only
    agreement of g with the actual partial derivative is used here;
    measurability is supplied separately. *)
Theorem approximate_partial_uniform_cutoffs_exhaust :
  0<e -> 0<c ->
  (forall x v, partial_function_graph
    (approximate_partial_derivative (scalar_absolute_value_norm R) setT f i) x v -> g x=v) ->
  \bigcup_p approximate_partial_uniform_cutoff p=Ai.
Proof.
move=> he hc hg; apply/seteqP; split=> x; first by move=> [p _ [hx _]].
move=> hx; have [v hv] := hx.
have hpartial := (approximate_partial_derivative_graph (scalar_absolute_value_norm R) setT f i x v).1 hv.
have hz := approximate_partial_remainder_density_zero hpartial he.
rewrite -(hg x v hv) in hz.
have [p hp] := euclidean_zero_density_has_small_mass_cutoff
  (S:=coordinate_remainder_exception_set i f g e) hc hz.
exists p=> //; by split.
Qed.
End UniformCutoffs.
