(** Supporting the projection averages in Federer (1969), 2.10.16, p. 178:
    continuously parametrise the projection and integrate its actual
    Lebesgue multiplicity integral. Joint counting measurability is proved
    before Fubini, so no composition rule for an arbitrary
    completed-measurable function is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanLebesgueDimensions EuclideanLebesgueHaar ProjectionJointMultiplicity
  ProjectionJointMultiplicityIntegral ProjectionMultiplicityIntegral ProjectionMultiplicityPrecomposition
  TopologicalBorel BorelRegularMeasureUP ProductMeasure ProductBorelRegularity
  CountableOpenBaseUP ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  PartialProductSections MeasureUP MeasureBasic MeasureSplit MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness MeasurableFunctionUP MeasureNonnegativeIntegral MeasureAlmostUP MeasureAlmostBasic
  CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableProduct
  CountablyMeasurableFunctions CountablyMeasurableNullModification
  ProductFunctionFubini ParameterizedIntegral TopologicalProductMaps SeparableMetricBaseSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_multiplicity_continuous_parameter_measurable]:
    supporting iterated-integral measurability for 2.10.16,
    p. 178. A countable-base parameter measure with countably
    measurable whole space suffices. Actual Lebesgue section
    integrals are identified at every parameter, not only almost
    everywhere. *)
Theorem projection_multiplicity_continuous_parameter_measurable (R : realType)
    (X : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (U : nat -> set X)
    (n m : nat) (u : X -> orthogonal_projection_metric_space R n m)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_countable_open_base U -> measure_countably_measurable mu setT ->
  continuous u -> borel_set A ->
  is_measure_measurable_function mu
    (partial_function_total (fun x => projection_multiplicity_integral A (u x))).
Proof.
move=> hU hwhole hu hA.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose Z := (Y*X)%type.
pose nu := product_measure (@euclidean_lebesgue_is_measure R m) hm.
have hn := product_measure_is_measure (@euclidean_lebesgue_is_measure R m) hm.
have [V hV] := euclidean_countable_open_base R m.
have hrn := @product_measure_borel_regular R Y X (@euclidean_lebesgue_measure R m) mu
  (@euclidean_lebesgue_is_measure R m) hm V U hV hU (@euclidean_lebesgue_borel_regular R m) hr.
have hc B : closed B -> measure_measurable nu B.
  move=> hB; exact (@borel_regular_borel_measurable R Z nu hn hrn B (closed_borel_set hB)).
pose v (z : Z) := (z.1,u z.2).
have hv : continuous v.
  apply: topological_pair_continuous; first exact: first_projection_continuous.
  move=> z; exact: continuous_comp (@second_projection_continuous Y X z) (hu z.2).
pose f := partial_function_total (fun z : Z => projection_joint_multiplicity A (v z)).
have hf := @projection_joint_precomposition_measurable R Z n m nu v A hn hc hv hA.
have hp : measure_almost_everywhere nu (partial_extended_nonnegative_locus f).
  apply: (@measure_almost_everywhere_mono R Z nu hn setT _ _ (measure_almost_everywhere_true hn))=> z _.
  exists (projection_joint_multiplicity A (v z)); split=> //; exact: projection_joint_multiplicity_nonnegative.
have [hi _] := @nonnegative_measurable_function_integral R Z nu hn f hf hp.
have hprod : measure_countably_measurable nu setT.
  exact: product_whole_countably_measurable (@euclidean_lebesgue_countably_measurable R m) hwhole.
have hcount : is_countably_measure_measurable_function nu (0 : extended_real_line R) f.
  exact: (@countably_measurable_function_on_countable_source R Z (extended_real_line R) nu hn
    0 f (@extended_real_zero_closed R) hprod hf).
have ho := (@product_function_fubini R Y X (@euclidean_lebesgue_measure R m) mu
  (@euclidean_lebesgue_is_measure R m) hm f _ hi hcount).2.
have he x z : partial_function_graph
    (parameterized_integral (@euclidean_lebesgue_measure R m) (partial_product_horizontal_section f)) x z <->
    partial_function_graph (partial_function_total (fun x => projection_multiplicity_integral A (u x))) x z.
  rewrite parameterized_integral_specification.
  change (is_measure_integral (@euclidean_lebesgue_measure R m)
    (projection_multiplicity_integrand A (u x)) z <-> projection_multiplicity_integral A (u x)=z).
  have hi0 := @projection_multiplicity_integral_specification R n m A (u x) hA.
  split; first by move=> hz; exact: esym (MeasureIntegralUniqueness.measure_integral_unique hz hi0).
  by move=> <-.
exact (@measure_integral_graph_equivalent R X mu _ _ _ he ho).1.
Qed.

(** Source for [projection_multiplicity_separable_parameter_measurable]:
    supporting countable-base instance for 2.10.16, p. 178.
    In a separable metric parameter space the already proved
    base existence discharges the explicit topological premise. *)
Theorem projection_multiplicity_separable_parameter_measurable (R : realType)
    (X : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (n m : nat)
    (u : X -> orthogonal_projection_metric_space R n m)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (exists D : set X, countable D /\ dense D) ->
  measure_countably_measurable mu setT -> continuous u -> borel_set A ->
  is_measure_measurable_function mu
    (partial_function_total (fun x => projection_multiplicity_integral A (u x))).
Proof.
move=> [D [hD hden]] hwhole hu hA.
pose U := @SeparableMetricBase.value R X D hD hden.
exact (@projection_multiplicity_continuous_parameter_measurable R X mu hm hr U n m u A
  (@SeparableMetricBase.laws R X D hD hden) hwhole hu hA).
Qed.
