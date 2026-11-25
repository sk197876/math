(** Supporting Federer (1969), 2.10.46, p. 204: an auxiliary Fubini route to
    the exceptional-projection assertion of Freilich (1950), Lemma 4.4, p.
    240. For any finite Borel regular measure on positive-dimensional
    projections, almost every source vector is annihilated by only a null
    set of projections. Invariance will upgrade this to every nonzero vector
    in a separate theorem. Freilich uses sphere measure in Lemmas 4.1–4.4,
    pp. 238–240; the present proof uses only the already established
    Lebesgue hyperplane nullity and Fubini. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  EuclideanProjectionKernelNull EuclideanLebesgueDimensions EuclideanLebesgueHaar
  TopologicalProductMaps TopologicalBorel ContinuousBorelPreimages SeparableMetricBaseSealed
  MeasureUP MeasureBasic MeasureSplit BorelRegularMeasureUP MeasureAlmostUP MeasureAlmostBasic
  ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureConullZeroIntegral ProductMeasure ProductBorelRegularity ProductSections ProductSetFubini ProductNullSections
  CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableProduct CountablyMeasurableSubsets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_kernel_incidence_almost_null]: supporting
    almost-every-vector step toward Freilich (1950), Lemma
    4.4, p. 240, for Federer 2.10.46, p. 204.
    Kernel incidence is Borel by continuous evaluation. Its
    Lebesgue sections are null, so Fubini gives product nullity
    and nullity of almost every section in the other direction. *)
Theorem projection_kernel_incidence_almost_null (R : realType) n m
    (theta : set (orthogonal_projection_metric_space R n.+1 m.+1) -> \bar R)
    (ht : is_measure theta) :
  is_borel_regular_measure theta -> theta setT< +oo ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n.+1)
    [set x | theta [set p | euclidean_projection_linear p x=0%R]=0].
Proof.
move=> hr hfin.
pose X := inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y := inner_metric_space (@euclidean_inner_productP R m.+1).
pose P := orthogonal_projection_metric_space R n.+1 m.+1.
pose S : set (X*P) := [set z | euclidean_projection_linear z.2 z.1=0%R].
pose ha := euclidean_lebesgue_is_measure R n.+1.
pose mu := product_measure ha ht.
have hm := product_measure_is_measure ha ht.
have [U hU] := euclidean_countable_open_base R n.+1.
have [D [hD hd]] := orthogonal_projection_metric_separable R n.+1 m.+1.
have hreg := @product_measure_borel_regular R X P
  (@euclidean_lebesgue_measure R n.+1) theta ha ht U
  (@SeparableMetricBase.value R P D hD hd) hU (@SeparableMetricBase.laws R P D hD hd)
  (euclidean_lebesgue_borel_regular R n.+1) hr.
have hev : continuous (fun z : X*P=>(euclidean_projection_linear z.2 z.1 : Y)).
  have hs : continuous (fun z : X*P=>(z.2,z.1)).
    apply: topological_pair_continuous; [exact: second_projection_continuous | exact: first_projection_continuous].
  move=> z; exact (continuous_comp (hs z) (@euclidean_projection_evaluation_continuous R n.+1 m.+1 (z.2,z.1))).
have hS : borel_set S.
  apply: (@continuous_borel_preimage (X*P)%type Y _ hev [set (0%R : Y)]).
  apply: closed_borel_set; apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
have hSm := @borel_regular_borel_measurable R (X*P)%type mu hm hreg S hS.
have hwt := @finite_measurable_set_countably_measurable R P theta setT
  (measure_measurable_whole ht) hfin.
have hw := product_whole_countably_measurable ha ht (euclidean_lebesgue_countably_measurable R n.+1) hwt.
have hSc := @measurable_subset_countably_measurable R (X*P)%type mu hm S setT hSm (subsetT S) hw.
have hi := (@product_set_fubini R X P (@euclidean_lebesgue_measure R n.+1) theta ha ht S hSc).2.2.2.
have hzero : is_measure_integral theta
    (partial_function_total (fun p=>euclidean_lebesgue_measure n.+1 (product_horizontal_section S p))) 0.
  apply: (measure_almost_zero_integral ht).
  apply: (@measure_almost_everywhere_mono R P theta ht setT _ _ (measure_almost_everywhere_true ht))=> p _.
  exact: euclidean_positive_projection_kernel_null (euclidean_projection_linear_member p).
have hz : mu S=0 := measure_integral_unique hi hzero.
exact: (@product_null_vertical_sections R X P (@euclidean_lebesgue_measure R n.+1) theta ha ht S hz).
Qed.
