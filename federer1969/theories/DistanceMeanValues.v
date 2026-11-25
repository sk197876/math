(** Federer (1969), 2.9.9, pp. 156–157: fixed-target distance functions in
    the Lebesgue-point proof. We retain Federer's exponent one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasurableFunctionUP MeasureSubsetIntegral MeasureIntegralUniqueness
  PartialZeroExtension MeasurableDistanceTo DistanceSubsetIntegral MeasureMeanFunction
  FiniteMeanPartValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_distance_mean_values]: supporting finite means and
    uniform one-Lipschitz estimate in Federer 2.9.9, p. 157 At exponent one,
    two integrated triangle inequalities give the estimate. Denominators are
    positive and finite, never completed at zero. *)
Lemma finite_distance_mean_values (R : realType) (X : choiceType) (Y : metricType R)
    (phi : set X -> \bar R) (f : partial_function X Y) S (b : R) (base y z : Y) :
  is_measure phi -> is_measure_measurable_function phi f -> measure_measurable phi S ->
  phi S=b%:E -> (0<b)%R ->
  (exists c : R, is_measure_subset_integral phi S (partial_distance_to f base) c%:E) ->
  exists a d : R,
    partial_function_graph (measure_mean_function phi (partial_distance_to f y)) S a%:E /\
    partial_function_graph (measure_mean_function phi (partial_distance_to f z)) S d%:E /\
    (`|a-d|<=mdist y z)%R.
Proof.
move=> hm hf hS hSb hbp [c hc].
have [a [ha _]] := @distance_subset_integral_bound R X Y phi f S c b base y hm hf hS hSb hc.
have [d [hd had]] := @distance_subset_integral_bound R X Y phi f S a b y z hm hf hS hSb ha.
have [a' [ha' hda]] := @distance_subset_integral_bound R X Y phi f S d b z y hm hf hS hSb hd.
have he := @measure_integral_unique R X phi
  (partial_function_zero_extension (0 : extended_real_line R) S (partial_distance_to f y))
  a'%:E a%:E ha' ha.
have hea : a'=a by apply/eqP; move: he=> /eqP; rewrite eqe.
rewrite hea (metric_sym z y) in hda.
exists (a/b)%R,(d/b)%R; split.
- exact: finite_measure_mean_value ha hSb hbp.
- split; first exact: finite_measure_mean_value hd hSb hbp.
  rewrite ler_norml; apply/andP; split.
  + rewrite lerNl opprB -mulrBl (ler_pdivrMr _ _ hbp) lerBlDr.
    by rewrite addrC.
  + rewrite -mulrBl (ler_pdivrMr _ _ hbp) lerBlDr.
    by rewrite addrC.
Qed.
