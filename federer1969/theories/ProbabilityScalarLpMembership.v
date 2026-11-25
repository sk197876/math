(** Supporting finite-norm representatives for the integral- geometric
    cost-cover argument in Federer (1969), 2.10.9, p. 175. The scalar Lp
    definitions are 2.4.12, p. 86; on a probability space the whole source
    is countably measurable, so the infinity-exponent support condition is
    automatic. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasureSplit
  MeasurableFunctionUP CountablyMeasurableBasic CountablyMeasurableFunctions
  TotalScalarLpUP NonnegativeExtendedExponentNorm NonnegativeExtendedScalarNorm
  NonnegativeExtendedNormFiniteValues ProbabilityNonnegativeExtendedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_scalar_finite_norm_lp]: supporting
    membership consequence of Federer 2.4.12, p. 86, for
    the cost-cover proof in 2.10.9, p. 175. No support
    assumption is added: the total probability mass supplies it. *)
Lemma probability_scalar_finite_norm_lp (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : \bar R) (g : X -> R) :
  mu setT = 1 -> 1<=t -> is_measure_measurable_function mu (total_scalar_function g) ->
  total_scalar_lp_norm mu t g< +oo -> total_scalar_lp mu t g.
Proof.
move=> hprob ht hg hfin; split=> //; split=> //; split=> //.
apply: (@countably_measurable_function_on_countable_source R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
  mu hm (0%R : R) (total_scalar_function g) _ _ hg).
- change (closed [set ((0%R : R) : real_norm_metric_space (scalar_absolute_value_norm R))]).
  apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
- apply: finite_measurable_set_countably_measurable; first exact: measure_measurable_whole hm.
  by rewrite hprob ltry.
Qed.

(** Source for [probability_extended_finite_norm_scalar_lp]:
    supporting finite scalar Lp representative for a nonnegative
    projected-volume input in Federer 2.10.9, p. 175.
    The finite norm proves almost everywhere finiteness before
    taking finite parts; the representative has exactly that norm. *)
Theorem probability_extended_finite_norm_scalar_lp (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> ExtendedRealOrderTopology.extended_real_line R) (t : \bar R) :
  mu setT = 1 -> (forall x, 0<=f x) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  nonnegative_extended_exponent_norm mu f t< +oo ->
  total_scalar_lp mu t (fun x => fine (f x)) /\
  total_scalar_lp_norm mu t (fun x => fine (f x))=nonnegative_extended_exponent_norm mu f t.
Proof.
move=> hprob hf0 ht hf hfin.
have hs := @nonnegative_extended_exponent_norm_specification R X mu f t hm hf0 ht hf.
have hfinite := @finite_nonnegative_extended_norm_almost_finite R X mu hm f t _ hf0 hs hfin.
have he := @nonnegative_extended_norm_almost_finite_scalar R X mu hm f t hf0 hfinite ht hf.
have hg := @measurable_extended_finite_scalar R X mu hm f hf.
split; last exact: esym he.
apply: (@probability_scalar_finite_norm_lp R X mu hm t (fun x => fine (f x)) hprob ht hg).
by rewrite /total_scalar_lp_norm /total_scalar_function -he.
Qed.
