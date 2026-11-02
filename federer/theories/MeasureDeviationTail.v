(** Federer (1969), 2.3.7, p. 78: decreasing continuity is applied to mu
    restricted to A. Source context: UniformPartialConvergenceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionLimitUP MeasureUP MeasureBasic
  MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureContinuityAbove
  MeasurableFunctionUP MetricDeviationTails.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_deviation_tail_small]: direct choice of
    J(i) in Federer 2.3.7, p. 78. A need not be measurable;
    restriction permits continuity of the measurable tail sets. *)
Lemma measure_deviation_tail_small (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set Y) (A : set X) (f : nat -> partial_function X Y) (g : partial_function X Y)
    (eta delta : R) : countable D -> dense D ->
  (forall n, is_measure_measurable_function mu (f n)) -> is_measure_measurable_function mu g ->
  mu A < +oo -> measure_almost_everywhere_on mu A (partial_function_limit_locus f g) ->
  (0 < eta)%R -> (0 < delta)%R ->
  exists N, mu (A `&` partial_metric_deviation_tail f g eta N) < delta%:E.
Proof.
move=> hc hd hf hg hfin hlim heta hdelta.
pose nu := measure_restrict mu A.
pose F N := partial_metric_deviation_tail f g eta N.
have hn : is_measure nu := measure_restrict_is_measure hm A.
have hF n : measure_measurable nu (F n).
  apply: measure_restrict_measurable.
  exact (@partial_metric_deviation_tail_measurable R X Y mu hm D f g eta n hc hd hf hg).
have hmono n m : (n <= m)%N -> F m `<=` F n.
  exact: partial_metric_deviation_tail_antitone.
have hf0 : nu (F 0%N) < +oo.
  apply: le_lt_trans _ hfin; apply: (@measure_mono R X mu hm)=> x [hx _]; exact hx.
have hzero : nu (\bigcap_n F n) = 0.
  apply: (@measure_null_subset R X mu hm _ (A `\` partial_function_limit_locus f g))=> //.
  move=> x [ha hx]; split=> //.
  exact: (@partial_metric_limit_avoids_tail_intersection R X Y f g eta heta x hx).
have hconv := @measure_continuity_above R X nu hn F hF hmono hf0.
have hpos : nu (\bigcap_n F n) < delta%:E by rewrite hzero lte_fin.
have [N hN] := hconv.2.2 delta%:E hpos.
exists N; exact: hN N (leqnn N).
Qed.
