(** Federer (1969), 2.4.12, pp. 86–87,
    used in 4.1.18, p. 376: null changes of
    the target preserve the original Lp pseudodistance
    and convergence. Every original partial domain is
    retained; no pointwise vector-space law on arbitrary
    partial graphs is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP
  PartialNormedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableNormedDifference
  MeasureLpNormAlmostEquality MeasureLpConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AlmostTarget.
Variable R:realType.
Variable X:choiceType.
Variable V:lmodType R.
Variable N:V->R.
Variable hN:is_real_norm N.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Variable p:R.
Hypothesis hp:1<=p.
Local Notation M:=(real_norm_metric_space hN).

(** Source for [measure_lp_distance_almost_target]:
    the almost-equality invariance of the difference
    seminorm, from Federer 2.4.12, pp. 86–87,
    supporting the compact field limit in 4.1.18, p. 376. *)
Lemma measure_lp_distance_almost_target (f g h:partial_function X M):
  is_measurable_normed_function mu f->
  is_measurable_normed_function mu g->
  is_measurable_normed_function mu h->measure_almost_equal mu g h->
  measure_lp_distance mu N p f g=measure_lp_distance mu N p f h.
Proof.
move=>hF hG hH hEqual.
have hFG:=@measurable_normed_function_subtract R X V N hN mu hm f g hF hG.
have hFH:=@measurable_normed_function_subtract R X V N hN mu hm f h hF hH.
apply:(@measure_lp_norm_almost_equal R X V N hN mu hm p _ _ hp hFG.1 hFH.1).
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _
  (measure_almost_everywhere_and hm (measurable_function_domain hF.1) hEqual))
  =>x [[a hA] [b [hB hBH]]].
exists (a-b);split.
- apply/partial_vector_subtract_graph;exists a,b;by split=>//;split.
- apply/partial_vector_subtract_graph;exists a,b;by split=>//;split.
Qed.

(** Source for [converges_in_lp_norm_almost_target]:
    an almost-equal representative is the same Lp
    limit in Federer 2.4.12, p. 87, as used
    to retain compact carriers in 4.1.18, p. 376. *)
Theorem converges_in_lp_norm_almost_target
    (f:nat->partial_function X M) (g h:partial_function X M):
  (forall i,is_measurable_normed_function mu (f i))->
  is_measurable_normed_function mu g->
  is_measurable_normed_function mu h->measure_almost_equal mu g h->
  converges_in_lp_norm mu N p f g->converges_in_lp_norm mu N p f h.
Proof.
move=>hF hG hH hEqual hConverges epsilon hEpsilon.
have[k hK]:=hConverges epsilon hEpsilon.
exists k=>i hI.
rewrite -(@measure_lp_distance_almost_target (f i) g h
  (hF i) hG hH hEqual).
exact:hK i hI.
Qed.
End AlmostTarget.
