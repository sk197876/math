(** Federer (1969), 4.1.7, p. 358: the
    dominated scalar density can be chosen between
    zero and one everywhere. Positivity follows
    from the preceding compact-test approximation;
    modification on the actual null exceptional set
    preserves every original integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableTotalBasic MeasurableTotalCutoff TotalScalarLpUP
  TotalScalarComparison RadonMeasureUP FunctionLatticeUP CompactSupportFunctionUP
  RealLatticeDensityUP RadonPositiveCompactDensity CountablyFiniteLocalNull CountablyMeasurableUP
  SummableRealFunctionUP MeasureIntegralUP MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_bounded_positive_compact_density]:
    a scalar density dominated by one for a
    positive original compact-test functional has
    an everywhere nonnegative representative, supporting
    Federer 4.1.7, p. 358, through 2.5.9,
    p. 100. The countable-finiteness premise concerns
    the original domain and is proved for open U. *)
Theorem radon_bounded_positive_compact_density (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (A:(X->R)->R) (k:X->R):
  measure_countably_measurable mu setT ->
  is_real_lattice_density mu
    (positive_function_lattice (@compactly_supported_continuous_functions R X)) A k ->
  (forall f,positive_function_lattice (@compactly_supported_continuous_functions R X) f ->0<=A f) ->
  (forall x,`|k x|<=1) ->exists l:X->R,
    is_real_lattice_density mu
      (positive_function_lattice (@compactly_supported_continuous_functions R X)) A l /\
    forall x,0<=l x<=1.
Proof.
move=>hCount hk hPositive hBound.
have hLocal:=@radon_positive_compact_density_locally_nonnegative R X mu hm hr A k hk hPositive.
have hAlmost:measure_almost_everywhere mu [set x|0<=k x].
  exact:(@countably_finite_locally_null_is_null R X mu hm _ hCount hLocal).
pose G:set X:=[set x|0<=k x].
pose l x:=if pselect (G x) then k x else 0.
have hZeroMeas:=@measurable_total_constant R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0.
have hG:measure_measurable mu G.
  exact:(@total_scalar_measurable_comparison R X mu hm (fun _=>0) k hZeroMeas hk.1).
have hl:is_measure_measurable_function mu (total_scalar_function l).
  exact:(@measurable_total_cutoff R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    mu hm G k 0 hG hk.1).
exists l; split.
- split; first exact:hl.
  move=>f hf; apply:(measure_integral_almost_equal hm (hk.2 f hf)).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAlmost)=>x hx.
  have hEq:l x=k x by rewrite /l; case:pselect=>// hn; exact:False_ind _ (hn hx).
  exists (f x*k x)%:E; split; first by rewrite real_total_integrand_graph.
  by rewrite real_total_integrand_graph hEq.
- move=>x; rewrite /l; case:pselect=>hx; last by rewrite lexx ler01.
  apply/andP; split; first exact:hx.
  exact:le_trans (ler_norm _) (hBound x).
Qed.
