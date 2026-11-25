(** Federer (1969), 4.1.7, p. 359:
    the original weighted image measure integrates
    a compact positive scalar test by its
    source weighted pullback. This supporting
    formula reuses 2.4.10, p. 85, and
    2.4.18, pp. 90–91, with the exact
    finite-real graph adapters. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasurePushforward MeasureAlmostUP PartialExtendedOrderLoci RadonMeasureUP RadonBorelRegularity
  BorelRegularMeasureUP MeasurableFunctionUP MeasurableGraphEquivalence CompactSupportSummability
  FunctionLatticeUP CompactSupportFunctionUP SummableRealFunctionUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence PushforwardIntegral MeasureDensityUP RealFiniteDensityIntegral
  RadonCompactScalarIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [real_total_pushforward_integral_iff]:
    the original image integral formula for
    total real scalar functions, supporting
    Federer 4.1.7, p. 359, by
    2.4.18, pp. 90–91. Integral definedness
    and every extended integral value are retained. *)
Lemma real_total_pushforward_integral_iff (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (f:X->Y) (g:Y->R):
  is_measure_measurable_function mu (real_total_integrand (fun x=>g (f x)))->forall a,
  is_measure_integral mu (real_total_integrand (fun x=>g (f x))) a<->
  is_measure_integral (measure_pushforward f mu) (real_total_integrand g) a.
Proof.
move=>hMeas a.
have hGraph x z:partial_function_graph (partial_function_precompose f (real_total_integrand g)) x z<->
    partial_function_graph (real_total_integrand (fun x=>g (f x))) x z.
  change (partial_function_graph (real_total_integrand g) (f x) z<->
    partial_function_graph (real_total_integrand (fun x=>g (f x))) x z).
  by rewrite !real_total_integrand_graph.
have hPreMeas:=measurable_function_graph_equivalent (fun x z=>iff_sym (hGraph x z)) hMeas.
have hIff:=@measure_pushforward_integral_iff R X Y mu hm f (real_total_integrand g) hPreMeas a.
split=>hI.
- apply:hIff.1;exact:(measure_integral_graph_equivalent (fun x z=>iff_sym (hGraph x z)) hI).
- exact:(measure_integral_graph_equivalent hGraph (hIff.2 hI)).
Qed.

(** Source for [radon_weighted_pushforward_compact_integral]:
    integrate a compact positive target test
    against the literal weighted image measure,
    supporting the sharp gauge inequality in
    Federer 4.1.7, p. 359. A coarse
    local bound is not used as a density. *)
Theorem radon_weighted_pushforward_compact_integral (R:realType) (X Y:topologicalType)
    (mu lambda:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (hl:is_measure lambda) (hs:is_radon_measure lambda) (w:X->R) (f:X->Y):
  is_measure_density mu (real_total_integrand w) lambda->
  is_measure_measurable_function mu (real_total_integrand w)->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand w))->
  continuous f->forall hnM:is_measure (measure_pushforward f lambda),
  forall hn:is_radon_measure (measure_pushforward f lambda),forall g,
  positive_function_lattice (@compactly_supported_continuous_functions R Y) g->
  is_measure_integral mu (real_total_integrand (fun x=>g (f x)*w x))
    (@radon_positive_compact_integral R Y (measure_pushforward f lambda)
      hnM hn g)%:E.
Proof.
move=>hDensity hW hPositive hF hnM hn g hG.
have hContinuous:continuous (fun x:X=>(g (f x):real_line_metric R)).
  move=>x O hNeighbour.
  exact (hF x (fun y:Y=>O (g y)) (hG.1.1 (f x) O hNeighbour)).
have hMuMeas:=@continuous_real_integrand_measurable R X mu hm
  (fun B hB=>borel_regular_borel_measurable hm (radon_borel_regular hm hr) hB)
  (fun x=>g (f x)) hContinuous.
have hLambdaMeas:=@continuous_real_integrand_measurable R X lambda hl
  (fun B hB=>borel_regular_borel_measurable hl (radon_borel_regular hl hs) hB)
  (fun x=>g (f x)) hContinuous.
have hTarget:=@radon_positive_compact_integral_laws R Y (measure_pushforward f lambda)
  hnM hn g hG.
have hSource:=(@real_total_pushforward_integral_iff R X Y lambda hl f g hLambdaMeas _).2 hTarget.
exact:((@real_finite_density_integral_iff R X mu lambda hm w (fun x=>g (f x))
  hDensity hW hPositive hMuMeas _).1 hSource).
Qed.
