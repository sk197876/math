(** Federer (1969), 4.1.7, p. 358:
    the bounded nonnegative scalar density identifies
    the original variation measure itself. The
    proof uses 2.4.10, p. 85, and the
    compact-test uniqueness consequence of 2.5.14,
    p. 107, retaining actual outer masses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionBasic
  SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasurableFunctionUP
  TotalScalarMeasurability MeasureStepIntegralIdentification RadonMeasureUP RadonBorelRegularity
  BorelRegularMeasureUP MeasureDensityUP MeasureDensity BoundedRealDensityMeasure
  FunctionLatticeUP CompactSupportFunctionUP CompactSupportSummability RealIntegralFunctionalUP
  RealLatticeDensityUP RealFiniteDensityIntegral RadonPositiveCompactUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_bounded_compact_density_identifies_measure]:
    the bounded nonnegative density supplied by
    2.5.9 determines the original Radon measure
    on all sets, supporting Federer 4.1.7,
    p. 358. Countable compact neighbourhood covers
    belong to the original domain; no bounded-set
    finiteness or global mass bound is added. *)
Theorem radon_bounded_compact_density_identifies_measure (R:realType) (X:metricType R)
    (mu nu:set X->\bar R) (hm:is_measure mu) (hn:is_measure nu)
    (hr:is_radon_measure mu) (hs:is_radon_measure nu)
    (F:(X->R)->R) (k:X->R) (C W:nat->set X):
  is_real_integral_functional nu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F ->
  is_real_lattice_density mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F k ->
  (forall x,0<=k x<=1) ->
  (forall j,compact (C j)) ->(forall j,open (W j)) ->(forall j,W j `<=` C j) ->
  setT `<=` \bigcup_j C j ->setT `<=` \bigcup_j W j ->
  is_measure_density mu (real_total_integrand k) nu.
Proof.
move=>hF hk hRange hC hW hWC hCover hWCover.
have hKReal:=@total_scalar_real_measurable R X mu hm k hk.1.
have hKMeas:=@measurable_partial_real_embedding R X mu hm
  (partial_function_total (k:X->real_line_metric R)) hKReal.
pose delta:=measure_with_density mu (real_total_integrand k).
have hPositive:=@unit_real_density_measure_nonnegative R X mu hm k hRange.
have hDelta:is_measure delta:=measure_with_density_is_measure hm hPositive.
have hDeltaRadon:=@unit_real_density_measure_radon R X mu hm hr k hKMeas hRange
  C W hC hW hWC hCover hWCover.
have hDeltaF:is_real_integral_functional delta
    (positive_function_lattice (@compactly_supported_continuous_functions R X)) F.
  move=>f hf.
  have hMeas:=@continuous_real_integrand_measurable R X mu hm
    (fun B hB=>borel_regular_borel_measurable hm (radon_borel_regular hm hr) hB) f hf.1.1.
  exact:((@real_finite_density_integral_iff R X mu delta hm k f
    (measure_with_density_laws mu (real_total_integrand k)) hKMeas hPositive hMeas (F f)%:E).2
    (hk.2 f hf)).
have hEqual:=@radon_positive_compact_integral_unique R X nu delta hn hDelta hs hDeltaRadon F hF hDeltaF.
move=>A; rewrite hEqual; exact:measure_with_density_laws.
Qed.
