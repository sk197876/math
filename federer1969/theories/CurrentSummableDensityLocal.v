(** Federer (1969), 4.1.25, p. 383: a
    globally summable target coefficient field meets
    the earlier local input conditions for its density
    current, 4.1.7, p. 356. The original measure
    may be any measure with measurable open sets;
    ambient Hausdorff measure need not be Radon. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ExteriorGrading CurrentCoefficientNorms CurrentDensityUP CurrentDensityNormMeasurable
  DistributionIntegralFieldUP SmoothCompactSet
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureFiniteClosure MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasurableFunctionUP SummableRealFunctionUP SummableSubsetRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_summable_density_locally_integrable]:
    global norm summability implies every original
    compact norm integral is finite, supporting the
    target density current in Federer 4.1.25,
    p. 383. Weak measurability is obtained from
    the previously proved finite coefficient topology. *)
Theorem current_summable_density_locally_integrable (R : realType)
    (h2 : (1+1 : R) != 0) n m
    (gamma : set (R_n R n) -> \bar R)
    (hGamma : is_measure gamma)
    (hBorel : @is_current_density_borel_measure R n gamma)
    (w : R_n R n -> exterior_power (R_n R n) m) b :
  is_measure_measurable_function gamma
    (partial_function_total (fun x =>
      (w x : real_norm_metric_space (@current_vector_mass_real_norm R h2 n m)))) ->
  is_measure_integral gamma (real_total_integrand
    (fun x => @current_vector_mass R h2 n m (w x))) b%:E ->
  @is_locally_integrable_current_density R h2 n m gamma w.
Proof.
move=> hMeas hIntegral.
constructor; first exact: (@current_density_weak_topology_measurable
  R h2 n m (R_n R n) gamma hGamma w hMeas).
move=> K.
pose X := R_n R n.
pose XT := real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
pose M := @current_vector_mass R h2 n m.
have hKClosed : @closed XT (smooth_compact_carrier K) :=
  compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact K).
have hKMeas : measure_measurable gamma (smooth_compact_carrier K).
  have h := measure_measurable_complement (hBorel _ (closed_openC hKClosed)).
  by rewrite setCK in h.
have hSummable : is_measure_summable gamma (real_total_integrand (fun x => M (w x))).
  by exists b.
have [a hA] := @summable_measurable_zero_extension R X gamma hGamma
  (smooth_compact_carrier K) _ hKMeas hSummable.
exists a; apply: (measure_integral_graph_equivalent _ hA) => x y.
rewrite real_total_integrand_graph.
case: pselect => hx.
- by rewrite (partial_function_zero_extension_on _ _ _ hx) real_total_integrand_graph.
- rewrite (partial_function_zero_extension_off _ _ _ hx).
  change (y = 0%E <-> 0%E = y); by split=> ->.
Qed.
