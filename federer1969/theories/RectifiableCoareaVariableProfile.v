(** Federer (1969), 3.2.48, pp. 284–286: an actual
    pointwise manifold Jacobian may replace the approximate Jacobian
    almost everywhere in signed coarea, on the original measurable source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialFunctionSourceRestriction
  PartialZeroExtension PartialDensityProduct ExtendedRealOrderTopology MeasureApproximateJacobian
  RectifiableCoareaIntegrands RectifiablePartialCoareaFormula RectifiableSetUP
  HausdorffMeasure MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureSubsetIntegral RestrictedIntegralIdentity
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_coarea_source_profile_integral]: the
    replacement of ap J by the computed manifold value in 3.2.48,
    p. 285, inside the coarea integral of p. 284. This is a
    supporting replacement lemma: its almost-everywhere graph premise
    is proved from actual submanifold tangents in the application. *)
Lemma rectifiable_coarea_source_profile_integral (R:realType) m n q v
    (W:set (R_n R n)) (f:partial_function (R_n R n) (R_n R v))
    (w j:R_n R n->R) a:
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  measure_measurable H W ->
  measure_almost_everywhere_on H W [set x|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H W) m q f) x (j x)] ->
  is_measure_integral H (rectifiable_coarea_source_integrand m q W f
    (partial_function_source_restrict W (real_total_integrand w))) a ->
  is_measure_integral (measure_restrict H W) (real_total_integrand (fun x=>w x*j x)) a.
Proof.
move=>H hW hJac hIntegral.
pose g:=partial_function_source_restrict W (real_total_integrand w).
pose h:=real_total_integrand (fun x=>w x*j x).
have hm:=@hausdorff_measure_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) m.
have hAlmost:measure_almost_equal H (rectifiable_coarea_source_integrand m q W f g)
    (partial_function_zero_extension (0:extended_real_line R) W h).
  apply:(measure_null_subset hm _ hJac)=>x hBad.
  have [hx|hx]:=pselect (W x); last first.
  - exfalso; apply hBad.
    exists (0:extended_real_line R); split;
      exact ((partial_function_zero_extension_off _ _ _ hx).2 erefl).
  split; first exact hx.
  move=>hJ; apply hBad.
    exists ((w x*j x)%:E:extended_real_line R); split.
    + apply/(partial_function_zero_extension_on _ _ _ hx).
      apply/partial_density_product_graph; exists (w x)%:E,(j x)%:E; split.
      * split; first exact hx.
        exact ((real_total_integrand_graph w x (w x)%:E).2 erefl).
      * split.
        -- exists (j x); by split.
        -- by rewrite EFinM.
    + apply/(partial_function_zero_extension_on _ _ _ hx).
      exact ((real_total_integrand_graph _ _ _).2 erefl).
have hRestored:=measure_integral_almost_equal hm hIntegral hAlmost.
exact ((@restricted_integral_zero_extension_iff R
  (inner_metric_space (@euclidean_inner_productP R n)) H hm W h a hW).2 hRestored).
Qed.
