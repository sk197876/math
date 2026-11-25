(** Federer (1969), 3.2.48, pp. 284–286: signed
    weighted coarea with the actual computed tangent profile. The
    approximate-Jacobian graph and original measurable domains are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  PartialZeroExtension PartialMappingMultiplicity MeasureApproximateJacobian
  RectifiableCoareaIntegrands RectifiablePartialCoareaFormula RectifiableCoareaVariableProfile RectifiableSetUP
  HausdorffMeasure MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  RestrictedAlmostEverywhere MeasurableNormedRestriction MeasureIntegralAlmostEquality
  MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_weighted_coarea_profile]: the application
    of 3.2.22(3), p. 258, in 3.2.48, p. 284. This supporting
    version exposes the almost-everywhere actual Jacobian graph, which
    the spherical submanifold calculation proves independently. It adds
    no Jacobian measurability or fibre-integrability hypothesis. *)
Theorem rectifiable_weighted_coarea_profile (R:realType) m n q v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v)) (w j:R_n R n->R):
  (q<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) q) q Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) q) Z ->
  partial_function_domain f=W ->
  (exists L,@is_partial_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) f L) ->
  partial_function_range f `<=` Z ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  is_measure_integrable (measure_restrict H W) (real_total_integrand w) ->
  measure_almost_everywhere_on H W [set x|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H W) m q f) x (j x)] ->
  exists a,is_measure_integral (measure_restrict H W)
      (real_total_integrand (fun x=>(w x*j x)%R)) a /\
    is_measure_subset_integral (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) q) Z
      (rectifiable_coarea_fibre_integral m q f
        (partial_function_source_restrict W (real_total_integrand w))) a.
Proof.
move=>hDim hRW hW hRZ hZ hDom hLip hRange H [b hWeight] hJac.
pose rho:=measure_restrict H W.
have hm:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hr:=measure_restrict_is_measure hm W.
have hConull:measure_almost_everywhere rho W.
  change (H (W `&` (~` W))=0)%E.
  have hEmpty:W `&` (~` W)=set0 by apply/seteqP; split=>x; [by move=>[h hN]; apply hN|by []].
  rewrite hEmpty; exact (measure_empty hm).
have hDomain:measure_almost_everywhere rho (partial_function_domain (real_total_integrand w)).
  apply:(measure_almost_everywhere_mono hr _ (measure_almost_everywhere_true hr))=>x _.
  exists (w x)%:E; exact ((real_total_integrand_graph _ _ _).2 erefl).
have hAlmost:=conull_source_restriction_almost_equal hr hConull hDomain.
have hG:=measure_integral_almost_equal hr hWeight hAlmost.
have hGDomain:partial_function_domain
    (partial_function_source_restrict W (real_total_integrand w))=W.
  apply/seteqP; split=>x.
  - by move=>[y [hx _]].
  - move=>hx; exists (w x)%:E; split; first exact hx.
    exact ((real_total_integrand_graph _ _ _).2 erefl).
have [a [hSource hTarget]]:=@rectifiable_partial_coarea_integrable_weights R m n q v W Z f
  (partial_function_source_restrict W (real_total_integrand w)) hDim hRW hW hRZ hZ hDom hLip
  hRange hGDomain (ex_intro _ b hG).
exists a; split; last exact hTarget.
exact (@rectifiable_coarea_source_profile_integral R m n q v W f w j a hW hJac hSource).
Qed.
