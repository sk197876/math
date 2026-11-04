(** Federer (1969), 3.2.22(3), p. 258, and
    3.2.47(3), p. 283: coarea bounds the
    integral of actual whole-fibre masses by an actual
    approximate-Jacobian bound times original source mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionality PartialFunctionSourceRestriction PartialFunctionPostcomposition
  PartialZeroExtension PartialDensityProduct PartialMappingMultiplicity ParameterizedIntegral
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureSubsetIntegral MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality
  MeasureApproximateJacobian HausdorffMeasure RectifiableCoareaUP RectifiableCoareaIntegrands
  MeasureSubsetConstantIntegral CoareaIntegralUpperBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_fibre_mass_integral_bound]:
    the coarea mass comparison of 3.2.47(3), p. 283,
    from actual 3.2.22(3), p. 258. Every fibre
    has its actual Hausdorff mass; infinite individual fibre
    masses are retained. The tangent Jacobian bound and
    Borel-fibre measurability are obligations discharged at the
    application, not assumed geometric conclusions. *)
Theorem rectifiable_coarea_fibre_mass_integral_bound (R:realType) m n q v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v)) (C:R):
  is_rectifiable_coarea m q W Z f ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  partial_function_domain f=W ->(0<C)%R ->
  (forall x j,W x ->partial_function_graph (measure_approximate_jacobian
    (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    m q f) x j ->(j<=C)%R) ->
  (forall z,measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) (m-q)) (partial_mapping_fibre f z)) ->
  exists a,is_measure_subset_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) q) Z
    (partial_function_total (fun z=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) (m-q)
      (partial_mapping_fibre f z):extended_real_line R))) a /\
    a<=C%:E* @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W.
Proof.
move=>hCoarea hW hDom hC hBound hFibreMeas.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose rho:=@hausdorff_measure R X m.
pose gamma:=@hausdorff_measure R Y q.
pose beta:=@hausdorff_measure R X (m-q).
have hRho:=@hausdorff_measure_is_measure R X m.
have hGamma:=@hausdorff_measure_is_measure R Y q.
have hBeta:=@hausdorff_measure_is_measure R X (m-q).
pose nu:=measure_restrict rho W.
have hNu:is_measure nu:=measure_restrict_is_measure hRho W.
pose one:=partial_function_total (fun _ : R_n R n=>(1:extended_real_line R)).
pose g:=partial_function_source_restrict W one.
have hGDomain:partial_function_domain g=W.
  by rewrite /g partial_function_source_restrict_domain partial_function_total_domain setIT.
have hNull:nu (~` W)=0.
  rewrite /nu /measure_restrict.
  have hEmpty:W `&` ~` W=set0 by apply/seteqP; split=>[x [hx hn]|x []]; exfalso; exact:hn hx.
  rewrite hEmpty; exact:measure_empty hRho.
have hNuW:measure_measurable nu W:=measure_restrict_measurable W hW.
have hOne:=@measure_nonnegative_constant_subset_integral R [the choiceType of X] nu W 1 hNu hNuW lee01.
have hWeight:measure_almost_equal nu (partial_function_zero_extension (0:extended_real_line R) W one) g.
  apply:(measure_null_subset hNu _ hNull)=>x hn hx.
  apply:hn; exists 1; split.
  - apply:(partial_function_zero_extension_on _ _ _ hx).2; reflexivity.
  - by split.
have hGInt:is_measure_integrable nu g.
  exists (1*nu W).
  exact (@measure_integral_almost_equal R [the choiceType of X] nu hNu _ _ _ hOne hWeight).
have [a [hSource hTarget]]:=rectifiable_coarea_integral_law hCoarea hGDomain hGInt.
pose target:=rectifiable_coarea_fibre_integral m q f g.
have hTargetPoint z:partial_function_graph target z (beta (partial_mapping_fibre f z)).
  have hConst:=@measure_nonnegative_constant_subset_integral R [the choiceType of X]
    beta (partial_mapping_fibre f z) 1 hBeta (hFibreMeas z) lee01.
  rewrite mul1e in hConst.
  apply:(parameterized_integral_specification _ _ _ _).2.
  apply:measure_integral_graph_equivalent _ hConst=>x y.
  rewrite !partial_function_zero_extension_graph.
  have hIn:partial_mapping_fibre f z x ->W x.
    move=>hx; rewrite -hDom; by exists z.
  split.
  - move=>[[hx hy]|[hx hy]]; [left|right]=>//.
    split; first exact hx; by split; first exact:hIn hx.
  - move=>[[hx [hWx hy]]|[hx hy]]; [left|right]=>//.
have hTargetEq:target=partial_function_total (fun z=>(beta (partial_mapping_fibre f z):extended_real_line R)).
  apply:partial_function_graph_extensionality=>z y; split=>hy.
  - exact (esym (partial_function_single_valued hy (hTargetPoint z))).
  - change (beta (partial_mapping_fibre f z)=y) in hy.
    by rewrite -hy; exact:hTargetPoint.
pose d:=measure_approximate_jacobian nu m q f.
pose u:=partial_density_product g (extended_measure_approximate_jacobian nu m q f).
have hUpper:a<=C%:E*rho W.
  apply:(@coarea_subset_integral_upper_constant R [the choiceType of X] rho hRho W u a C hW hC _ hSource).
  move=>x y hx hValue.
  have [b [c0 [hB [hCJ hProduct]]]]:=(partial_density_product_graph _ _ _ _).1 hValue.
  have hOneValue:b= 1 by exact:esym hB.2.
  have [j [hJ hFinite]]:=hCJ.
  rewrite hOneValue -hFinite mul1e in hProduct.
  rewrite -hProduct lee_fin; exact (@hBound x j hx hJ).
exists a; split; last exact hUpper.
change (is_measure_subset_integral gamma Z
  (partial_function_total (fun z=>(beta (partial_mapping_fibre f z):extended_real_line R))) a).
by rewrite -hTargetEq.
Qed.
