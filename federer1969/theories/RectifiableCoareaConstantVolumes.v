(** Federer (1969), 3.2.28(2),(3), pp. 265–266:
    constant actual Jacobian and constant actual fibre
    measure turn rectifiable coarea into a volume identity.
    All integrals keep the original partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPostcomposition
  PartialZeroExtension PartialDensityProduct PartialMappingMultiplicity ParameterizedIntegral
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality MeasureIntegralUniqueness
  MeasureApproximateJacobian HausdorffMeasure RectifiableCoareaUP RectifiableCoareaIntegrands
  MeasureSubsetConstantIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_constant_volumes]: the
    coarea specializations giving both Stiefel volume
    identities in Federer 3.2.28(2),(3), pp. 265–266.
    Actual approximate Jacobian values and actual fibre
    masses are the hypotheses to be instantiated by
    the computed manifold maps. No finite fibre mass
    or cancellation of an infinite factor is assumed. *)
Theorem rectifiable_coarea_constant_volumes (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v)) (j:R) (lambda : \bar R):
  is_rectifiable_coarea m mu W Z f ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  partial_function_domain f=W ->(0<=j)%R ->0<=lambda ->
  measure_almost_everywhere_on (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W
    [set x|partial_function_graph (measure_approximate_jacobian
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
      m mu f) x j] ->
  (forall z,Z z ->@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)
    (partial_mapping_fibre f z)=lambda) ->
  j%:E* @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W=
    lambda* @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu Z.
Proof.
move=>hCoarea hW hZ hDom hj hLambda hJac hMass.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose rho:=@hausdorff_measure R X m.
pose gamma:=@hausdorff_measure R Y mu.
pose beta:=@hausdorff_measure R X (m-mu).
have hRho:=@hausdorff_measure_is_measure R X m.
have hGamma:=@hausdorff_measure_is_measure R Y mu.
have hBeta:=@hausdorff_measure_is_measure R X (m-mu).
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
pose d:=measure_approximate_jacobian nu m mu f.
pose source:=rectifiable_coarea_source_integrand m mu W f g.
pose cSource:=partial_function_zero_extension (0:extended_real_line R) W
  (partial_function_total (fun _ : R_n R n=>(j%:E:extended_real_line R))).
have hSourceAgreement x:
    (~W x \/partial_function_graph d x j) ->partial_function_agreement source cSource x.
  move=>[hx|hJ].
  - exists 0; split; apply:(partial_function_zero_extension_off _ _ _ hx).2; reflexivity.
  - case:(pselect (W x))=>hx.
    + exists j%:E; split.
      * apply:(partial_function_zero_extension_on _ _ _ hx).2.
        apply/partial_density_product_graph; exists 1,j%:E; split.
        -- by split.
        -- split; last by rewrite mul1e.
           exists j; by split.
      * apply:(partial_function_zero_extension_on _ _ _ hx).2; reflexivity.
    + exists 0; split; apply:(partial_function_zero_extension_off _ _ _ hx).2; reflexivity.
have hSourceAE:measure_almost_equal rho source cSource.
  apply:(measure_null_subset hRho _ hJac)=>x hn; split.
  - apply:contrapT=>hx; exact:hn (hSourceAgreement x (or_introl hx)).
  - move=>hJ; exact:hn (hSourceAgreement x (or_intror hJ)).
have hSourceValue:is_measure_integral rho cSource (j%:E*rho W).
  exact:(@measure_nonnegative_constant_subset_integral R [the choiceType of X] rho W j%:E hRho hW
    ltac:(by rewrite lee_fin)).
have hA:a=j%:E*rho W:=measure_integral_unique
  (measure_integral_almost_equal hRho hSource hSourceAE) hSourceValue.
pose target:=rectifiable_coarea_fibre_integral m mu f g.
pose cTarget:=partial_function_zero_extension (0:extended_real_line R) Z
  (partial_function_total (fun _ : R_n R v=>(lambda:extended_real_line R))).
have hTargetPoint z:Z z ->measure_measurable beta (partial_mapping_fibre f z) ->
    partial_function_graph target z lambda.
  move=>hz hFibre.
  have hConst:=@measure_nonnegative_constant_subset_integral R [the choiceType of X]
    beta (partial_mapping_fibre f z) 1 hBeta hFibre lee01.
  rewrite mul1e /beta /X (hMass z hz) in hConst.
  apply:(parameterized_integral_specification _ _ _ _).2.
  apply:measure_integral_graph_equivalent _ hConst=>x y.
  rewrite !partial_function_zero_extension_graph.
  have hIn:partial_mapping_fibre f z x ->W x.
    move=>hx; rewrite -hDom; by exists z.
  split.
  - move=>[[hx hy]|[hx hy]]; [left|right]=>//.
    split; first exact hx; by split; first exact:hIn hx.
  - move=>[[hx [hWx hy]]|[hx hy]]; [left|right]=>//.
have hTargetAE:measure_almost_equal gamma
    (partial_function_zero_extension (0:extended_real_line R) Z target) cTarget.
  apply:(measure_null_subset hGamma _ (rectifiable_coarea_fibre_law hCoarea))=>z hn.
  have hz:Z z.
    apply:contrapT=>hz; apply:hn; exists 0; split;
      apply:(partial_function_zero_extension_off _ _ _ hz).2; reflexivity.
  split; first exact hz.
  move=>[_ hFibre]; apply:hn; exists lambda; split.
  - apply:(partial_function_zero_extension_on _ _ _ hz).2; exact:hTargetPoint hz hFibre.
  - apply:(partial_function_zero_extension_on _ _ _ hz).2; reflexivity.
have hTargetValue:is_measure_integral gamma cTarget (lambda*gamma Z):=
  @measure_nonnegative_constant_subset_integral R [the choiceType of Y] gamma Z lambda hGamma hZ hLambda.
have hAT:a=lambda*gamma Z:=measure_integral_unique
  (measure_integral_almost_equal hGamma hTarget hTargetAE) hTargetValue.
exact:eq_trans (esym hA) hAT.
Qed.
