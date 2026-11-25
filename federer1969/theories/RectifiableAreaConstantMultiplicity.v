(** Federer (1969), 3.2.28(4), pp. 266–267:
    actual unit Jacobian and two-point fibres in the
    area formula. The supporting lemma allows any
    nonnegative constant Jacobian and multiplicity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialZeroExtension PartialDensityProduct
  PartialMetricLipschitz LipschitzBasic EuclideanPartialLipschitzExtension PartialMappingMultiplicity CountingMeasure MeasureUP MeasureBasic MeasureRestriction
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  MeasureIntegralAlmostEquality MeasureIntegralUniqueness MeasureApproximateJacobian HausdorffMeasure
  RectifiableSetUP RectifiableAreaIntegrands RectifiableAreaFormula MeasureSubsetConstantIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_area_constant_multiplicity]:
    specialize the actual area identity 3.2.20,
    pp. 256–257, as in Federer 3.2.28(4),
    pp. 266–267. Exact original domains and
    infinite measure values are retained. The already proved
    dimension-free global-extension area theorem supplies
    the identity in every natural ambient degree. *)
Theorem rectifiable_area_constant_multiplicity (R:realType) m n k
    (W:set (R_n R n)) (Z:set (R_n R k))
    (f:partial_function (R_n R n) (R_n R k)) (j:R) (r : \bar R):
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) m) Z ->
  partial_function_domain f=W ->
  (exists L,@is_partial_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) f L) ->
  partial_function_range f `<=` Z ->(0<=j)%R ->0<=r ->
  measure_almost_everywhere_on (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W
    [set x|partial_function_graph (measure_approximate_jacobian
      (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W)
      m m f) x j] ->
  (forall z,Z z ->@partial_mapping_multiplicity R _ _ f z=r) ->
  j%:E* @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W=
    r* @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) m Z.
Proof.
move=>hRect hW hZ hDom hLip hRange hj hr hJac hCount.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R k).
pose rho:=@hausdorff_measure R X m.
pose gamma:=@hausdorff_measure R Y m.
have hRho:=@hausdorff_measure_is_measure R X m.
have hGamma:=@hausdorff_measure_is_measure R Y m.
pose one:=fun _ : R_n R k=>(1 : \bar R).
pose source:=rectifiable_area_source_integrand m W f one.
pose cs:=partial_function_zero_extension (0:extended_real_line R) W
  (partial_function_total (fun _ : R_n R n=>(j%:E:extended_real_line R))).
have hAE:measure_almost_equal rho cs source.
  apply:(measure_null_subset hRho _ hJac)=>x hn; split.
  - apply:contrapT=>hx; apply:hn; exists 0; split;
      apply:(partial_function_zero_extension_off _ _ _ hx).2; reflexivity.
  - move=>hJ; apply:hn.
    case:(pselect (W x))=>hx.
    + exists j%:E; split.
      * apply:(partial_function_zero_extension_on _ _ _ hx).2; reflexivity.
      * apply:(partial_function_zero_extension_on _ _ _ hx).2.
        apply/partial_density_product_graph; exists 1,j%:E; split.
        -- have [y hy]:partial_function_domain f x by rewrite hDom.
           exists y; by split.
        -- split; last by rewrite mul1e.
           exists j; by split.
    + exists 0; split; apply:(partial_function_zero_extension_off _ _ _ hx).2; reflexivity.
have hCS:is_measure_integral rho cs (j%:E*rho W):=
  @measure_nonnegative_constant_subset_integral R [the choiceType of X] rho W j%:E hRho hW
    ltac:(by rewrite lee_fin).
have hSource:=measure_integral_almost_equal hRho hCS hAE.
have [L hL]:=hLip.
have [F [hF hGraph]]:=euclidean_partial_lipschitz_global_extension hL.
rewrite hDom in hGraph.
have hArea: is_measure_integral rho (rectifiable_area_source_integrand m W f one) (j%:E*rho W) <->
    is_measure_integral gamma (rectifiable_area_target_integrand f one) (j%:E*rho W).
  rewrite hGraph.
  exact:(@rectifiable_area_global_extension R m n k W F hRect hW (metric_lipschitz_of_bound hF) one (j%:E*rho W)).
have hTarget:=hArea.1 hSource.
pose ct:=partial_function_zero_extension (0:extended_real_line R) Z
  (partial_function_total (fun _ : R_n R k=>(r:extended_real_line R))).
have hTargetGraph z y:partial_function_graph (rectifiable_area_target_integrand f one) z y <->
    partial_function_graph ct z y.
  rewrite partial_function_zero_extension_graph.
  change (1* @partial_mapping_multiplicity R _ _ f z=y <->
    (Z z /\r=y) \/(~Z z /\y=0)).
  rewrite mul1e.
  case:(pselect (Z z))=>hz.
  - rewrite (hCount z hz); split=>hy.
    + left; by split.
    + case:hy=>[[_ hy]|[hn _]]=>//; exfalso; exact:hn hz.
  - have hEmpty:partial_mapping_fibre f z=set0.
      apply/seteqP; split=>[x hx|x []]; exfalso; apply:hz; apply:hRange; by exists x.
    have hZero:@partial_mapping_multiplicity R _ _ f z=0.
      rewrite /partial_mapping_multiplicity hEmpty; exact:measure_empty (counting_measure_is_measure R X).
    rewrite hZero; split=>hy.
    + right; split=>//; by symmetry.
    + case:hy=>[[hx _]|[_ hy]]; first by exfalso; exact:hz hx.
      by symmetry.
have hCT:=measure_integral_graph_equivalent hTargetGraph hTarget.
have hConst:=@measure_nonnegative_constant_subset_integral R [the choiceType of Y] gamma Z r hGamma hZ hr.
exact:measure_integral_unique hCT hConst.
Qed.
