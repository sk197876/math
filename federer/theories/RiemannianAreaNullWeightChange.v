(** Federer (1969), 3.2.5, p. 245, extended
    by 3.2.46, p. 282: null target weight changes
    preserve both actual area integrands almost everywhere.
    Actual positive-Jacobian preimages are null and all
    other defined Jacobians are zero; missing differentials
    retain their exact partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianMapJacobian RiemannianLocalAreaSelection RiemannianAreaRankReduction
  RiemannianAreaJacobianVolumeMeasurable RiemannianAreaRankWeightAgreement RiemannianAreaTransformIntegrands
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_area_null_target_weight_change]:
    the null-weight replacement in 3.2.5, p. 245,
    for actual original Riemannian objects in 3.2.46,
    p. 282. It includes the finite-multiplicity
    alternative without adding measurability or integrability
    of either original weight. *)
Theorem riemannian_area_null_target_weight_change (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=m%:R :> R)%R) (S : set (riemannian_metric_space hg))
    (u U : riemannian_metric_space hh -> real_line_metric R) N :
  is_riemannian_path_lipschitz f -> riemannian_hausdorff_measure hh m%:R hp N=0 ->
  (forall y, (f @` S) y -> ~N y -> U y=u y) ->
  measure_almost_equal (riemannian_hausdorff_measure hg m%:R hp)
    (riemannian_area_source_integrand f S U) (riemannian_area_source_integrand f S u) /\
  measure_almost_equal (riemannian_hausdorff_measure hh m%:R hp)
    (riemannian_area_target_integrand f S U) (riemannian_area_target_integrand f S u).
Proof.
move=>hLip hN hAgree.
have hm := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hb := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
split.
- have hPreNull:=@riemannian_positive_area_null_preimage R m n A B g h hg hh f hp N hLip hN.
  have hOff:measure_almost_everywhere (riemannian_hausdorff_measure hg m%:R hp)
      (~` (positive_riemannian_area_locus f `&` (f @^-1` N))).
    by rewrite /measure_almost_everywhere setCK.
  have hJDom:=measurable_function_domain (@riemannian_area_jacobian_volume_measurable R m n A B g h hg hh f hp hLip).
  apply:(@measure_almost_everywhere_mono R _ _ hm _ _ _
    (measure_almost_everywhere_and hm hOff hJDom))=>x [hx [j hj]].
  case:(pselect (S x))=>hA.
  + case:(pselect (positive_riemannian_area_locus f x))=>hP.
    * have hNotN:~N (f x) by move=>hNfx; apply:hx; split.
      have hImage:(f @` S) (f x) by exists x.
      have hEq:U (f x)=u (f x):=hAgree _ hImage hNotN.
      exists ((u (f x))%:E*j); split; apply:(partial_function_zero_extension_on _ _ _ hA).2;
        apply/partial_density_product_graph.
      -- exists (U (f x))%:E,j; split=>//; split=>//; by rewrite hEq.
      -- exists (u (f x))%:E,j; by split=>//; split.
    * have hj0:j=0:=riemannian_jacobian_zero_outside_positive_locus hP hj.
      exists 0; split; apply:(partial_function_zero_extension_on _ _ _ hA).2;
        apply/partial_density_product_graph.
      -- exists (U (f x))%:E,j; split=>//; split=>//; by rewrite hj0 mule0.
      -- exists (u (f x))%:E,j; split=>//; split=>//; by rewrite hj0 mule0.
  + exists 0; split; apply:(partial_function_zero_extension_off _ _ _ hA).2; by [].
- have hOff:measure_almost_everywhere
      (riemannian_hausdorff_measure hh m%:R hp) (~` N).
    by rewrite /measure_almost_everywhere setCK.
  apply:(@measure_almost_everywhere_mono R _ _ hb _ _ _ hOff)=>y hy.
  case:(pselect ((f @` S) y))=>hImage.
  + exists ((u y)%:E*@mapping_multiplicity R _ _ f S y); split; last by [].
    change ((U y)%:E*@mapping_multiplicity R _ _ f S y=(u y)%:E*@mapping_multiplicity R _ _ f S y).
    by rewrite (hAgree y hImage hy).
  + have hZero:=(@mapping_multiplicity_zero_iff R _ _ f S y).2 hImage.
    exists 0; split.
    * change ((U y)%:E*@mapping_multiplicity R _ _ f S y=0); by rewrite hZero mule0.
    * change ((u y)%:E*@mapping_multiplicity R _ _ f S y=0); by rewrite hZero mule0.
Qed.
