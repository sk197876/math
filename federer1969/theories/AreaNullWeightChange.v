(** Federer (1969), 3.2.5, p. 245: ignore a
    Hausdorff-null exceptional set of target weights. On
    positive Jacobian points its inverse image is null;
    other defined Jacobian values are zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP LipschitzUP HausdorffMeasure
  EuclideanJacobianMeasurable PositiveJacobianImageNull PositiveJacobianNullPreimage BorelAreaSelection
  AreaTransformIntegrands MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_null_target_weight_change]: null-set
    weight replacement in the proof of Federer 3.2.5,
    p. 245, including the finite-multiplicity reduction.
    Both conclusions compare actual defined values, not defaults. *)
Theorem area_null_target_weight_change (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g G:R_n R n->R) N:
  is_metric_lipschitz setT f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m N=0 ->
  (forall y,(f @` A) y -> ~N y -> G y=g y) ->
  measure_almost_equal (@euclidean_lebesgue_measure R m)
    (area_transform_source_integrand f A G) (area_transform_source_integrand f A g) /\
  measure_almost_equal (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (area_transform_target_integrand f A G) (area_transform_target_integrand f A g).
Proof.
move=>hLip hN hAgree.
have hm:=euclidean_lebesgue_is_measure R m.
have hb:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
split.
- have hPreNull:=positive_jacobian_null_preimage hLip hN.
  have hOff:measure_almost_everywhere (@euclidean_lebesgue_measure R m)
      (~` (positive_euclidean_jacobian_locus f `&` (f @^-1` N))).
    by rewrite /measure_almost_everywhere setCK.
  have hJDom:=measurable_function_domain (extended_euclidean_jacobian_measurable hLip).
  apply:(@measure_almost_everywhere_mono R _ _ hm _ _ _
    (measure_almost_everywhere_and hm hOff hJDom))=>x [hx [j hj]].
  case:(pselect (A x))=>hA.
  + case:(pselect (positive_euclidean_jacobian_locus f x))=>hP.
    * have hNotN:~N (f x) by move=>h; apply:hx; split.
      have hImage:(f @` A) (f x) by exists x.
      have hEq:G (f x)=g (f x):=hAgree _ hImage hNotN.
      exists ((g (f x))%:E*j); split; apply:(partial_function_zero_extension_on _ _ _ hA).2;
        apply/partial_density_product_graph.
      -- exists (G (f x))%:E,j; split=>//; split=>//; by rewrite hEq.
      -- exists (g (f x))%:E,j; by split=>//; split.
    * have hj0:j=0:=extended_jacobian_zero_outside_positive_locus hP hj.
      exists 0; split; apply:(partial_function_zero_extension_on _ _ _ hA).2;
        apply/partial_density_product_graph.
      -- exists (G (f x))%:E,j; split=>//; split=>//; by rewrite hj0 mule0.
      -- exists (g (f x))%:E,j; split=>//; split=>//; by rewrite hj0 mule0.
  + exists 0; split; apply:(partial_function_zero_extension_off _ _ _ hA).2; by [].
- have hOff:measure_almost_everywhere
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) (~` N).
    by rewrite /measure_almost_everywhere setCK.
  apply:(@measure_almost_everywhere_mono R _ _ hb _ _ _ hOff)=>y hy.
  case:(pselect ((f @` A) y))=>hImage.
  + exists ((g y)%:E*@mapping_multiplicity R _ _ f A y); split; last by [].
    change ((G y)%:E*@mapping_multiplicity R _ _ f A y=(g y)%:E*@mapping_multiplicity R _ _ f A y).
    by rewrite (hAgree y hImage hy).
  + have hZero:=(@mapping_multiplicity_zero_iff R _ _ f A y).2 hImage.
    exists 0; split.
    * change ((G y)%:E*@mapping_multiplicity R _ _ f A y=0); by rewrite hZero mule0.
    * change ((g y)%:E*@mapping_multiplicity R _ _ f A y=0); by rewrite hZero mule0.
Qed.
