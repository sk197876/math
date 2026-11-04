(** Federer (1969), 3.2.5, p. 245, extended
    by 3.2.46, p. 282: both actual Riemannian area
    integrands depend on the weight only on the original
    image f(S). Exact graph equality retains undefined
    differentials and infinite counting multiplicities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianAreaTransformIntegrands
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_area_image_weight_graph_agreement]:
    exact zero-off-image replacement in 3.2.5, p. 245,
    with the actual original Riemannian map in 3.2.46,
    p. 282. No weight measurability, integral existence
    or finite-fibre premise is required. *)
Lemma riemannian_area_image_weight_graph_agreement (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (S : set (riemannian_metric_space hg))
    (u U : riemannian_metric_space hh -> real_line_metric R) :
  (forall y, (f @` S) y -> U y=u y) ->
  (forall x z, partial_function_graph (riemannian_area_source_integrand f S U) x z <->
    partial_function_graph (riemannian_area_source_integrand f S u) x z) /\
  (forall y z, partial_function_graph (riemannian_area_target_integrand f S U) y z <->
    partial_function_graph (riemannian_area_target_integrand f S u) y z).
Proof.
move=>hAgree.
have hSource (g1 g2:riemannian_metric_space hh->R):
    (forall y,(f @` S) y -> g1 y=g2 y) -> forall x z,
    partial_function_graph (riemannian_area_source_integrand f S g1) x z ->
    partial_function_graph (riemannian_area_source_integrand f S g2) x z.
  move=>he x z hGraph.
  have [[hA hProd]|[hNot hz]]:=(partial_function_zero_extension_graph _ _ _ x z).1 hGraph.
  - apply/partial_function_zero_extension_graph; left; split=>//.
    have [a [j [ha [hj heq]]]]:=(partial_density_product_graph _ _ x z).1 hProd.
    change ((g1 (f x))%:E=a) in ha.
    have hImage:(f @` S) (f x) by exists x.
    rewrite (he _ hImage) in ha.
    apply/partial_density_product_graph; exists a,j; by split=>//; split.
  - apply/partial_function_zero_extension_graph; right; by split.
split.
- move=>x z; split; [exact (hSource U u hAgree x z)|].
  apply:(hSource u U _ x z)=>y hy; symmetry; exact (hAgree y hy).
- move=>y z; change ((U y)%:E*@mapping_multiplicity R _ _ f S y=z <->
    (u y)%:E*@mapping_multiplicity R _ _ f S y=z).
  case:(pselect ((f @` S) y))=>hy.
  + by rewrite (hAgree y hy).
  + have hZero:=(@mapping_multiplicity_zero_iff R _ _ f S y).2 hy.
    by rewrite hZero !mule0.
Qed.
