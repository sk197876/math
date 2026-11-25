(** Federer (1969), 3.2.5, p. 245: the
    transformation identity depends on g only on f(A).
    Replacing g by zero off that image preserves both
    exact integrand graphs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension PartialDensityProduct AreaTransformIntegrands MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_image_weight_graph_agreement]: the
    zero-off-f(A) reduction at the beginning of the proof
    of Federer 3.2.5, p. 245. No measurability or
    integral existence is required for these graph identities. *)
Lemma area_image_weight_graph_agreement (R:realType) m n (f:R_n R m->R_n R n)
    A (g G:R_n R n->R):
  (forall y,(f @` A) y -> G y=g y) ->
  (forall x z,partial_function_graph (area_transform_source_integrand f A G) x z <->
    partial_function_graph (area_transform_source_integrand f A g) x z) /\
  (forall y z,partial_function_graph (area_transform_target_integrand f A G) y z <->
    partial_function_graph (area_transform_target_integrand f A g) y z).
Proof.
move=>hAgree.
have hSource (g1 g2:R_n R n->R):
    (forall y,(f @` A) y -> g1 y=g2 y) -> forall x z,
    partial_function_graph (area_transform_source_integrand f A g1) x z ->
    partial_function_graph (area_transform_source_integrand f A g2) x z.
  move=>he x z hGraph.
  have [[hA hProd]|[hNot hz]]:=(partial_function_zero_extension_graph _ _ _ x z).1 hGraph.
  - apply/partial_function_zero_extension_graph; left; split=>//.
    have [a [j [ha [hj heq]]]]:=(partial_density_product_graph _ _ x z).1 hProd.
    change ((g1 (f x))%:E=a) in ha.
    have hImage:(f @` A) (f x) by exists x.
    rewrite (he _ hImage) in ha.
    apply/partial_density_product_graph; exists a,j; by split=>//; split.
  - apply/partial_function_zero_extension_graph; right; by split.
split.
- move=>x z; split; [exact (hSource G g hAgree x z)|].
  apply:(hSource g G _ x z)=>y hy; symmetry; exact (hAgree y hy).
- move=>y z; change ((G y)%:E*@mapping_multiplicity R _ _ f A y=z <->
    (g y)%:E*@mapping_multiplicity R _ _ f A y=z).
  case:(pselect ((f @` A) y))=>hy.
  + by rewrite (hAgree y hy).
  + have hZero:=(@mapping_multiplicity_zero_iff R _ _ f A y).2 hy.
    by rewrite hZero !mule0.
Qed.
