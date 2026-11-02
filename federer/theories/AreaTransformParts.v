(** Federer (1969), 3.2.5, p. 245: apply
    2.4.4(6) to the source and target integrands.
    Their parts use the corresponding parts of the finite
    real weight, including infinite multiplicity and zero weight. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations ExtendedRealPartial ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialZeroExtension PartialDensityProduct
  EuclideanJacobianMeasurable AreaTransformIntegrands MappingMultiplicity MappingMultiplicityLaws
  ExtendedRealPartsScale MeasureUpperIntegralPositivePart PartialFunctionIntegralParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_transform_source_part_graph]: supporting
    source part identity in Federer 3.2.5, p. 245.
    The identity is proved on the exact partial graph,
    before applying an integral law. *)
Lemma area_transform_source_part_graph (R:realType) m n (f:R_n R m->R_n R n)
    A (g:R_n R n->R) (p:R->R) (q:extended_real_line R->extended_real_line R):
  q 0=0 -> (forall c j,0<=j -> q (c%:E*j)=(p c)%:E*j) -> forall x z,
  partial_function_graph (area_transform_source_integrand f A (fun y=>p (g y))) x z <->
  partial_function_graph (partial_function_postcompose (area_transform_source_integrand f A g) q) x z.
Proof.
move=>hq0 hq x z; case:(pselect (A x))=>hA; split.
- move=>h; have hProd:partial_function_graph
      (partial_density_product (partial_function_total (fun x=>(p (g (f x)))%:E:extended_real_line R))
        (extended_euclidean_jacobian f)) x z:=
      (partial_function_zero_extension_on _ _ _ hA).1 h.
  have [a [j [ha [hj he]]]]:=(partial_density_product_graph _ _ x z).1 hProd.
  change ((p (g (f x)))%:E=a) in ha; rewrite -ha in he.
  exists ((g (f x))%:E*j); split.
  + apply:(partial_function_zero_extension_on _ _ _ hA).2.
    apply/partial_density_product_graph; exists (g (f x))%:E,j; by split=>//; split.
  + by rewrite (hq _ _ (extended_euclidean_jacobian_nonnegative hj)) he.
- move=>[v [hv hqv]].
  have hProd:partial_function_graph
      (partial_density_product (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R))
        (extended_euclidean_jacobian f)) x v:=
      (partial_function_zero_extension_on _ _ _ hA).1 hv.
  have [a [j [ha [hj he]]]]:=(partial_density_product_graph _ _ x v).1 hProd.
  change ((g (f x))%:E=a) in ha; rewrite -ha in he.
  apply:(partial_function_zero_extension_on _ _ _ hA).2.
  apply/partial_density_product_graph; exists (p (g (f x)))%:E,j; split=>//; split=>//.
  by rewrite -hqv -he (hq _ _ (extended_euclidean_jacobian_nonnegative hj)).
- move=>h; have hz:z=0:=(partial_function_zero_extension_off _ _ _ hA).1 h.
  exists 0; split; last by rewrite hq0 hz.
  apply:(partial_function_zero_extension_off _ _ _ hA).2; by [].
- move=>[v [hv hz]]; have hv0:v=0:=(partial_function_zero_extension_off _ _ _ hA).1 hv.
  apply:(partial_function_zero_extension_off _ _ _ hA).2.
  by rewrite -hz hv0 hq0.
Qed.

(** Source for [area_transform_target_part_graph]: supporting
    multiplicity-integrand part identity in Federer 3.2.5,
    p. 245, using nonnegativity of N and 2.1.1(11).
    Multiplicity may be infinite. *)
Lemma area_transform_target_part_graph (R:realType) m n (f:R_n R m->R_n R n)
    A (g:R_n R n->R) (p:R->R) (q:extended_real_line R->extended_real_line R):
  (forall c j,0<=j -> q (c%:E*j)=(p c)%:E*j) -> forall y z,
  partial_function_graph (area_transform_target_integrand f A (fun y=>p (g y))) y z <->
  partial_function_graph (partial_function_postcompose (area_transform_target_integrand f A g) q) y z.
Proof.
move=>hq y z.
change ((p (g y))%:E*@mapping_multiplicity R _ _ f A y=z <->
  exists v,(g y)%:E*@mapping_multiplicity R _ _ f A y=v /\ q v=z).
split.
- move=>hz; exists ((g y)%:E*@mapping_multiplicity R _ _ f A y); split=>//.
  by rewrite (hq _ _ (@mapping_multiplicity_nonnegative R _ _ f A y)) hz.
- move=>[v [<- hz]]; by rewrite (hq _ _ (@mapping_multiplicity_nonnegative R _ _ f A y)) in hz.
Qed.
