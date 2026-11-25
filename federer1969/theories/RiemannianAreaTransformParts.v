(** Federer (1969), 3.2.5, p. 245, extended by
    3.2.46, p. 282: exact signed-part identities for
    the two actual Riemannian area integrands. Their
    partial domains and infinite target multiplicities remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealPartial ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianMapJacobian RiemannianAreaTransformIntegrands
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialZeroExtension PartialDensityProduct
  MappingMultiplicity ExtendedRealPartsScale MeasureUpperIntegralPositivePart PartialFunctionIntegralParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section Parts.
Context (R : realType) m n A B g h
  (hg : @is_continuous_riemannian_tensor R m A g)
  (hh : @is_continuous_riemannian_tensor R n B h)
  (f : riemannian_metric_space hg -> riemannian_metric_space hh)
  (S : set (riemannian_metric_space hg))
  (u : riemannian_metric_space hh -> real_line_metric R).

(** Source for [riemannian_extended_area_jacobian_nonnegative]:
    pointwise nonnegativity of each actual exterior-norm
    value in 3.2.46, p. 282, supporting the signed
    parts used in 3.2.5, p. 245. *)
Lemma riemannian_extended_area_jacobian_nonnegative x j :
  partial_function_graph (extended_riemannian_map_jacobian f m) x j -> 0<=j.
Proof.
move=> [r [hr <-]].
rewrite lee_fin; exact: riemannian_map_jacobian_nonnegative hr.
Qed.

(** Source for [riemannian_area_transform_source_part_graph]:
    exact source positive/negative-part identity in 3.2.5,
    p. 245, with actual Riemannian Jacobian as required
    by 3.2.46, p. 282. Undefined differentials retain
    their original domain. *)
Lemma riemannian_area_transform_source_part_graph (p : R -> R)
    (q : extended_real_line R -> extended_real_line R) :
  q 0=0 -> (forall c j, 0<=j -> q (c%:E*j)=(p c)%:E*j) -> forall x z,
  partial_function_graph (riemannian_area_source_integrand f S (fun y=>p (u y))) x z <->
  partial_function_graph (partial_function_postcompose (riemannian_area_source_integrand f S u) q) x z.
Proof.
move=>hq0 hq x z; case:(pselect (S x))=>hA; split.
- move=>hValueProof; have hProd:partial_function_graph
      (partial_density_product (partial_function_total (fun x=>(p (u (f x)))%:E:extended_real_line R))
        (extended_riemannian_map_jacobian f m)) x z:=
      (partial_function_zero_extension_on _ _ _ hA).1 hValueProof.
  have [a [j [ha [hj he]]]]:=(partial_density_product_graph _ _ x z).1 hProd.
  change ((p (u (f x)))%:E=a) in ha; rewrite -ha in he.
  exists ((u (f x))%:E*j); split.
  + apply:(partial_function_zero_extension_on _ _ _ hA).2.
    apply/partial_density_product_graph; exists (u (f x))%:E,j; by split=>//; split.
  + by rewrite (hq _ _ (riemannian_extended_area_jacobian_nonnegative hj)) he.
- move=>[v [hv hqv]].
  have hProd:partial_function_graph
      (partial_density_product (partial_function_total (fun x=>(u (f x))%:E:extended_real_line R))
        (extended_riemannian_map_jacobian f m)) x v:=
      (partial_function_zero_extension_on _ _ _ hA).1 hv.
  have [a [j [ha [hj he]]]]:=(partial_density_product_graph _ _ x v).1 hProd.
  change ((u (f x))%:E=a) in ha; rewrite -ha in he.
  apply:(partial_function_zero_extension_on _ _ _ hA).2.
  apply/partial_density_product_graph; exists (p (u (f x)))%:E,j; split=>//; split=>//.
  by rewrite -hqv -he (hq _ _ (riemannian_extended_area_jacobian_nonnegative hj)).
- move=>hValueProof; have hz:z=0:=(partial_function_zero_extension_off _ _ _ hA).1 hValueProof.
  exists 0; split; last by rewrite hq0 hz.
  apply:(partial_function_zero_extension_off _ _ _ hA).2; by [].
- move=>[v [hv hz]]; have hv0:v=0:=(partial_function_zero_extension_off _ _ _ hA).1 hv.
  apply:(partial_function_zero_extension_off _ _ _ hA).2.
  by rewrite -hz hv0 hq0.
Qed.

(** Source for [riemannian_area_transform_target_part_graph]:
    exact target multiplicity part identity in 3.2.5,
    p. 245, supporting 3.2.46, p. 282. The
    distinguished product retains zero weights on infinite
    fibres; signed infinity differences are not assigned. *)
Lemma riemannian_area_transform_target_part_graph (p : R -> R)
    (q : extended_real_line R -> extended_real_line R) :
  (forall c j, 0<=j -> q (c%:E*j)=(p c)%:E*j) -> forall y z,
  partial_function_graph (riemannian_area_target_integrand f S (fun y=>p (u y))) y z <->
  partial_function_graph (partial_function_postcompose (riemannian_area_target_integrand f S u) q) y z.
Proof.
move=>hq y z.
change ((p (u y))%:E*@mapping_multiplicity R _ _ f S y=z <->
  exists v,(u y)%:E*@mapping_multiplicity R _ _ f S y=v /\ q v=z).
split.
- move=>hz; exists ((u y)%:E*@mapping_multiplicity R _ _ f S y); split=>//.
  by rewrite (hq _ _ (@mapping_multiplicity_nonnegative R _ _ f S y)) hz.
- move=>[v [<- hz]]; by rewrite (hq _ _ (@mapping_multiplicity_nonnegative R _ _ f S y)) in hz.
Qed.
End Parts.
