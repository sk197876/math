(** Federer (1969), 3.2.20, p. 257: the first displayed
    Jacobian identity identifies the two parameter-space integrands
    before the two transformations of integrals are applied. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP EuclideanLinearJacobian Jacobian EuclideanJacobianMeasurable ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic AreaExtendedTransformIntegrands.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_parameter_chain_integrand_agreement]: supporting
    almost equality of the source integrands in Federer 3.2.20,
    p. 257. The actual Jacobian chain identity is a premise of
    this algebraic adapter and is proved by the chart differential
    theorem in the application. Extended signed weights are allowed. *)
Lemma area_parameter_chain_integrand_agreement (R : realType) m n k
    (mu : set (R_n R m) -> \bar R) (hm : is_measure mu)
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n)
    (F : R_n R n -> R_n R k) (J0 : R_n R n -> R) :
  measure_almost_everywhere_on mu K [set a|
    exists (D : Hom (R_n R m) (R_n R n)) (H : Hom (R_n R m) (R_n R k)),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT psi a D /\
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H /\
      (J0 (psi a)*euclidean_linear_jacobian m D=euclidean_linear_jacobian m H)%R] ->
  forall (g : R_n R k -> \bar R), measure_almost_equal mu
    (area_extended_source_integrand (fun x=>F (psi x)) K g)
    (area_extended_source_integrand psi K (fun w=>g (F w)* (J0 w)%:E)).
Proof.
move=> hChain g.
have hImp := (@measure_almost_everywhere_on_implication R _ mu K _).1 hChain.
apply: (@measure_almost_everywhere_mono R _ mu hm _ _ _ hImp)=> a hAt.
case: (pselect (K a))=> ha.
- have [D [H [hD [hH hProduct]]]] := hAt ha.
  have hDJ : partial_function_graph (extended_euclidean_jacobian psi) a
      (euclidean_linear_jacobian m D)%:E.
    exists (euclidean_linear_jacobian m D); split; last reflexivity.
    apply: (euclidean_jacobian_graph m setT psi a _).2; exists D; by split.
  have hHJ : partial_function_graph (extended_euclidean_jacobian (fun x=>F (psi x))) a
      (euclidean_linear_jacobian m H)%:E.
    exists (euclidean_linear_jacobian m H); split; last reflexivity.
    apply: (euclidean_jacobian_graph m setT (fun x=>F (psi x)) a _).2; exists H; by split.
  exists (g (F (psi a))* (euclidean_linear_jacobian m H)%:E); split.
  + apply: (partial_function_zero_extension_on _ _ _ ha).2.
    apply/partial_density_product_graph; exists (g (F (psi a))), (euclidean_linear_jacobian m H)%:E.
    split; first reflexivity; by split.
  + apply: (partial_function_zero_extension_on _ _ _ ha).2.
    apply/partial_density_product_graph; exists (g (F (psi a))* (J0 (psi a))%:E), (euclidean_linear_jacobian m D)%:E.
    split; first reflexivity.
    split; first exact hDJ.
    by rewrite -muleA -EFinM hProduct.
- exists 0; split; apply: (partial_function_zero_extension_off _ _ _ ha).2; reflexivity.
Qed.
