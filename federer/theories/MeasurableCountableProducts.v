(** Federer (1969), 2.3.2(5), p. 73: coordinatewise measurability for
    countable products with countable factor bases. We use only the sealed
    refinement specification and local measurable-set closure. it cannot be
    inferred from an empty family of projections. *)
From mathcomp Require Import all_boot finmap classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPreimages PartialFunctionPostcomposition
  CountableOpenBaseUP CountableProductCylindersUP CountableProductCylindersSealed
  MeasureUP MeasureFiniteClosure MeasureCountableClosure MeasureAlmostUP
  MeasurableFunctionUP MeasurableFunctionBorel MeasurablePostcomposition BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Import ArrowAsProduct.

(** Source for [measurable_product_cylinder_preimage]: supporting
    finite-cylinder step in Federer 2.3.2(5), p. 73. The domain intersection
    is retained for an empty cylinder family. *)
Lemma measurable_product_cylinder_preimage (R : realType) (X I : choiceType)
    (Y : I -> topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (prod_topology Y)) (U : forall i, nat -> set (Y i)) :
  (forall i, is_countable_open_base (U i)) ->
  measure_almost_everywhere mu (partial_function_domain f) ->
  (forall i, is_measure_measurable_function mu (partial_function_postcompose f (fun y => y i))) ->
  forall W, finI_from (product_coordinate_cylinders U) id W ->
    measure_measurable mu (partial_function_preimage f W).
Proof.
move=> hU hd hf W [D hD <-].
rewrite partial_function_preimage_intersection.
apply: (@measure_measurable_intersection R X mu hm _ _
  (@conull_partial_function_domain_measurable R X _ mu hm f hd)).
apply: (@measure_measurable_countable_intersection R X _ mu hm _ _
  (finite_set_countable (finite_fset D)))=> C hC.
have [i _ [n _ <-]] := set_mem (hD C hC).
have h := measurable_function_open_preimage (hf i) (countable_base_open (hU i) n).
by rewrite partial_function_postcompose_preimage in h.
Qed.

(** Source for [measurable_function_countable_product_iff]: direct Federer
    2.3.2(5), p. 73 A countable abstract index type and enumerated factor
    bases are supplied. The separate conull-domain premise also handles the
    empty index set without a vacuous inference. *)
Theorem measurable_function_countable_product_iff (R : realType) (X I : choiceType)
    (Y : I -> topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (prod_topology Y)) (U : forall i, nat -> set (Y i)) :
  countable (@setT I) -> (forall i, is_countable_open_base (U i)) ->
  measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <->
   forall i, is_measure_measurable_function mu (partial_function_postcompose f (fun y => y i))).
Proof.
move=> hi hU hd; split.
- move=> hf i; apply: (@measurable_function_borel_postcomposition R X _ _ mu hm f _ hf).
  apply: continuous_borel_function; exact: proj_continuous.
- move=> hf; constructor=> // V ho.
  pose B := @CountableProductCylinders.value I Y U hi hU.
  have hB := @CountableProductCylinders.laws I Y U hi hU.
  pose D := [set W | B W /\ W `<=` V].
  have hc : countable D.
    apply: sub_countable _ (product_cylinder_refinement_countable hB).
    apply: subset_card_le=> W [hW _]; exact hW.
  have he : V = \bigcup_(W in D) W.
    apply/seteqP; split=> x.
    + move=> hx; have [W [hW [hxW hWV]]] := product_cylinder_refinement_local hB ho hx.
      exists W=> //; by split.
    + by move=> [W [_ hWV] hx]; exact: hWV hx.
  rewrite he partial_function_preimage_union.
  apply: (@measure_measurable_countable_union R X _ mu hm _ _ hc)=> W [hW _].
  exact: (@measurable_product_cylinder_preimage R X I Y mu hm f U hU hd hf W
    (product_cylinder_refinement_finite hB hW)).
Qed.
