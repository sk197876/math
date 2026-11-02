(** Federer (1969), 3.1.3(4), p. 213: Fubini supplies measurable
    scalar sections almost everywhere. The countable rational-ray tests
    from 2.3.2(2) permit one common exceptional null set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialProductSections ProductSections
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  ProductMeasure ProductSetFubini ProductNullFubini CountablyMeasurableUP
  CountablyMeasurableSubsets CountablyMeasurableProduct MeasurableOrderRays
  CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_almost_measurable_order_sections]: the
    almost-everywhere section-measurability step in Federer 3.1.3(4),
    p. 213, by 2.6.2 and the ray criterion of 2.3.2(2). This supporting
    version permits any countable order-dense family and sigma-finite
    factor measures, and keeps every section's original domain. *)
Theorem product_almost_measurable_order_sections (R : realType) (X Y : choiceType)
    disp (Z : orderTopologicalType disp) (J : countType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (d : J -> Z) (f : partial_function (X*Y) Z) :
  measure_countably_measurable alpha setT ->
  measure_countably_measurable beta setT -> is_order_dense_family d ->
  is_measure_measurable_function (product_measure ha hb) f ->
  measure_almost_everywhere beta [set y |
    is_measure_measurable_function alpha (partial_product_horizontal_section f y)].
Proof.
move=> hca hcb hd hf.
have hdom := @product_null_horizontal_sections R X Y alpha beta ha hb
  (~` partial_function_domain f) (measurable_function_domain hf).
change (measure_almost_everywhere beta [set y | measure_almost_everywhere alpha
  (partial_function_domain (partial_product_horizontal_section f y))]) in hdom.
have hq j : measure_almost_everywhere beta [set y | measure_measurable alpha
    (partial_function_preimage (partial_product_horizontal_section f y) [set z | (z<d j)%O])].
  have hS := @measurable_function_open_preimage R (X*Y)%type Z
    (product_measure ha hb) f hf [set z | (z<d j)%O]
    (@order_strict_lower_ray_open disp Z (d j)).
  have hc : measure_countably_measurable (product_measure ha hb)
      (partial_function_preimage f [set z | (z<d j)%O]).
    apply: (measurable_subset_countably_measurable (product_measure_is_measure ha hb)
      hS (fun p _=>Logic.I)).
    exact: product_whole_countably_measurable hca hcb.
  exact: (@product_set_fubini R X Y alpha beta ha hb _ hc).2.1.
have hall := @measure_almost_everywhere_countable R Y J beta hb setT
  (fun j=>[set y | measure_measurable alpha
    (partial_function_preimage (partial_product_horizontal_section f y) [set z | (z<d j)%O])])
  (countableP _) (fun j _=>hq j).
have hboth := measure_almost_everywhere_and hb hdom hall.
apply: (@measure_almost_everywhere_mono R Y beta hb _ _ _ hboth)=> y [hy hys].
apply: (measurable_order_dense_rays_iff ha hd hy).2=> j.
exact: hys j Logic.I.
Qed.
