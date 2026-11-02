(** Federer (1969), 2.5.10, pp. 100–101: measurability of the density
    obtained by gluing local representations. The family need not be
    countable; measurability follows from countable coverage of each finite
    test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureRestriction MeasureAlmostBasic MeasurableFunctionUP TotalScalarLpUP
  FiniteMeasureDecompositionUP FiniteCoverMeasurability MeasurableRestrictionTransfer
  DisjointFunctionGluingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [disjoint_density_gluing_measurable]: supporting
    measurable-density conclusion of Federer 2.5.10, pp. 100–101 Each local
    density need only be measurable for the measure restricted to its own
    piece. *)
Theorem disjoint_density_gluing_measurable (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (B : J -> set X)
    (f : J -> X -> R) (g : X -> R) :
  is_finite_measure_decomposition mu D B -> is_disjoint_function_gluing D B f g ->
  (forall j, D j -> is_measure_measurable_function (measure_restrict mu (B j)) (total_scalar_function (f j))) ->
  is_measure_measurable_function mu (total_scalar_function g).
Proof.
move=> hD hg hf; constructor.
- rewrite /total_scalar_function partial_function_total_domain; exact: measure_almost_everywhere_true hm.
- move=> U hU; rewrite /total_scalar_function partial_function_total_preimage.
  apply: (@finite_cover_measurable_from_pieces R X J mu hm D B _ hD.2.2)=> j hj.
  have hlocal := @measurable_function_open_preimage R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (measure_restrict mu (B j)) (total_scalar_function (f j)) (hf j hj) U hU.
  rewrite /total_scalar_function partial_function_total_preimage in hlocal.
  have he : (g @^-1` U) `&` B j=(f j @^-1` U) `&` B j.
    apply/seteqP; split=> x [hx hb]; split=> //.
    + change (U (f j x)); rewrite -(hg.1 j x hj hb); exact: hx.
    + change (U (g x)); rewrite (hg.1 j x hj hb); exact: hx.
  rewrite he; exact: (@measurable_restriction_intersection_transfer R X mu hm _ _ (hD.1 j hj).1 hlocal).
Qed.
