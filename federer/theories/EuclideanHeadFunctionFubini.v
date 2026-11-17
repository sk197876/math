(** Federer 2.10.27, p. 191: supporting scalar-coordinate Fubini
    connection for the real ball-section integral. Reuse the actual
    Euclidean product measure from 2.6.5 and function Fubini from
    2.6.2(4); no new product measure or integrability premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanCoordinateSplit EuclideanHeadSectionIntegral LebesgueScalarMeasure
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition PartialProductSections
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasurePushforward PushforwardIntegral CountablyMeasurableUP CountablyMeasurableFunctions
  CountablyMeasurableProduct CountablyMeasurableNullModification ProductMeasure ProductFunctionFubini ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_head_function_fubini]: the scalar-section
    integral underlying Federer 2.10.27, p. 191. The first scalar
    coordinate is split from its remaining natural-dimensional base;
    the actual inner integral retains its complete partial domain.
    Include the zero-dimensional base. *)
Theorem euclidean_head_function_fubini (R:realType) n
    (f:partial_function (inner_metric_space (@euclidean_inner_productP R n.+1))
      (extended_real_line R)) a:
  is_measure_integral (@euclidean_lebesgue_measure R n.+1) f a ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (parameterized_integral (@lebesgue_scalar_measure R)
      (partial_product_vertical_section (partial_function_precompose (@euclidean_join R n) f))) a.
Proof.
move=> hI.
pose F:=partial_function_precompose (@euclidean_join R n) f.
have hPre:is_measure_integral (@euclidean_lebesgue_measure R n.+1)
    (partial_function_precompose (@euclidean_split R n) F) a.
  apply:(measure_integral_graph_equivalent _ hI)=>x z.
  change (partial_function_graph f x z <->
    partial_function_graph f (euclidean_join (euclidean_split x)) z).
  by rewrite euclidean_splitK.
have hPush:=(@measure_pushforward_integral_iff R _ _
  (@euclidean_lebesgue_measure R n.+1) (euclidean_lebesgue_is_measure R n.+1)
  (@euclidean_split R n) F hPre.1 a).1 hPre.
rewrite euclidean_head_split_measure in hPush.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose ha:=euclidean_lebesgue_is_measure R n.
pose hb:=lebesgue_scalar_is_measure R.
have hWhole:=@product_whole_countably_measurable R [the choiceType of X] R
  (@euclidean_lebesgue_measure R n) (@lebesgue_scalar_measure R) ha hb
  (euclidean_lebesgue_countably_measurable R n) (lebesgue_scalar_countably_measurable R).
have hCount:=countably_measurable_function_on_countable_source
  (product_measure_is_measure ha hb) (@extended_real_zero_closed R) hWhole hPush.1.
exact (@product_function_fubini R [the choiceType of X] R
  (@euclidean_lebesgue_measure R n) (@lebesgue_scalar_measure R) ha hb F a hPush hCount).1.
Qed.
