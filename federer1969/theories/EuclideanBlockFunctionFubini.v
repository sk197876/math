(** Federer (1969), 3.2.10, p. 248: transfer a
    Euclidean integral to its iterated coordinate integrals.
    Euclidean sigma finiteness supplies the hypotheses of
    2.6.2(4), pp. 115, 117, including infinite integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanBlockCoordinates EuclideanBlockIntegral
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition PartialProductSections
  MeasureUP MeasurableFunctionUP MeasureIntegralUP CountablyMeasurableUP CountablyMeasurableFunctions
  CountablyMeasurableProduct CountablyMeasurableNullModification ProductMeasure ProductFunctionFubini ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_block_function_fubini]: the
    iterated integral step in Federer 3.2.10, p. 248.
    The original partial integrand is retained, and the inner
    integral is defined exactly on its actual integrability domain. *)
Theorem euclidean_block_function_fubini (R:realType) n k
    (f:partial_function (inner_metric_space (@euclidean_inner_productP R (n+k))) (extended_real_line R)) a:
  is_measure_integral (@euclidean_lebesgue_measure R (n+k)) f a ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (parameterized_integral (@euclidean_lebesgue_measure R k)
      (partial_product_vertical_section (partial_function_precompose (@euclidean_block_join R n k) f))) a.
Proof.
move=>hI.
have hProduct:=euclidean_block_integral_transfer hI.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R k).
pose ha:=euclidean_lebesgue_is_measure R n.
pose hb:=euclidean_lebesgue_is_measure R k.
have hWhole:=@product_whole_countably_measurable R [the choiceType of X] [the choiceType of Y]
  (@euclidean_lebesgue_measure R n) (@euclidean_lebesgue_measure R k) ha hb
  (euclidean_lebesgue_countably_measurable R n) (euclidean_lebesgue_countably_measurable R k).
have hCount:=countably_measurable_function_on_countable_source
  (product_measure_is_measure ha hb) (@extended_real_zero_closed R) hWhole hProduct.1.
exact (@product_function_fubini R [the choiceType of X] [the choiceType of Y]
  (@euclidean_lebesgue_measure R n) (@euclidean_lebesgue_measure R k) ha hb _ a hProduct hCount).1.
Qed.
