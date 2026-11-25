(** Federer (1969), 4.1.9, pp. 363–364: apply
    the original 2.6.2 Fubini theorem to actual product
    current domains and their original Radon measures.
    The preceding compact exhaustions supply the countable
    hypotheses. Retain partial section integrals and infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentDomain CurrentCartesianDomain
  CurrentCartesianDomainMapsSealed CurrentCartesianMeasureSealed CurrentCartesianMeasureRadon CurrentDomainRadonSigmaFinite
  MeasureUP RadonMeasureUP CountablyMeasurableUP CountablyMeasurableFunctions CountablyMeasurableProduct
  PartialFunctionUP PartialFunctionPrecomposition PartialProductSections ParameterizedIntegral
  CountablyMeasurableNullModification MeasureIntegralUP MeasureBijectionIntegralTransport ProductMeasure ProductFunctionFubini ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section CurrentCartesianRadonFubini.
Variable R:realType.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) (@euclidean_cartesian_set R m n A B)).
Local Notation PT := (Choice.clone (AT*BT)%type _).
Variables (alpha:set AT->\bar R) (beta:set BT->\bar R).
Hypothesis hAlpha:is_measure alpha.
Hypothesis hBeta:is_measure beta.
Hypothesis hARadon:is_radon_measure alpha.
Hypothesis hBRadon:is_radon_measure beta.
Local Notation lambda := (@CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta).
Local Notation J := (@CartesianCurrentDomain.join R m n A B).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).
Local Notation mu := (product_measure hAlpha hBeta).
Local Notation hm := (product_measure_is_measure hAlpha hBeta).

(** Source for [current_cartesian_radon_vertical_fubini]:
    the original product-domain integral equals its actual
    iterated factor integral, supporting the represented
    homotopy formula in Federer 4.1.9, pp. 363–364,
    by 2.6.2(4), pp. 115, 117. No finiteness of
    either whole factor or of the integral is added. *)
Theorem current_cartesian_radon_vertical_fubini
    (f:partial_function CT (extended_real_line R)) a:
  is_measure_integral lambda f a->
  is_measure_integral alpha (parameterized_integral beta
    (partial_product_vertical_section (partial_function_precompose J f))) a.
Proof.
move=>hIntegral.
have hProduct:=(@measure_bijection_integral_iff R PT CT mu lambda hm J D
  (@current_cartesian_measure_bijection R m n A B alpha beta hAlpha hBeta) f a).2 hIntegral.
have hCount:=@product_whole_countably_measurable R AT BT alpha beta hAlpha hBeta
  (@current_domain_radon_countably_measurable R m A hA alpha hAlpha hARadon)
  (@current_domain_radon_countably_measurable R n B hB beta hBeta hBRadon).
have hFunction:=countably_measurable_function_on_countable_source hm
  (@CountablyMeasurableNullModification.extended_real_zero_closed R) hCount hProduct.1.
exact:(@product_function_fubini R AT BT alpha beta hAlpha hBeta _ a hProduct hFunction).1.
Qed.
End CurrentCartesianRadonFubini.
