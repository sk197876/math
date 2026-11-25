(** Federer (1969), 3.2.46, p. 282: the discarded
    ordinary area-Jacobian null sets also have zero
    Riemannian area-Jacobian mass. Use the actual common
    differential and the proved rank-zero equivalence;
    no bounded tensor field or global frame is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLinearJacobian Jacobian EuclideanJacobianMeasurable
  JacobianDensityMeasure RiemannianTensorUP RiemannianLinearJacobian RiemannianTargetJacobian
  RiemannianAreaJacobianNullity PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialExtendedOrderLoci ExtendedRealOrderTopology
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureSubsetIntegral MeasureDensityUP MeasureDensity
  MeasureNonnegativeZero ZeroExtensionNonnegative MeasureConullZeroIntegral LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_area_null_reduction]: a
    Lebesgue-measurable source with zero ordinary Jacobian
    mass has zero actual Riemannian-target Jacobian mass,
    supporting the null reductions in 3.2.46, p. 282.
    The set itself need not have zero Lebesgue mass;
    critical positive-mass regions are retained. *)
Theorem riemannian_area_null_reduction (R : realType) m n A h
    (hh : @is_continuous_riemannian_tensor R n A h)
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (hf : forall x, A (f x)) (S : set (R_n R m)) :
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) S ->
  euclidean_jacobian_measure f S=0%E ->
  measure_with_density (@euclidean_lebesgue_measure R m)
    (@extended_target_riemannian_jacobian R m n A h hh f hf m) S=0%E.
Proof.
move=> hLip hS hNull.
pose X := [the choiceType of inner_metric_space (@euclidean_inner_productP R m)].
pose phi := @euclidean_lebesgue_measure R m.
pose F := extended_euclidean_jacobian f.
pose G := @extended_target_riemannian_jacobian R m n A h hh f hf m.
pose cutF := partial_function_zero_extension (0 : extended_real_line R) S F.
pose cutG := partial_function_zero_extension (0 : extended_real_line R) S G.
have hPhi := euclidean_lebesgue_is_measure R m.
have hIntegral : is_measure_integral phi cutF 0%E.
  have hI := euclidean_jacobian_measure_integral hLip hS.
  by rewrite hNull in hI.
have hPos := @zero_extension_nonnegative_almost R X phi hPhi S F
  (euclidean_jacobian_nonnegative_almost hLip).
have hZero := @nonnegative_integral_zero_almost_equal R X phi hPhi cutF hIntegral hPos.
have hCutZero : measure_almost_everywhere phi [set x | partial_function_graph cutG x 0%E].
  apply: (@measure_almost_everywhere_mono R X phi hPhi _ _ _ hZero)=> x [z [hF hZ]].
  have hz : z=0%E := esym hZ.
  have hF0 : partial_function_graph cutF x 0%E by rewrite -hz.
  case: (pselect (S x))=> hx.
  - apply/partial_function_zero_extension_graph; left; split; first exact hx.
    have hFValue := (@partial_function_zero_extension_on X (extended_real_line R) 0 S F x 0 hx).1 hF0.
    have [r [hR hR0]] := hFValue.
    have hr0 : r=0 by case: hR0.
    rewrite hr0 in hR.
    have [D [hD hJ]] := (euclidean_jacobian_graph m setT f x 0).1 hR.
    have hRZero : riemannian_linear_jacobian (@euclidean_inner_productP R m)
        (riemannian_tensor_inner hh (hf x)) m D=0.
      exact: (@riemannian_area_jacobian_zero_iff R m n (@euclidean_inner_product R m)
        (h (f x)) (@euclidean_inner_productP R m) (riemannian_tensor_inner hh (hf x)) D).2 hJ.
    exists (0 : R); split; last by [].
    apply: (@target_riemannian_jacobian_graph R m n A h hh f hf m x 0).2.
    exists D; by split.
  - apply/partial_function_zero_extension_graph; right; by split.
have hGIntegral := @measure_almost_zero_integral R X phi hPhi cutG hCutZero.
rewrite (measure_with_density_laws phi G S) /measure_subset_upper_integral.
exact (measure_upper_integral_unique (measure_upper_integral_specification phi cutG) hGIntegral.2.1).
Qed.
