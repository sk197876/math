(** Federer (1969), 3.2.33, p. 270: the actual
    original-domain integral over X outside the positive-fibre
    preimage is strictly positive. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanOpenUnitCube
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionSourceRestriction
  MeasureUP MeasureRestriction HausdorffMeasure HausdorffClosedCoverAgreement BorelRegularMeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureSubsetIntegral MeasureSubsetConstantIntegral
  SubsetIntegralAlmostAgreement ExtendedRealOrderTopology MeasureApproximateJacobian RectifiablePositiveFibreCoareaUP
  DenseSmallIntervalFamilyUP IntervalBumpPrimitiveUP ScalarCylinderMapUP ScalarCylinderCriticalMass
  ScalarCylinderCriticalJacobian ScalarCylinderPositiveFibre.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_cylinder_positive_remainder_integral]:
    the strict inequality in the last display of the smooth
    example of Federer 3.2.33, p. 270. Its actual
    integral equals H^m(X)=L^1(T minus V)>0, since
    Y is empty and the public approximate Jacobian is one
    everywhere on X. Characteristic integration and graph
    agreement prove integrability before any value is used.
    All dimensions mu<m, including mu= 0 and k= 0, remain. *)
Theorem scalar_cylinder_positive_remainder_integral (R:realType) mu k (a b:nat->R) (psi g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->is_dense_small_interval_family a b ->is_interval_bump_primitive a b psi g ->
  let f:=partial_function_source_restrict (@euclidean_open_unit_cube R ((mu+1)+k)) (partial_function_total F) in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k) in
  let X:=partial_approximate_image_dimension_locus ((mu+1)+k) mu f in
  is_measure_subset_integral H (X `\` partial_function_preimage f (positive_partial_fibre_locus ((mu+1)+k) mu f))
    (extended_measure_approximate_jacobian (measure_restrict H (partial_function_domain f)) ((mu+1)+k) mu f) (H X) /\
  (0<H X)%E.
Proof.
move=>hF hFamily hPrimitive f H X.
have hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k).
have [hXB [hMass hPositive]]:=scalar_cylinder_critical_source_mass hF hFamily hPrimitive.
split; last exact hPositive.
have hY:=scalar_cylinder_original_positive_fibre_empty hF hPrimitive.
rewrite /f hY partial_function_preimage_empty setD0.
have hXMeas:measure_measurable H X.
  exact:(borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R
    (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k)) hXB).
have hConstant:=@measure_nonnegative_constant_subset_integral R
  [the choiceType of (R_n R ((mu+1)+k):Type)] H X 1%E hH hXMeas (ltac:(by rewrite lee_fin)).
rewrite mul1e in hConstant.
apply:(subset_integral_almost_agreement hH _ hConstant).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hH _ (measure_almost_everywhere_true hH))=>x _ hx.
exists (1%E:extended_real_line R); split; first reflexivity.
exact:(scalar_cylinder_critical_jacobian_one hF hPrimitive hx).
Qed.
