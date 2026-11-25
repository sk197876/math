(**  Federer (1969), 3.2.6, p. 246: almost
    every level satisfies the signed multiplicity identity.
    This combines regularity and finiteness of the actual
    fibre with the ordered crossing calculation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground LocallyAbsolutelyContinuousCurve ScalarRegularFibresAlmost
  ScalarSignedFibreCount ScalarCurveDerivativeLoci EndpointLevelSigns MappingMultiplicity
  ScalarAbsoluteContinuousArea PartialFunctionUP PartialFunctionBasic PartialDensityProduct PartialExtendedArithmetic
  PartialSimpleIntegralError MeasureUP MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(**  Source for [scalar_signed_multiplicity_almost]: the
    almost-everywhere difference of the two counting functions
    in Federer 3.2.6, p. 246. The formula includes
    equal and reversed endpoint values. *)
Theorem scalar_signed_multiplicity_almost (R:realType) (f:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) -> a<b ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set y|exists p q:R,
    @mapping_multiplicity R [the choiceType of real_line_metric R] R f (scalar_positive_derivative_set f a b) y=p%:E /\
    @mapping_multiplicity R [the choiceType of real_line_metric R] R f (scalar_negative_derivative_set f a b) y=q%:E /\
    p-q=oriented_level_indicator (f a) (f b) y].
Proof.
move=>hAC hab; have hm:=lebesgue_scalar_is_measure R.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ (scalar_regular_fibres_almost hAC hab))=>y [hF hR].
exact (scalar_regular_level_signed_multiplicity hab
  (locally_absolutely_continuous_curve_continuous hAC) hF hR).
Qed.

(**  Source for [scalar_oriented_interval_integrand]: the
    target g on the oriented interval from f(a) to f(b)
    in Federer 3.2.6, pp. 245–246. For increasing
    endpoints this is the ordinary interval cutoff almost
    everywhere; reversal changes its sign. *)
Definition scalar_oriented_interval_integrand (R:realType) (g:R->R) (a b:R):=
  partial_function_total (fun y:R=>(g y * oriented_level_indicator a b y)%:E).

(**  Source for [scalar_signed_target_sign_split]: the last
    target subtraction in Federer 3.2.6, p. 246.
    Finiteness of both actual counts is proved on a conull
    set before subtracting; no infinite subtraction occurs. *)
Theorem scalar_signed_target_sign_split (R:realType) (f g:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) -> a<b ->
  measure_almost_equal (@lebesgue_scalar_measure R)
    (partial_extended_function_subtract
      (scalar_curve_area_target_integrand f (scalar_positive_derivative_set f a b) g)
      (scalar_curve_area_target_integrand f (scalar_negative_derivative_set f a b) g))
    (scalar_oriented_interval_integrand g (f a) (f b)).
Proof.
move=>hAC hab; have hm:=lebesgue_scalar_is_measure R.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ (scalar_signed_multiplicity_almost hAC hab))=>y [p [q [hP [hN he]]]].
have hU:partial_function_graph
    (scalar_curve_area_target_integrand f (scalar_positive_derivative_set f a b) g) y (g y * p)%:E.
  change (((g y)%:E  *  @mapping_multiplicity R [the choiceType of real_line_metric R] R f
    (scalar_positive_derivative_set f a b) y)%E=(g y * p)%:E).
  by rewrite hP -EFinM.
have hV:partial_function_graph
    (scalar_curve_area_target_integrand f (scalar_negative_derivative_set f a b) g) y (g y * q)%:E.
  change (((g y)%:E  *  @mapping_multiplicity R [the choiceType of real_line_metric R] R f
    (scalar_negative_derivative_set f a b) y)%E=(g y * q)%:E).
  by rewrite hN -EFinM.
have hDiff:=@partial_subtract_finite_graph R [the choiceType of real_line_metric R] _ _ y (g y * p) (g y * q) hU hV.
have hVal:g y * p-g y * q=g y * oriented_level_indicator (f a) (f b) y.
  by rewrite -mulrBr he.
rewrite hVal in hDiff.
exists (g y * oriented_level_indicator (f a) (f b) y)%:E; by split.
Qed.
