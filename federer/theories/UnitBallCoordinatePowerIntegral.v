(** Federer 2.10.27, p. 191: evaluation of the real-coordinate
    unit-ball integral used by the section profile. The existing
    polar formula, actual sphere-coordinate moment and proved radial
    power integral supply both finite definedness and its exact value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLebesgueDimensions LebesgueScalarMeasure HausdorffMeasure
  UnitBallCoordinatePowerSummability UnitBallCoordinateSphereValue
  RealPowerRadialIntegral RealPower PolarUnitSphereFormula PolarUnitSphereIntegral
  SphereCoordinateParameters SphereCoordinateMoment EulerGamma EulerGammaHalfParameters
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence SummableRealFunctionUP SummableRealArithmetic
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [unit_ball_coordinate_power_from_sphere]: supporting
    unit-ball evaluation for Federer 2.10.27, p. 191, from an
    independently proved finite angular value. The actual radial
    integral is proved at zero, and the full ball integrability
    follows from the Gaussian domination theorem, not a premise. *)
Theorem unit_ball_coordinate_power_from_sphere (R:realType) n (i:'I_n) (q:R)
    (g:inner_metric_space (@euclidean_inner_productP R n)->R) (b:R):
  (0<n)%N ->-1<q ->is_unit_ball_coordinate_power i q g ->
  is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1))
    [set u|inner_norm (@euclidean_inner_productP R n) u = 1]
    (real_total_integrand (fun u:inner_metric_space (@euclidean_inner_productP R n)=>real_power `|u i| q)) b%:E ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (real_total_integrand g)
    (b*(q+n%:R)^-1)%:E.
Proof.
move=> hn hq hg hAngular.
pose p:=q+n%:R.
have hN:(1<=(n%:R:R)) by rewrite ler1n.
have hp:0<p by rewrite /p;lra.
have [c hSum]:=@unit_ball_coordinate_power_summable R n i q g hq hg.
have [a [hSource hPolar]]:=@polar_unit_sphere_integral_formula R n g hn
  (ex_intro _ c%:E hSum).
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
pose f:=fun t:R=>b* positive_radius_power p 1 t.
have hPower:=@positive_radius_power_integral R p 1 hp ltr01.
rewrite real_power_one_base mulr1 in hPower.
have hRadial:=@real_total_integral_scale R R mu hm (positive_radius_power p 1) p^-1 b hPower.
have hGraph t z:partial_function_graph (real_total_integrand f) t z <->
    partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      [set r:R|0<r] (weighted_unit_sphere_integral (real_total_integrand g))) t z.
  rewrite real_total_integrand_graph.
  case:(pselect ((0<t)%R))=> ht.
  - rewrite (@partial_function_zero_extension_on R (extended_real_line R) (0:extended_real_line R)
      [set r:R|0<r] (weighted_unit_sphere_integral (real_total_integrand g)) t z ht).
    have hValue:=@unit_ball_coordinate_weighted_sphere_value R n i q g b t hn ht hg hAngular.
    split.
    + move=> hz;rewrite -hz;exact hValue.
    + move=> hz;exact:(@partial_function_single_valued R (extended_real_line R)
        (weighted_unit_sphere_integral (real_total_integrand g)) t (f t)%:E z hValue hz).
  - rewrite (@partial_function_zero_extension_off R (extended_real_line R) (0:extended_real_line R)
      [set r:R|0<r] (weighted_unit_sphere_integral (real_total_integrand g)) t z ht).
    have hNot:~~(0<t<=1) by apply/negP=>/andP [h _];exact:ht h.
    by rewrite /f /positive_radius_power (negbTE hNot) mulr0.
have hKnown:is_measure_subset_integral mu [set r:R|0<r]
    (weighted_unit_sphere_integral (real_total_integrand g)) (b* p^-1)%:E.
  exact:(measure_integral_graph_equivalent hGraph hRadial).
have he:=measure_integral_unique hPolar hKnown.
by rewrite he in hSource.
Qed.

(** Source for [unit_ball_coordinate_power_integral]: actual Gamma
    value for the auxiliary unit-ball coordinate integral underlying
    Federer 2.10.27, p. 191. The angular factor is the original
    proved coordinate moment of 3.2.13, p. 251; every real q>-1
    and every positive natural ambient dimension are retained. *)
Corollary unit_ball_coordinate_power_integral (R:realType) n (hn:(0<n)%N)
    (i:'I_n) (q:R) (hq:-1<q)
    (g:inner_metric_space (@euclidean_inner_productP R n)->R):
  is_unit_ball_coordinate_power i q g ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (real_total_integrand g)
    ((2*euler_gamma (positive_coordinate_moment_parameter hq)*(euler_gamma_half R)^+(n-1)/
      euler_gamma (@positive_coordinate_moment_denominator R n q hn hq))*(q+n%:R)^-1)%:E.
Proof.
move=> hg;exact:(@unit_ball_coordinate_power_from_sphere R n i q g _ hn hq hg
  (@hausdorff_unit_sphere_coordinate_moment R n hn i q hq)).
Qed.
