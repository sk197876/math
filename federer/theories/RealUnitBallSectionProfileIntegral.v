(** Federer 2.10.27, p. 191: the unit-radius, centred
    real-degree ball profile. The Gaussian, polar and scalar-section
    integrals are all proved before this assembly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanCoordinateSplit EuclideanLebesgueDimensions LebesgueScalarMeasure InnerNormedTopology
  RealPower RealHausdorffBallCoefficient RealEuclideanBallSectionProfileUP
  UnitBallCoordinatePowerSummability UnitBallCoordinatePowerModel UnitBallCoordinatePowerIntegral
  UnitBallCoordinateVerticalIntegral EuclideanHeadFunctionFubini RealBallSectionGammaCoefficient
  EulerGamma EulerGammaHalfParameters SphereCoordinateParameters SphereCoordinateMoment
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  ParameterizedIntegral PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  PartialProductSections SummableRealFunctionUP SummableRealArithmetic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [real_unit_ball_section_profile_integral]: supporting
    exact first-display integral in Federer 2.10.27, p. 191,
    at centre zero and radius one, for every positive real
    section degree and every natural base dimension. Its pointwise
    profile specification has no measurability or integral premise. *)
Theorem real_unit_ball_section_profile_integral (R:realType) m (k:R) (hk:0<=k)
    (q:inner_metric_space (@euclidean_inner_productP R m)->\bar R):
  0<k ->is_real_euclidean_ball_section_profile hk 0 1 q ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(q y:extended_real_line R)))
    (real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m)))%:E.
Proof.
move=> hkPos hq.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose N:=inner_norm (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose g:=@unit_ball_coordinate_power_model R m.+1 ord0 (k-1).
have hg:=@unit_ball_coordinate_power_model_laws R m.+1 ord0 (k-1).
have hExp:-1<k-1 by lra.
pose b:=((2*euler_gamma (positive_coordinate_moment_parameter hExp)*
  (euler_gamma_half R)^+(m.+1-1)/
  euler_gamma (@positive_coordinate_moment_denominator R m.+1 (k-1) (ltn0Sn m) hExp))*
  ((k-1)+m.+1%:R)^-1).
have hBall:is_measure_integral (@euclidean_lebesgue_measure R m.+1)
    (real_total_integrand g) b%:E.
  exact:unit_ball_coordinate_power_integral hg.
have hFubini:=euclidean_head_function_fubini hBall.
pose p (y:X):R:=if N y<= 1 then real_power (Num.sqrt (1-(N y)^+2)) k else 0.
have hVertical y:is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun t=>g (euclidean_join (y,t)))) ((2/k)* p y)%:E.
  have h:=@unit_ball_coordinate_vertical_integral R m k g y hkPos hg.
  rewrite /p;case hNy:(N y<= 1).
  - by rewrite hNy in h.
  - rewrite mulr0;by rewrite hNy in h.
have hGraph y z:partial_function_graph
    (parameterized_integral (@lebesgue_scalar_measure R)
      (partial_product_vertical_section (partial_function_precompose (@euclidean_join R m)
        (real_total_integrand g)))) y z <->
    partial_function_graph (real_total_integrand (fun y=>(2/k)* p y)) y z.
  rewrite parameterized_integral_specification real_total_integrand_graph.
  split.
  - move=> hi;have hKnown:=hVertical y.
    have hSame:is_measure_integral (@lebesgue_scalar_measure R)
        (partial_product_vertical_section (partial_function_precompose (@euclidean_join R m)
          (real_total_integrand g)) y) ((2/k)* p y)%:E.
      exact:(measure_integral_graph_equivalent (fun t v=>iff_refl _) hKnown).
    exact:esym (measure_integral_unique hi hSame).
  - move=> <-;exact:(measure_integral_graph_equivalent (fun t v=>iff_refl _) (hVertical y)).
have hScaled:=measure_integral_graph_equivalent hGraph hFubini.
have hKernel:=@real_total_integral_scale R X mu hm (fun y=>(2/k)* p y) b (k/2) hScaled.
have hkNe:k!=0:=lt0r_neq0 hkPos.
have hCancel:(fun y:X=>(k/2)*((2/k)* p y))=p.
  apply:funext=> y;field;by rewrite hkNe.
rewrite hCancel in hKernel.
have hProfile:=@real_total_integral_scale R X mu hm p ((k/2)*b)
  (real_hausdorff_ball_coefficient hk) hKernel.
have hValue:real_hausdorff_ball_coefficient hk*((k/2)*b)=
    real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m)).
  rewrite mulrA;exact:(@real_ball_section_gamma_coefficient R m k hkPos hk hExp).
rewrite hValue in hProfile.
apply:(measure_integral_graph_equivalent _ hProfile)=> y z.
have hDist:mdist (0:X) y=N y by rewrite inner_metric_normE subr0.
have hEq:(real_hausdorff_ball_coefficient hk* p y)%:E=q y.
  rewrite /p;case:(leP (N y) 1)=> hy.
  - have hIn:mdist (0:X) y<= 1 by rewrite hDist.
    by rewrite (real_ball_section_profile_inside hq hIn) hDist expr1n.
  - have hOut:1<mdist (0:X) y by rewrite hDist.
    by rewrite (real_ball_section_profile_outside hq hOut) mulr0.
by rewrite real_total_integrand_graph hEq.
Qed.
