(** Federer (1969), 3.2.13, p. 250: the
    unit sphere has H^(m-1) measure
    m alpha(m). The finite unit-ball
    test proves finiteness and normalization together;
    neither is assumed in applying polar integration. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerNormedTopology
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanBallVolume HausdorffMeasure
  MetricClosedBalls TopologicalBorel CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureCharacteristicIntegral MeasureIntegralUP MeasureIntegralUniqueness
  PolarUnitSphereFormula BallCharacteristicPolarMass SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_unit_sphere_mass]: the formula
    H^(m-1){x:|x|= 1}=m alpha(m)
    deduced from the unit-ball characteristic function,
    Federer 3.2.13, p. 250. All
    positive natural dimensions, including the two-point
    sphere in dimension one, are covered. *)
Theorem hausdorff_unit_sphere_mass (R:realType) m:
  (0<m)%N ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1)
    [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R]=
    (m%:R*euclidean_unit_ball_volume R m)%R%:E.
Proof.
move=>hm.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hmu:=euclidean_lebesgue_is_measure R m.
pose B:set X:=[set x|(inner_norm (@euclidean_inner_productP R m) x<1)%R].
pose g:=@CharacteristicFunction.value R X B.
have hG:=@CharacteristicFunction.laws R X B.
have hB:measure_measurable mu B.
  apply:euclidean_borel_measurable; apply:open_borel_set.
  have hEq:B=[set x:X|(mdist (0%R:X) x<1)%R].
    apply/seteqP; split=>x /=;
      by rewrite inner_metric_distanceE sub0r inner_normN.
  rewrite hEq; exact:metric_open_ball_open.
have hBall:B=[set x:X|(`|x|<1)%R].
  apply/seteqP; split=>x /=; by rewrite inner_norm_topologyE.
have hVol:mu B=(euclidean_unit_ball_volume R m)%:E.
  rewrite hBall; exact:(euclidean_unit_ball_volumeE R m).1.
have hGI:=@measure_characteristic_integral R X mu hmu B g hG hB.
rewrite hVol in hGI.
have [a [hSource hOuter]]:=polar_unit_sphere_integral_formula hm
  (ex_intro _ (euclidean_unit_ball_volume R m)%:E hGI).
have hAlpha:=measure_integral_unique hSource hGI.
have hMass:=@unit_ball_polar_mass_integral R m g hG.
have hNat:(m-1).+1=m by rewrite subn1 prednK.
rewrite hNat in hMass.
have hOuterValue:=measure_integral_unique hOuter hMass.
have hM:(0<(m%:R:R))%R by rewrite ltr0n.
have hMNe:(m%:R!= 0)%R:=lt0r_neq0 hM.
pose C:=@hausdorff_measure R X (m-1)
  [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R].
have hValue:(euclidean_unit_ball_volume R m)%:E=C*(m%:R^-1)%R%:E.
  by rewrite -hAlpha.
have hScaled:=congr1 (fun z=>m%:R%:E*z) hValue.
have hCancel:m%:R%:E*(C*(m%:R^-1)%R%:E)=C.
  by rewrite [C*(_^-1)%R%:E]muleC muleA -EFinM mulfV // mul1e.
rewrite hCancel -EFinM in hScaled.
exact:Logic.eq_sym hScaled.
Qed.
