(** Federer (1969), 3.2.7, p. 246:
    the prescribed reciprocal square-root cutoff weight
    is Lebesgue summable on the whole line. Use the
    finite absolute-derivative integral of the monotone
    signed root; no measurability assumption on the
    weight is added to its defining value laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra ring.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology SignedSquareRootSealed SignedSquareRootLaws
  SignedSquareRootDerivative ReciprocalRootWeightUP CurveArcLength StieltjesMonotone StieltjesImageMeasures
  RealBVDerivativeIntegral RealCurveDerivativeUP RealCurveDerivativeIntegrands PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialZeroExtension SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureUpperIntegralScale MeasureIntegralScaleLaw MeasureIntegralAlmostEquality LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [reciprocal_root_weight_summable]: the
    g in the third example of Federer 3.2.7,
    p. 246, is Lebesgue summable. Twice the
    actual speed of the signed root on [-1,1]
    agrees with g outside the single null point zero. *)
Theorem reciprocal_root_weight_summable (R:realType) (g:R->R):
  is_reciprocal_root_weight g ->
  is_measure_summable (@lebesgue_scalar_measure R) (real_total_integrand g).
Proof.
move=>hg; have hm:=lebesgue_scalar_is_measure R.
pose G:=@SignedSquareRoot.value R.
have hBV:curve_locally_finite_variation (G:R->real_line_metric R).
  exact (@monotone_locally_finite_variation R G (@signed_root_monotone R)).
have [psip [psim hp]]:=@induced_measure_pair_exists R G hBV.
have hOrder:(-1:R)<= 1 by lra.
have [I [hI0 [hI hIV]]]:=@real_bv_absolute_derivative_interval_integral R G psip psim (-1) 1 hBV hp hOrder.
pose A:=(`[(-1)%R,1%R]:set (real_line_metric R)).
pose H:=partial_function_zero_extension (0:extended_real_line R) A (real_curve_absolute_derivative_integrand G).
have hH:is_measure_integral (@lebesgue_scalar_measure R) H I%:E:=hI.
have hScaled:=@measure_integral_positive_scale R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm 2 H I%:E (ltr0n R 2) hH.
rewrite -EFinM in hScaled.
exists (2*I).
apply:(measure_integral_almost_equal hm hScaled).
have hOff:measure_almost_everywhere (@lebesgue_scalar_measure R) (~` [set (0:R)]).
  by rewrite /measure_almost_everywhere setCK lebesgue_scalar_singleton.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ hOff)=>x hx0.
have hx:x!= 0 by apply/eqP=>he; exact (hx0 he).
exists (g x)%:E; split; last by apply/real_total_integrand_graph.
case:(pselect (A x))=>hxA.
- have hxA':=hxA; move:hxA'; rewrite /A /= in_itv /= =>/andP[hxl hxu].
  have hxPos:0<`|x| by rewrite normr_gt0.
  have hxOne:`|x|<= 1 by rewrite ler_norml; apply/andP; split.
  pose s:=Num.sqrt `|x|; pose v:=(2*s)^-1.
  have hs:0<s by rewrite /s sqrtr_gt0.
  have hv:0<v by rewrite /v invr_gt0 mulr_gt0 // ltr0n.
  have hD:has_real_curve_derivative G x v:=signed_root_actual_derivative hx.
  have hValue:2*v=s^-1.
    have hs0:s!= 0 by rewrite gt_eqF.
    have hTwo:(2:R)!= 0 by rewrite pnatr_eq0.
    rewrite /v; by field; rewrite ?(negbTE hs0) ?(negbTE hTwo).
  exists v%:E; split.
  + apply/partial_function_zero_extension_graph; left; split; first exact hxA.
    exists v; split; first exact hD; by rewrite (ger0_norm (ltW hv)).
  + rewrite (reciprocal_root_weight_on hg hxPos hxOne) -EFinM hValue; exact:erefl.
- have hNot:~(0<`|x| /\ `|x|<= 1).
    move=>[_ hxOne]; apply:hxA; move:hxOne; rewrite ler_norml=>/andP[hxl hxu].
    by rewrite /A /= in_itv /= hxl hxu.
  rewrite (reciprocal_root_weight_off hg hNot).
  exists 0%E; split; last exact:mule0.
  apply/partial_function_zero_extension_graph; right; by split.
Qed.
