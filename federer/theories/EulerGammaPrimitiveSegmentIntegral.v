(** Federer (1969), 3.2.13, p. 250: the
    integration-by-parts identity on every positive
    finite segment. The internal normed fundamental
    theorem and the proved scalar Lebesgue/Riemann
    identification supply the actual subset integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground RealNormUP EulerGammaPrimitiveDifferential EulerGammaPrimitiveContinuity
  NormDifferentialUP NormDifferentialLocal NormClassOneUP NormedCurveFundamentalTheorem
  NormedStieltjesUP NormedStieltjesLocal NormedStieltjesUnique NormedStieltjesLaws
  StieltjesSubstitution SegmentRetractionTopology StieltjesIntegral StieltjesMonotone CurveVariationUP CurveArcLength
  LebesgueContinuousDegenerateIntegral LebesgueScalarMeasure MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  PartialFunctionUP PartialZeroExtension SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euler_gamma_primitive_segment_integral]: finite
    endpoint identity for the Gamma recurrence,
    Federer 3.2.13, p. 250. The
    derivative's positive-domain continuity is proved;
    no improper-integral theorem or external calculus
    result is assumed. Degenerate positive segments are included. *)
Lemma euler_gamma_primitive_segment_integral (R:realType) (s a b:R):
  0<a ->a<=b ->is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (real_total_integrand (euler_gamma_primitive_derivative s))
    (euler_gamma_primitive s b-euler_gamma_primitive s a)%:E.
Proof.
move=>ha hab.
pose F:=euler_gamma_primitive s.
pose D:=euler_gamma_primitive_derivative s.
pose N:=fun x:R^o=>`|x|.
pose hN:=@scalar_absolute_value_norm R.
pose A:=fun x:R^o=>0<x.
have hC:=@euler_gamma_primitive_derivative_class_zero R s.
have hAB x:a<=x<=b ->A x.
  move=>/andP[hax _]; exact:lt_le_trans ha hax.
have hD x:A x ->has_norm_differential N N A F x
    (@NormHigherCurveDerivativeUP.scalar_coefficient_linear_map R R^o (D x)).
  move=>hx; apply:(norm_differential_restrict (fun y (_:A y)=>Logic.I) (hC x hx).1).
  exact:euler_gamma_primitive_differential hx.
have hFTC:=@normed_curve_fundamental_theorem R R^o N hN A F D a b hab hAB hD hC.
pose q (x:R):R:=D (segment_retraction a b x).
have hq:continuous (q:real_line_metric R->real_line_metric R).
  move=>x U hU.
  have /andP[hLower _]:=segment_retraction_bounds x hab.
  have hPos:0<segment_retraction a b x:=lt_le_trans ha hLower.
  have hAt:=@euler_gamma_primitive_derivative_continuous_at R s (segment_retraction a b x) hPos.
  exact ((@segment_retraction_continuous R a b x) _ (hAt U hU)).
have hEq x:a<=x<=b ->D x=q x.
  by move=>hx; rewrite /q segment_retraction_id.
have hFTCq:=normed_stieltjes_integral_segment_agreement hEq hFTC.
have hId:curve_locally_finite_variation ((fun x:R=>x):R->real_line_metric R).
  apply:monotone_locally_finite_variation; by move=>x y hxy.
have hRS:=normed_stieltjes_scalar_agreement hId hq hab.
have hValue:=normed_stieltjes_integral_unique hN hFTCq hRS.
have hLeb:=lebesgue_continuous_segment_integral_including_diagonal hq hab.
rewrite -hValue in hLeb.
apply:measure_integral_graph_equivalent _ hLeb=>x z.
rewrite !partial_function_zero_extension_graph !real_total_integrand_graph.
have hOn: (`[a,b]:set (real_line_metric R)) x ->q x=euler_gamma_primitive_derivative s x.
  rewrite /= in_itv /= =>hx; symmetry; exact:hEq x hx.
split.
- move=>[[hx hz]|[hx hz]].
  + left; split=>//; by rewrite -(hOn hx).
  + right; by split.
- move=>[[hx hz]|[hx hz]].
  + left; split=>//; by rewrite (hOn hx).
  + right; by split.
Qed.
