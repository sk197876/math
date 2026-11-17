(** Federer 2.10.27, p. 191: the real radial power integral used
    in the section-profile evaluation. Reuse the internal finite
    fundamental theorem of 3.1.11, pp. 220-221, and actual real-power
    differentiation. No improper integral is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal
  topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground RealNormUP RealPower RealPowerDifferential ScalarDifferentialContinuity ScalarPositiveClassZero Hom NormDifferentialArithmetic NormHigherCurveDerivativeUP
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

(** Source for [positive_real_power_segment_integral]: finite
    radial power integral for Federer 2.10.27, p. 191. The
    positive-domain derivative is continuous;
    no improper-integral theorem or external calculus
    result is assumed. Degenerate positive segments are included. *)
Lemma positive_real_power_segment_integral (R:realType) (p a b:R):
  0<p ->0<a ->a<=b ->is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (real_total_integrand (fun x:R=>real_power x (p-1)))
    (p^-1*real_power b p-p^-1*real_power a p)%:E.
Proof.
move=>hp ha hab.
pose F:=fun x:R=>p^-1*real_power x p.
pose D:=fun x:R=>real_power x (p-1).
pose N:=fun x:R^o=>`|x|.
pose hN:=@scalar_absolute_value_norm R.
pose A:=fun x:R^o=>0<x.
have hAt x (hx:0<x):
    (fun t:real_line_metric R=>(D t:real_line_metric R)) @ (x:real_line_metric R) -->
      (D x:real_line_metric R).
  exact:scalar_differential_continuous_at (real_power_differential (p-1) hx).
have hC:norm_class_zero N N A D.
  exact:scalar_positive_continuity_class_zero hAt.
have hAB x:a<=x<=b ->A x.
  move=>/andP[hax _]; exact:lt_le_trans ha hax.
have hD x:A x ->has_norm_differential N N A F x
    (@NormHigherCurveDerivativeUP.scalar_coefficient_linear_map R R^o (D x)).
  move=>hx; apply:(norm_differential_restrict (fun y (_:A y)=>Logic.I) (hC x hx).1).
  have hScale:=@norm_differential_scale R R^o R^o N N hN hN setT
    (fun x:R^o=>real_power x p) x (real_power_linear_term p x) p^-1
    (real_power_differential p hx).
  have hMap:p^-1*:real_power_linear_term p x=
      @NormHigherCurveDerivativeUP.scalar_coefficient_linear_map R R^o (D x).
    apply:hom_ext=>v.
    change (p^-1*((p*real_power x (p-1))*v)=v*real_power x (p-1)).
    by rewrite !mulrA mulVf ?gt_eqF // mul1r mulrC.
  by rewrite hMap in hScale.
have hFTC:=@normed_curve_fundamental_theorem R R^o N hN A F D a b hab hAB hD hC.
pose q (x:R):R:=D (segment_retraction a b x).
have hq:continuous (q:real_line_metric R->real_line_metric R).
  move=>x U hU.
  have /andP[hLower _]:=segment_retraction_bounds x hab.
  have hPos:0<segment_retraction a b x:=lt_le_trans ha hLower.
  have hLocal:=hAt (segment_retraction a b x) hPos.
  exact ((@segment_retraction_continuous R a b x) _ (hLocal U hU)).
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
have hOn: (`[a,b]:set (real_line_metric R)) x ->q x=real_power x (p-1).
  rewrite /= in_itv /= =>hx; symmetry; exact:hEq x hx.
split.
- move=>[[hx hz]|[hx hz]].
  + left; split=>//; by rewrite -(hOn hx).
  + right; by split.
- move=>[[hx hz]|[hx hz]].
  + left; split=>//; by rewrite (hOn hx).
  + right; by split.
Qed.
